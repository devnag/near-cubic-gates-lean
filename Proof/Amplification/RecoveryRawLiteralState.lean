import Proof.Amplification.RecoveryRawShape

/-! The raw inspector decodes the next actual clause-list cell and keeps
a separate nonempty-cell flag. Invalid natural Boolean tags are data for
the exact default-empty branch, not a malformed certificate rejection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteral
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  data : RecoveryClauseState.State
  present : Bool

def State.tapes (x : State) : Fin 29 → List Bool :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) x.data.tapes (fun _=>[x.present])
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 29 s := ⟨q,fun _=>0,x.tapes⟩
def stepped (x : State) : State := {x with data:=x.data.after 0}
def marked (x : State) : State := {stepped x with present:=(stepped x).data.flag}
def literal (x : State) := RecoveryCellStore.headWord x.data.bits
def decoded (x : State) : State :=
  {marked x with data:=RecoveryCheckedLiteral.checkedState (stepped x).data 0 (literal x)}
def output (x : State) := if (marked x).present then decoded x else marked x

noncomputable def cellMachine := TapeEmbedding.machine 1 (RecoveryClauseState.machine 0)
def flagMachine := RecoveryBankPair.flagMachine (28 : Fin 29) 23
noncomputable def firstMachine := Composition.machine cellMachine flagMachine
noncomputable def decodeMachine := TapeEmbedding.machine 1 (RecoveryCheckedLiteral.machine 0)
noncomputable def machine := RecoveryGatedSequence.machine firstMachine decodeMachine 28
def firstCost (x : State) := RecoveryStoredListCell.time x.data.bits+1+1
def cost (x : State) := firstCost x+RecoveryCheckedLiteral.time (literal x)+2
def budget (x : State) := 524288*(x.data.bits.length+1)^2

theorem marked_present (x : State) : (marked x).present=decide (RadixSemantics.value x.data.bits≠0) :=
  RecoveryThreeCellReader.after_flag x.data 0

theorem literal_length (x : State) : (literal x).length=(stepped x).data.bits.length := by
  rw [show (stepped x).data.bits.length=x.data.bits.length from RecoveryClauseState.after_length x.data 0]
  exact RecoveryCellStore.headWord_length x.data.bits

theorem literal_field (x : State) (hx : (marked x).present=true) :
    (stepped x).data.fields 0=frame (literal x) := by
  have hn : RadixSemantics.value x.data.bits≠0 := by
    rw [marked_present,decide_eq_true_eq] at hx
    exact hx
  simp only [stepped,RecoveryClauseState.State.after,hn,ite_false,Function.update_self]
  rfl

theorem output_valid (x : State) (hx : x.data.Valid) : (output x).data.Valid := by
  have hs := RecoveryClauseState.after_valid x.data 0 hx
  unfold output
  split
  · exact RecoveryCheckedLiteral.checked_valid (stepped x).data 0 (literal x) hs (literal_length x)
  · exact hs

theorem cost_bound (x : State) : cost x ≤ budget x := by
  have hc := RecoveryStoredListCell.time_bound x.data.bits
  have hd := RecoveryCheckedLiteral.time_bound (literal x)
  have hw : (literal x).length=x.data.bits.length := RecoveryCellStore.headWord_length x.data.bits
  unfold RecoveryStoredListCell.budget at hc
  unfold RecoveryCheckedLiteral.budget at hd
  rw [hw] at hd
  unfold cost firstCost budget
  have hp : 0<(x.data.bits.length+1)^2 := by positivity
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRawLiteral
