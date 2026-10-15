import Proof.Amplification.RecoveryRawViewEntryMeaning

/-! The raw-SAT replay reuses the existing 42-tape clause evaluator and
one retained outer-code bank. Every clause reads the same valuation word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  clause : RecoveryClauseState.State
  valuation : RecoveryClauseEvaluation.Extra
  outer : RecoveryClauseState.State

def State.width (x : State) := x.clause.bits.length
def State.tapes (x : State) : Fin 70→List Bool :=
  Fin.addCases (m:=42) (n:=28) (motive:=fun _=>List Bool)
    (RecoveryClauseEvaluation.tapes x.clause x.valuation) x.outer.tapes
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 70 s := ⟨q,fun _=>0,x.tapes⟩
def State.Valid (x : State) (word : List Bool) : Prop :=
  x.clause.Valid ∧ x.valuation.Valid x.clause word ∧ x.outer.Valid ∧ x.outer.bits.length=x.width

def cleared (x : State) : State :=
  let clause := RecoveryClauseEvaluation.boundaryState 0 x.clause x.valuation
  let valuation := RecoveryClauseEvaluation.boundaryExtra 0 x.valuation
  {x with clause:=clause,valuation:=valuation}
def outerStep (x : State) : State := {x with outer:=x.outer.after 0}
def headWord (x : State) := RecoveryCellStore.headWord x.outer.bits
def copied (x : State) (bits : List Bool) : State :=
  let clause := {x.clause with bits:=bits,capacity:=max x.clause.capacity (4*bits.length+3)}
  let outer := {x.outer with capacity:=max x.outer.capacity (2*bits.length+1)}
  {x with clause:=clause,outer:=outer}

noncomputable def clearMachine := TapeEmbedding.machine 28 (RecoveryClauseEvaluation.boundaryMachine 0)
noncomputable def outerMachine := RecoveryBankPair.rightMachine (t:=42) (RecoveryClauseState.machine 0)
def copySlots : Fin 4→Fin 70 := ![66,0,64,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def clauseMachine := TapeEmbedding.machine 28 RecoveryClauseEvaluation.machine

theorem cleared_valid (x : State) (word : List Bool) (hx : x.Valid word) : (cleared x).Valid word := by
  have h := RecoveryClauseEvaluation.boundary_valid 0 x.clause x.valuation word hx.1 hx.2.1
  exact ⟨h.1,h.2,hx.2.2⟩

theorem outer_step_valid (x : State) (word : List Bool) (hx : x.Valid word) : (outerStep x).Valid word :=
  ⟨hx.1,hx.2.1,RecoveryClauseState.after_valid x.outer 0 hx.2.2.1,
    (RecoveryClauseState.after_length x.outer 0).trans hx.2.2.2⟩

theorem copied_width (x : State) (bits : List Bool) (hw : bits.length=x.width) : (copied x bits).width=x.width := hw

theorem copied_capacity (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity x.clause.bits := by
  change 8192*(bits.length+1)^2=8192*(x.width+1)^2
  rw [hw]

theorem copied_valid (x : State) (word bits : List Bool) (hx : x.Valid word) (hw : bits.length=x.width) :
    (copied x bits).Valid word := by
  have hc := copied_capacity x bits hw
  have hs : (copied x bits).clause.Valid := by
    constructor
    · intro i
      change (x.clause.backing i).length ≤ RecoveryReusableUnpair.capacity bits
      rw [hc]
      exact hx.1.1 i
    · intro i
      change (x.clause.fields i).length ≤ 2*bits.length+1
      rw [hw]
      exact hx.1.2 i
  have he := hx.2.1
  refine ⟨hs,?_,hx.2.2.1,hx.2.2.2.trans hw.symm⟩
  refine ⟨he.source,?_,?_,he.count.trans hw.symm,he.committed.trans_eq hw.symm,?_,?_,?_⟩
  · change x.valuation.row.length ≤ 2*(bits.length+1)+1
    rw [hw]
    exact he.row
  · change x.valuation.counter.length ≤ RecoveryReusableUnpair.capacity bits
    rw [hc]
    exact he.counter
  · change x.valuation.cap ≤ 3*(bits.length+1)
    rw [hw]
    exact he.cap
  · change x.valuation.cap*(bits.length+2)+1 ≤ x.valuation.prefixLimit
    rw [hw]
    exact he.prefixBound
  · change RecoveryReusableUnpair.capacity bits+1 ≤ max x.clause.capacity (4*bits.length+3)
    rw [hc]
    exact he.reset.trans (Nat.le_max_left _ _)

theorem clear_ready (x : State) : ReadyRun clearMachine 1 x.tapes (cleared x).tapes :=
  (RecoveryClauseEvaluation.boundary_ready_state 0 x.clause x.valuation).embed x.outer.tapes

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
