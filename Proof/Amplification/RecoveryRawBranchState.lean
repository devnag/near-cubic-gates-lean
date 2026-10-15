import Proof.Amplification.RecoveryCompactBranchCanonical

/-! The raw syntax frontend and shared-valuation SAT replay share the
same physically produced outer-count tape. The original code and valuation
remain on the independent70-tape SAT bank during syntax replay. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawBranch
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  view : RecoveryRawView.State
  eval : RecoveryRawSAT.State

def cfg {s : Nat} (x : State) (total : Nat) (q : Fin s) : Configuration 136 s :=
  RecoveryBankPair.cfg (RecoveryRawViewEnd.cfg x.view total q).heads
    (RecoveryRawViewEnd.cfg x.view total q).tapes (fun _ : Fin 70=>0) x.eval.tapes q
def evalSlots (i : Fin 71) : Fin 136 := if h:i.val<70 then ⟨66+i.val,by omega⟩ else 65
theorem eval_injective : Function.Injective evalSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold evalSlots at hv
  split at hv <;> split at hv <;> apply Fin.ext <;> dsimp at hv <;> omega
noncomputable def viewMachine := RecoveryBankPair.leftMachine (u:=70) RecoveryRawViewEntry.machine
noncomputable def evalMachine := RecoveryFocus.machine evalSlots RecoveryRawSATTable.machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem eval_config {s : Nat} (x : State) (total : Nat) (q : Fin s) :
    RecoveryFocus.config evalSlots (cfg x total q).heads (cfg x total q).tapes
      (RecoveryRawSATEnd.cfg x.eval.tapes total q)=cfg x total q := by
  apply focus_configuration evalSlots eval_injective
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i _; rfl
  · intro i _; rfl

end NearCubicWires.RepairOrdinary.RecoveryRawBranch
