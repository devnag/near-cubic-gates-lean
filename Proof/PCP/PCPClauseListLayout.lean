import Proof.PCP.PCPClauseList

/-! The whole clause-list program has only two nonblank physical inputs:
the native triple stream and its retained M driver. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseList
open LocalBitMultitape
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputHeads (i : Fin 309) : ℕ := if i=0 then 1 else 0
def inputTapes (M : ℕ) (source : List Bool) (i : Fin 309) : List Bool :=
  if i=0 then RepairSource.VerifierDecoding.CompareMachine.word M else if i=5 then source else []

theorem entry_heads (M : ℕ) (source : List Bool) : (entry M source).heads=inputHeads := by
  funext i
  fin_cases i <;> rfl
theorem entry_tapes (M : ℕ) (source : List Bool) : (entry M source).tapes=inputTapes M source := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.PCPClauseList
