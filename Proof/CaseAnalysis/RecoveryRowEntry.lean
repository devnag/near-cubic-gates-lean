import Proof.CaseAnalysis.RecoveryRowMeaning

/-! The retained clause driver is the actual finite-loop sentinel. This
boundary makes its entry equality explicit without another copy or scan. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRow
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodySlots (j : Fin 72) : Fin 73:=j.castAdd 1
theorem clause_entry (H : Fin 73→ℕ) (A : Fin 73→List Bool) (count : ℕ)
    (hH : H 72=1) (hA : A 72=CompareMachine.word count) :
    RecoveryBoundedClauses.entry (H∘bodySlots) (A∘bodySlots) count=
      (⟨RecoveryBoundedClauses.machine.start,H,A⟩ : Configuration 73 _) := by
  apply configuration_ext
  · rfl
  · funext i
    change Fin.addCases (m:=72) (n:=1) (motive:=fun _=>ℕ) (H∘bodySlots) (fun _=>1) i=H i
    refine Fin.addCases (m:=72) (n:=1) ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
      rfl
    · intro j
      fin_cases j
      exact hH.symm
  · funext i
    change Fin.addCases (m:=72) (n:=1) (motive:=fun _=>List Bool) (A∘bodySlots)
      (fun _=>CompareMachine.word count) i=A i
    refine Fin.addCases (m:=72) (n:=1) ?_ ?_ i
    · intro j
      simp only [Fin.addCases_left]
      rfl
    · intro j
      fin_cases j
      exact hA.symm

theorem body_clause (H : Fin 73→ℕ) : (H∘bodySlots)∘RecoveryBoundedClauseCollect.old=H∘clauseSlots := rfl
theorem body_clause_data (A : Fin 73→List Bool) :
    (A∘bodySlots)∘RecoveryBoundedClauseCollect.old=A∘clauseSlots := rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRow
