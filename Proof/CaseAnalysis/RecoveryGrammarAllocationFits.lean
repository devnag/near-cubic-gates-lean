import Proof.CaseAnalysis.RecoveryGrammarAllocation
import Proof.CaseAnalysis.RecoveryGrammarResources
import Proof.CaseAnalysis.RecoveryWorkspacePolynomial

/-! The SAME original graph workspace discharges every grammar allocation
premise. Its concrete Room backing remains source polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarResources
open RecoveryBoundedGrammarCold CloseoutRecoveryWorkspace
open OuterPCPRecovery PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem allocation (q bound G : ℕ) : Allocation q bound G (workspace q bound G) := by
  have hb:=workspace_bounds q bound G
  have hF : boundedCircuitFieldLimit q bound=q+bound+1 := rfl
  refine ⟨graph_le_workspace (Nat.le_refl G),by omega,?_,?_,?_⟩
  · have h:=hb.2.2.1
    rw [hF]
    omega
  · have h:=hb.2.2.1
    rw [hF]
    have hm:=Nat.mul_le_mul_left (q+bound+1)
      (show 3*(q+bound+1)+1≤3*(q+bound+1)+2 by omega)
    omega
  · intro row start hs
    exact index_le_workspace row start hs

theorem backing_polynomial {width support : ℕ→ℕ}
    (hw : SourcePoly width) (hs : SourcePoly support) :
    SourcePoly (fun n=>backing (width n) (support n)) :=
  CloseoutRecoveryWorkspacePolynomial.row_workspace hs hw

end NearCubicWires.RepairOrdinary.CloseoutRecoveryGrammarResources
