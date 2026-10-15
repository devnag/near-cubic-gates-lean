import Proof.CaseAnalysis.RecoveryGrammarDriverRefresh

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open RecoveryBoundedGrammarDriverBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem total_budget (B bound count : ℕ) (hc : count<bound) :
    compiledBudget B bound count+initialBudget bound count+RecoveryBoundedGrammarDriverBank.refreshBudget B (count+1) ≤
      8192*(bound+2)*(B+2) := by
  have hcount : count+1≤bound:=by omega
  have hrest : bound-(count+1)≤bound:=Nat.sub_le _ _
  have h1:=Nat.mul_le_mul_right (B+2) hcount
  have h2:=Nat.mul_le_mul_right (B+2) hrest
  unfold compiledBudget forwardBudget nodeScanBudget outputScanBudget outputStageBudget
    paddingScanBudget finishScanBudget rowBodyBudget nodeBudget paddingBudget
    afterRowBudget RecoveryBoundedGrammarAdvance.budget atomBudget initialBudget RecoveryBoundedGrammarDriverBank.refreshBudget
  nlinarith

theorem total_budget_W (B bound count W : ℕ) (hc : count<bound) (hb : bound+1≤W) :
    compiledBudget B bound count+initialBudget bound count+RecoveryBoundedGrammarDriverBank.refreshBudget B (count+1) ≤
      16384*(W+1)*(B+2) := by
  apply (total_budget B bound count hc).trans
  calc
    8192*(bound+2)*(B+2) ≤ 8192*(2*(W+1))*(B+2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = 16384*(W+1)*(B+2) := by ring

theorem driver_fits {W C D L S B P bound count : ℕ}
    (room : Room W C D L S B P) (hb : bound+1≤W) (hc : count<bound) :
    bound+3≤B ∧ count+4≤B := by
  have hr:=room.reference
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
