import Proof.CaseAnalysis.RecoveryGraphBudgetSupport
import Proof.CaseAnalysis.RecoveryCountCompiled

/-! A loose scalar bound for every actual original count and randomness
iteration, with the same paid W and B. C.12 needs no sharper exponent. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private def foldEnvelope (count C : ℕ) := 101+(count*(24*C+66)+count+3)
private theorem fold_envelope (conjunction : Bool) (count total C : ℕ) (h : count ≤ total) :
    RecoveryBoundedGrammarFold.budget conjunction count C ≤ foldEnvelope total C := by
  have hb : (RecoveryBoundedGrammarFold.bits conjunction).length ≤ 100 := by cases conjunction <;> decide
  have hm := Nat.mul_le_mul_right (24*C+66) h
  unfold RecoveryBoundedGrammarFold.budget foldEnvelope
  omega

private def rowsEnvelope (B W : ℕ) :=
  W*(512*(B+2)+2)+(W+1)+3+1+256*(B+2)+1+foldEnvelope (W+1) (capacity W)
private theorem rows_envelope (B W total : ℕ) (ht : total ≤ W) :
    RecoveryBoundedRows.budget B W total ≤ rowsEnvelope B W := by
  have hm := Nat.mul_le_mul_right (512*(B+2)+2) ht
  have hf := fold_envelope true (total+1) (W+1) (capacity W) (by omega)
  unfold RecoveryBoundedRows.budget RecoveryBoundedRows.scanBudget
    RecoveryBoundedRows.bodyBudget RecoveryBoundedRows.finishBudget rowsEnvelope
  omega

private def bodyEnvelope (B W : ℕ) :=
  32768*(W+1)*(B+2)+(rowsEnvelope B W+1+(24*capacity W+64)+1+64*(B+2)+1+(4*W+6))

theorem compiled_scalar (B W R bound : ℕ) (hR : R ≤ W) (hb : bound ≤ W) (htwo : 2^R ≤ W) :
    RecoveryBoundedCountUniform.compiledBudget B W R bound ≤ 1000000000*(W+1)^4*(B+2) := by
  have hr := rows_envelope B W (2^R-1) (by omega)
  have hbody : RecoveryBoundedCountUniform.bodyBudget B W R ≤ bodyEnvelope B W := by
    unfold RecoveryBoundedCountUniform.bodyBudget RecoveryBoundedFixedRows.reusableBudget
      RecoveryBoundedFixedRows.Reuse.budget RecoveryBoundedFixedRows.budget bodyEnvelope
    omega
  have hcounts := Nat.mul_le_mul hb (Nat.add_le_add_right hbody 2)
  have hfold := fold_envelope false bound W (capacity W) hb
  have hwhole : RecoveryBoundedCountUniform.compiledBudget B W R bound ≤
      W*(bodyEnvelope B W+2)+W+3+1+foldEnvelope W (capacity W) := by
    unfold RecoveryBoundedCountUniform.compiledBudget RecoveryBoundedCountUniform.scanBudget
    omega
  apply hwhole.trans
  unfold bodyEnvelope rowsEnvelope foldEnvelope capacity
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4),
    Nat.zero_le (B*W^2),Nat.zero_le (B*W^3),Nat.zero_le (B*W^4)]

def scalarSupport (W : ℕ) := 10000000000*(W+1)^6
def scalarBacking (W : ℕ) := CloseoutRecoveryGrammarResources.backing W (scalarSupport W)

theorem scalar_backing (W : ℕ) : scalarBacking W+2 ≤ 330000000066*(W+1)^6 := by
  have h : 1 ≤ (W+1)^6 := Nat.one_le_pow _ _ (by omega)
  unfold scalarBacking scalarSupport CloseoutRecoveryGrammarResources.backing
  omega

theorem compiled_paid_scalar (W R bound : ℕ) (hR : R ≤ W) (hb : bound ≤ W) (htwo : 2^R ≤ W) :
    RecoveryBoundedCountUniform.compiledBudget (scalarBacking W) W R bound ≤
      (1000000000*330000000066)*(W+1)^10 := by
  have h := compiled_scalar (scalarBacking W) W R bound hR hb htwo
  have hm := Nat.mul_le_mul_left (1000000000*(W+1)^4) (scalar_backing W)
  apply h.trans (hm.trans (le_of_eq ?_))
  ring

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
