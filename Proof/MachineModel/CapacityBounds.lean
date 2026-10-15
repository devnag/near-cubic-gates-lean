import Proof.MachineModel.FinalState
import Proof.PCP.ProjectionDimensionPolynomialBounds

/-! Coarse capacity estimates for the actual source round and cache header.
These estimates are chosen before any capacity-dependent sweep. -/
namespace NearCubicWires.ExtDecompositionBatch.CapacityBounds
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bit_length (n:ℕ):natBitLength n≤n+1:=by
  unfold natBitLength
  have h:=Nat.log_le_self 2 n
  omega

theorem round_bound (a:DecompositionAlgorithm) {q:ℕ} (g:SupportedNormalizedGate q) (U:ℕ)
    (hq:q≤U) (hw:(frame (nativeWord g)).length≤U) (hs:sourceBudget a (request g)≤U) :
    bodyCost a q g≤1024*(U+1)^2 := by
  have hk:(children a g).length≤U:=(children_le_budget a g).trans hs
  have hb:((children a g).flatMap exactWord).length≤U:=(body_le_budget a g).trans hs
  have word:(natWord q++Call.tail (request g)).length≤U:=by
    have hn:(natWord q++Call.tail (request g))=nativeWord g:=(nativeWord_input g).symm
    rw [hn]
    exact (word_le_frame _).trans hw
  have nq:=Count.budget_bound q
  have nk:=Count.budget_bound (children a g).length
  have qsq:(q+1)^2≤(U+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have ksq:((children a g).length+1)^2≤(U+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have cq:Count.budget q≤128*(U+1)^2:=nq.trans (Nat.mul_le_mul_left _ qsq)
  have ck:Count.budget (children a g).length≤128*(U+1)^2:=nk.trans (Nat.mul_le_mul_left _ ksq)
  have bq:=bit_length q
  have bk:=bit_length (children a g).length
  have prod:q*(children a g).length≤U*U:=Nat.mul_le_mul hq hk
  change (2*(frame (nativeWord g)).length+2)+1+
      (Prepare.budget q (Call.tail (request g))+2*sourceBudget a (request g)+3+
        Count.budget (children a g).length+1)+1+
      (2*natBitLength (children a g).length+3)+1+
      (((children a g).flatMap exactWord).length+(6*q+10)*(children a g).length+3)+1+
      (2*(children a g).length+2)≤_
  unfold Prepare.budget PCPPQueryField.fieldCost
  nlinarith

theorem cache_fits {q:ℕ} (gs:List (ExactThresholdGate q)) (U:ℕ)
    (hg:gs.length≤U) (hb:(gs.flatMap exactWord).length≤U) :
    gs.length+2≤4096*(U+1)^2 ∧
      PCPPNativeNaturalAppend.budget gs.length≤4096*(U+1)^2 ∧
      (gs.flatMap exactWord).length≤4096*(U+1)^2 ∧
      (exactListWord gs).length≤4096*(U+1)^2 := by
  have sq:(gs.length+1)^2≤(U+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have header:PCPPNativeNaturalAppend.budget gs.length≤256*(U+1)^2:=
    (PCPPNativeNaturalAppend.budget_bound _).trans (Nat.mul_le_mul_left _ sq)
  have bits:=bit_length gs.length
  have cache:(exactListWord gs).length≤3*U+3:=by
    simp only [exactListWord,List.length_append,natWord_length]
    omega
  refine ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end NearCubicWires.ExtDecompositionBatch.CapacityBounds
