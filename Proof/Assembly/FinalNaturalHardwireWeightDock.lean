import Proof.Assembly.FinalNaturalHardwireWeights
import Proof.Assembly.FinalPoolJoin

/-! The consumed arbitrary-live residual weight worker and its exact paid Step. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireWeightDock
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation SupplierPipeline SupplierEstimator
open CloseoutRowsGateSupport CloseoutRowsTouching CloseoutFinalPool
open C10NaturalHardwireWeights
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem weight_step {q : ℕ} (g : ExactThresholdGate q) (live : Finset (Fin q))
    (y : BitInput live.card) (pre tail backing out : List Bool) :
    Step C10NaturalHardwireWeights.loop (C10NaturalHardwireWeights.loopBudget (gateItems g live))
      (wH pre.length 0 out) (wT (pre++exactWord g++tail) backing out (gateMembers live) q)
      (wH (pre.length+(weightWord g).length) q
        (out++weightWord (C10SupplierRowInput.hardwire live g y)))
      (wT (pre++exactWord g++tail) (CloseoutRowsPoolWeight.saved (gateItems g live) backing)
        (out++weightWord (C10SupplierRowInput.hardwire live g y)) (gateMembers live) q) := by
  obtain ⟨r,hr,hf,_⟩ := hardwire_weights_run g live y pre tail backing out [] []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hr hf
  exact step_of_repeat C10NaturalHardwireWeights.body (fun _ _=>true)
    (C10NaturalHardwireWeights.loopBudget (gateItems g live))
    ⟨C10NaturalHardwireWeights.body.start,CloseoutRowsPoolWeight.heads pre.length 0 out,
      CloseoutRowsPoolWeight.data (pre++exactWord g++tail) backing out (gateMembers live)⟩
    ⟨C10NaturalHardwireWeights.body.start,
      CloseoutRowsPoolWeight.heads (pre.length+(weightWord g).length) q
        (out++weightWord (C10SupplierRowInput.hardwire live g y)),
      CloseoutRowsPoolWeight.data (pre++exactWord g++tail)
        (CloseoutRowsPoolWeight.saved (gateItems g live) backing)
        (out++weightWord (C10SupplierRowInput.hardwire live g y)) (gateMembers live)⟩
    q 1 1 r hr hf

end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireWeightDock
