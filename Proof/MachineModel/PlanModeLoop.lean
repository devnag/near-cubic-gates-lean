import Proof.CaseAnalysis.FinalThresholdEstimateRowJoin

/-! Consumer application: THR's dependent row list uses the existing family
loop. The actual hrow execution and next-state invariant remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Plan.Modes
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SupplierPipeline SourceInterfaces CanonicalFourfoldRowProgram
open RepairRepresentation
open RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
open RepairSource.CloseoutFinal.C10ThresholdNaturalSum
open RepairSource.CloseoutFinal.C10ExternalRowLoop
open CloseoutFinalC10RowAnswerWord
noncomputable section
theorem threshold_raw_family_run (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (liveScale listDen cutoff w : Nat)
    {tp st : ℕ} (body : Machine tp st)
    (source : ℕ → List Bool → Configuration tp st) (slot : Fin tp) (rowCost : ℕ)
    (out : List Bool)
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < (thresholdPayloadWords a r w liveScale listDen cutoff).length,
      ∀ pre, (source k pre).control = body.start)
    (hrow : ∀ k < (thresholdPayloadWords a r w liveScale listDen cutoff).length,
      ∀ pre, ∃ rc : ExecutionReceipt tp st,
        runFrom body rowCost (source k pre) = some rc ∧
        rc.final.heads = (source (k + 1) (pre ++
          (thresholdPayloadWords a r w liveScale listDen cutoff).getD k [])).heads ∧
        rc.final.tapes = (source (k + 1) (pre ++
          (thresholdPayloadWords a r w liveScale listDen cutoff).getD k [])).tapes ∧
        rc.steps ≤ rowCost) :
    ∃ T, Step (familyWriter body)
        (familyFuel (thresholdPayloadWords a r w liveScale listDen cutoff).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (thresholdPayloadWords a r w liveScale listDen cutoff).length
            (out ++ (thresholdPayloadWords a r w liveScale listDen cutoff).flatten))
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).heads T ∧
      T (slot.castAdd 1) =
        out ++ CompetitorCountFold.raw w (thresholdPayloadList a r liveScale listDen cutoff) ∧
      (thresholdPayloadList a r liveScale listDen cutoff).sum
        = nativeNumerator a r liveScale listDen cutoff := by
  obtain ⟨rc, hr, hf, hst⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => (thresholdPayloadWords a r w liveScale listDen cutoff).getD k []) rowCost
    (thresholdPayloadWords a r w liveScale listDen cutoff).length hstart hrow out
  rw [flatten_getD (thresholdPayloadWords a r w liveScale listDen cutoff)] at hf
  refine ⟨_, ⟨rc, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hst⟩, ?_,
    thresholdPayloadList_sum a r liveScale listDen cutoff⟩
  rw [RepairSource.CloseoutFinal.C10SupplierSelect.cfg_tapes_castAdd]
  rw [hslot, thresholdPayloadWords_flatten]

end
end NearCubicWires.P1Plan.Modes
