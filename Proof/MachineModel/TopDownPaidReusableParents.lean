import Proof.MachineModel.TopDownPaidReusableFamily
import Proof.MachineModel.PlanModeLoop

/-! Apply the completed physical hrow to both existing family consumers.
The list-to-payload equality is the explicit upstream semantic contract;
it does not supply an execution receipt or a row-loader callback. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open SupplierPipeline SupplierEstimator SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource.CloseoutFinal.C10ExternalRowLoop
open RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
open RepairSource.CloseoutFinal.C10ThresholdNaturalSum
open CloseoutFinalC10RowAnswerWord
open CloseoutFinalC10SupplierAccuracy (rowAnswer)
open P1TopDownPaidPayload (tapes)
attribute [local irreducible] machine CompetitorCrossScheduler.producer

noncomputable def outputSlot (a : WilliamsAlgorithm) : Fin (tapes a+1+2+4) :=
  ((0 : Fin 2).natAdd (tapes a+1)).castAdd 4

theorem source_output (a : WilliamsAlgorithm) (ds : List Datum) (S R B k : Nat) (out : List Bool) :
    (source a ds S R B k out).tapes (outputSlot a)=out := by
  simp [source,bank,outputSlot,P1TopDownPaidReusableBody.bank,P1Closure.RawRowJoin.bank]

set_option maxHeartbeats 1000000 in
theorem hrow_words (a : WilliamsAlgorithm) (ds : List Datum) (dflt : Datum)
    (S R B cost : Nat) (wanted : List (List Bool))
    (hv : ∀ k (hk : k<ds.length),Valid a B R S ds[k])
    (hb : ∀ k (hk : k<ds.length),(ds[k]).budget a B S≤cost)
    (hwords : ds.map Datum.emit=wanted) (k : Nat) (hk : k<wanted.length) (out : List Bool) :
    ∃ r,runFrom (machine a) cost (source a ds S R B k out)=some r ∧
      r.final.heads=(source a ds S R B (k+1) (out++wanted.getD k [])).heads ∧
      r.final.tapes=(source a ds S R B (k+1) (out++wanted.getD k [])).tapes ∧ r.steps≤cost := by
  have hk' : k<ds.length := by simpa only [←hwords,List.length_map] using hk
  have he : wanted.getD k []=(ds.getD k dflt).emit := by
    rw [←hwords]
    exact C10RowFrameJoin.getD_map Datum.emit ds k dflt [] hk'
  rw [he]
  exact hrow a ds dflt S R B cost hv hb k hk' out

set_option maxHeartbeats 1000000 in
theorem sym_family_run (printer : WilliamsAlgorithm) (spectrum : ExpanderSpectrumContract)
    (liveScale : Nat) (target : Nat→Nat) (arity w : Nat)
    (factors : List (NormalizedSymmetricThresholdCircuit arity))
    (ds : List Datum) (dflt : Datum) (S R B rowCost : Nat) (out : List Bool)
    (hv : ∀ k (hk : k<ds.length),Valid printer B R S ds[k])
    (hb : ∀ k (hk : k<ds.length),(ds[k]).budget printer B S≤rowCost)
    (hwords : ds.map Datum.emit=payloadWords w liveScale target ⟨arity,factors⟩) :
    ∃ T, Step (familyWriter (machine printer))
        (familyFuel (payloadWords w liveScale target ⟨arity, factors⟩).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (P1TopDownPaidReusable.source printer ds S R B (payloadWords w liveScale target ⟨arity, factors⟩).length
            (out ++ (payloadWords w liveScale target ⟨arity, factors⟩).flatten))
          (payloadWords w liveScale target ⟨arity, factors⟩).length 1).heads T ∧
      T ((outputSlot printer).castAdd 1) =
        out ++ CompetitorCountFold.raw w (payloadList liveScale target ⟨arity, factors⟩) ∧
      (payloadList liveScale target ⟨arity, factors⟩).sum
        = rowAnswer (symmetricFourfoldRows spectrum liveScale target) arity factors := by
  exact CloseoutFinalC10RowAnswerWord.raw_family_run spectrum liveScale target arity w factors
    (machine printer) (source printer ds S R B) (outputSlot printer) rowCost out
    (source_output printer ds S R B) (by intros;rfl)
    (hrow_words printer ds dflt S R B rowCost _ hv hb hwords)

set_option maxHeartbeats 1000000 in
theorem thr_family_run (printer : WilliamsAlgorithm) (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (liveScale listDen cutoff w : Nat)
    (ds : List Datum) (dflt : Datum) (S R B rowCost : Nat) (out : List Bool)
    (hv : ∀ k (hk : k<ds.length),Valid printer B R S ds[k])
    (hb : ∀ k (hk : k<ds.length),(ds[k]).budget printer B S≤rowCost)
    (hwords : ds.map Datum.emit=thresholdPayloadWords a r w liveScale listDen cutoff) :
    ∃ T, Step (familyWriter (machine printer))
        (familyFuel (thresholdPayloadWords a r w liveScale listDen cutoff).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (P1TopDownPaidReusable.source printer ds S R B (thresholdPayloadWords a r w liveScale listDen cutoff).length
            (out ++ (thresholdPayloadWords a r w liveScale listDen cutoff).flatten))
          (thresholdPayloadWords a r w liveScale listDen cutoff).length 1).heads T ∧
      T ((outputSlot printer).castAdd 1) =
        out ++ CompetitorCountFold.raw w (thresholdPayloadList a r liveScale listDen cutoff) ∧
      (thresholdPayloadList a r liveScale listDen cutoff).sum
        = nativeNumerator a r liveScale listDen cutoff := by
  exact P1Plan.Modes.threshold_raw_family_run a r liveScale listDen cutoff w
    (machine printer) (source printer ds S R B) (outputSlot printer) rowCost out
    (source_output printer ds S R B) (by intros;rfl)
    (hrow_words printer ds dflt S R B rowCost _ hv hb hwords)

end NearCubicWires.P1TopDownPaidReusable
