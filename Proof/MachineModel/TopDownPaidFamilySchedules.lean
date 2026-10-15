import Proof.MachineModel.TopDownPaidFamilyRows

/-! The original ordered external-row schedules, instantiated with real
binary C.10 requests. The emitted list is the exact parent's payload list. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal CloseoutRawRows
open C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow
open C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord
attribute [local irreducible] BinaryPool.pool CompactBounds.radix
  symDatum thrDatum familyPolynomial pairList

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (L : Nat) (target : Nat→Nat) (s w degree : Nat)
  (harity : (s+1)/2+s/2=(normalizedLiveSet (symmetricFourfoldOccurrences r) L)ᶜ.card)
  (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+2)) ≤ s)
  (hmon : ∀ x∈pairList L target r,
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
      (symmetricFourfoldOccurrences r) (familyPolynomial L target r x.1 x.2)).length<2^w)
  (hdegree : ∀ x∈pairList L target r,
    RawMonomialDegreeAtMost degree (familyPolynomial L target r x.1 x.2))
  (C : Nat)

set_option maxHeartbeats 1000000 in
noncomputable def symData : List Datum :=
  (pairList L target r).attach.map (fun x=>
    symDatum a r L target s w degree harity hs hpos hload x.val.1 x.val.2
      (hmon x.val x.property) (hdegree x.val x.property) C)

theorem symData_emits :
    (symData a r L target s w degree harity hs hpos hload hmon hdegree C).map Datum.emit=
      payloadWords (P1TopDownFamilyShape.commonWidth a
        (normalizedLiveSet (symmetricFourfoldOccurrences r) L) (symmetricFourfoldOccurrences r) s harity degree)
        L target r := by
  simp only [symData,List.map_map,Function.comp_def,sym_emit,payloadWords,payloadList,
    List.map_subtype,List.unattach_attach]
end Sym

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (L listDen cutoff s w degree : Nat)
  (harity : (s+1)/2+s/2=(normalizedLiveSet (thresholdFourfoldOccurrences r) L)ᶜ.card)
  (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+2)) ≤ s)
  (hmon : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
      (thresholdFourfoldOccurrences r) (thresholdRow a r sel L listDen prime.val offset.val sample)).length<2^w)
  (hdegree : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    RawMonomialDegreeAtMost degree (thresholdRow a r sel L listDen prime.val offset.val sample))
  (C : Nat)

noncomputable def thrData : List Datum :=
  (Finset.univ : Finset (ThresholdRows.Selection a r)).toList.flatMap (fun sel=>
    (Finset.univ : Finset (PrimeIndex cutoff)).toList.flatMap (fun prime=>
      (Finset.univ : Finset (NormalizedOccurrenceListSeed
        (thresholdFourfoldOccurrences r) L listDen)).toList.flatMap (fun sample=>
        (Finset.univ : Finset (Fin prime.val)).toList.map (fun offset=>
          thrDatum a r L listDen s w degree harity hs hpos hload sel prime sample offset
            (hmon sel prime sample offset) (hdegree sel prime sample offset) C))))

theorem thrData_emits :
    (thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C).map Datum.emit=
      thresholdPayloadWords a r (P1TopDownFamilyShape.commonWidth a
        (normalizedLiveSet (thresholdFourfoldOccurrences r) L) (thresholdFourfoldOccurrences r) s harity degree)
        L listDen cutoff := by
  simp only [thrData,List.map_flatMap,List.map_map,Function.comp_def,thr_emit,
    thresholdPayloadWords,thresholdPayloadList]
end Thr

end NearCubicWires.P1TopDownPaidReusable
