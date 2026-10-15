import Proof.MachineModel.TopDownPaidBinaryReserves

/-! Substitute explicit common reserves into both actual family consumers.
No storage-capacity hypothesis remains; the displayed source bank is still
an upstream physical production duty. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidFamilyReserves
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal CloseoutRawRows
open C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow
open C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord
open CloseoutFinalC10SupplierAccuracy (rowAnswer)
open C10ThresholdNaturalSum (nativeNumerator)
open P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
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

  (c e : Nat)
  (hcache : CompactBounds.radix a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
    (symmetricFourfoldOccurrences r) ≤ c*(r.q+1)^e) (hdeg : degree ≤ r.q+1)

include hcache hdeg

theorem sym_physical (printer : WilliamsAlgorithm) :
    let V:=driverCapacity printer r.q s c e
    ∀ d∈symData a r L target s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e),
      PhysicalBounds printer (buffer V) (rewind printer V) (workspace printer V) d := by
  dsimp only
  intro d hd
  change d∈(pairList L target r).attach.map _ at hd
  obtain ⟨x,_hx,rfl⟩:=List.mem_map.mp hd
  unfold symDatum
  exact binary_physical a _ _ s harity w degree hs hpos hload printer _ c e hcache hdeg

set_option maxHeartbeats 1000000 in
theorem sym_run (printer : WilliamsAlgorithm) (spectrum : ExpanderSpectrumContract)
    (dflt : Datum) (out : List Bool) :
    let C:=headerCapacity r.q s c e
    let V:=driverCapacity printer r.q s c e
    let B:=buffer V
    let R:=rewind printer V
    let S:=workspace printer V
    let ds:=symData a r L target s w degree harity hs hpos hload hmon hdegree C
    let b:=P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (symmetricFourfoldOccurrences r) L) (symmetricFourfoldOccurrences r) s harity degree
    let rowCost:=(3*P1TopDownPaidPayload.tapes printer+6)*(S+1)
    ∃ T, Step (familyWriter (machine printer))
        (familyFuel (payloadWords b L target r).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (payloadWords b L target r).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (payloadWords b L target r).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (P1TopDownPaidReusable.source printer ds S R B (payloadWords b L target r).length
            (out ++ (payloadWords b L target r).flatten))
          (payloadWords b L target r).length 1).heads T ∧
      T ((outputSlot printer).castAdd 1) =
        out ++ CompetitorCountFold.raw b (payloadList L target r) ∧
      (payloadList L target r).sum
        = rowAnswer (symmetricFourfoldRows spectrum L target) r.q r.circuits := by
  dsimp only
  exact actualSym_run a r L target s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e) printer spectrum (buffer (driverCapacity printer r.q s c e))
    (rewind printer (driverCapacity printer r.q s c e))
    (workspace printer (driverCapacity printer r.q s c e)) dflt out
    (sym_physical a r L target s w degree harity hs hpos hload hmon hdegree c e hcache hdeg printer)

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

  (c e : Nat)
  (hcache : CompactBounds.radix a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
    (thresholdFourfoldOccurrences r) ≤ c*(r.q+1)^e) (hdeg : degree ≤ r.q+1)

include hcache hdeg

theorem thr_physical (printer : WilliamsAlgorithm) :
    let V:=driverCapacity printer r.q s c e
    ∀ d∈thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e),
      PhysicalBounds printer (buffer V) (rewind printer V) (workspace printer V) d := by
  dsimp only
  intro d hd
  simp only [thrData,List.mem_flatMap,List.mem_map] at hd
  obtain ⟨sel,_hsel,prime,_hprime,sample,_hsample,offset,_hoffset,rfl⟩:=hd
  unfold thrDatum
  exact binary_physical a _ _ s harity w degree hs hpos hload printer _ c e hcache hdeg

set_option maxHeartbeats 1000000 in
theorem thr_run (printer : WilliamsAlgorithm)
    (dflt : Datum) (out : List Bool) :
    let C:=headerCapacity r.q s c e
    let V:=driverCapacity printer r.q s c e
    let B:=buffer V
    let R:=rewind printer V
    let S:=workspace printer V
    let ds:=thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C
    let b:=P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (thresholdFourfoldOccurrences r) L) (thresholdFourfoldOccurrences r) s harity degree
    let rowCost:=(3*P1TopDownPaidPayload.tapes printer+6)*(S+1)
    ∃ T, Step (familyWriter (machine printer))
        (familyFuel (thresholdPayloadWords a r b L listDen cutoff).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (thresholdPayloadWords a r b L listDen cutoff).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (P1TopDownPaidReusable.source printer ds S R B 0 out)
          (thresholdPayloadWords a r b L listDen cutoff).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (P1TopDownPaidReusable.source printer ds S R B (thresholdPayloadWords a r b L listDen cutoff).length
            (out ++ (thresholdPayloadWords a r b L listDen cutoff).flatten))
          (thresholdPayloadWords a r b L listDen cutoff).length 1).heads T ∧
      T ((outputSlot printer).castAdd 1) =
        out ++ CompetitorCountFold.raw b (thresholdPayloadList a r L listDen cutoff) ∧
      (thresholdPayloadList a r L listDen cutoff).sum
        = nativeNumerator a r L listDen cutoff := by
  dsimp only
  exact actualThr_run a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e) printer (buffer (driverCapacity printer r.q s c e))
    (rewind printer (driverCapacity printer r.q s c e))
    (workspace printer (driverCapacity printer r.q s c e)) dflt out
    (thr_physical a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree c e hcache hdeg printer)

end Thr

end NearCubicWires.P1TopDownPaidFamilyReserves
