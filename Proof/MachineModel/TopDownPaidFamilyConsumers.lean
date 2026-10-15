import Proof.MachineModel.TopDownPaidFamilySchedules

/-! Actual family applications with the row semantics and execution discharged.
Only original source construction and concrete capacity inequalities remain. -/
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
open CloseoutFinalC10SupplierAccuracy (rowAnswer)
open C10ThresholdNaturalSum (nativeNumerator)
attribute [local irreducible] BinaryPool.pool CompactBounds.radix
  symDatum thrDatum familyPolynomial pairList

structure PhysicalBounds (a : WilliamsAlgorithm) (B R S : Nat) (d : Datum) : Prop where
  capacity : (Header.stream d.row).length ≤ d.C
  rewind : P1TopDownPaidReloadCore.fuel a d.row d.C d.Q ≤ R
  buffer : RowPayload.budget (scalarWidth (EquationRow.request d.row) d.Q) ≤ B
  reset : B+1 ≤ R
  workspace : P1TopDownPaidReloadCore.budget a d.row d.C d.Q B+1 ≤ S
  bufferWorkspace : B ≤ S

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
theorem symData_valid (printer : WilliamsAlgorithm) (B R S : Nat)
    (hb : ∀ d∈symData a r L target s w degree harity hs hpos hload hmon hdegree C,
      PhysicalBounds printer B R S d) :
    ∀ k (hk : k<(symData a r L target s w degree harity hs hpos hload hmon hdegree C).length),
      Valid printer B R S (symData a r L target s w degree harity hs hpos hload hmon hdegree C)[k] := by
  intro k hk
  have hm:=List.getElem_mem hk
  change (symData a r L target s w degree harity hs hpos hload hmon hdegree C)[k]∈
    (pairList L target r).attach.map _ at hm
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
  have hb':=hb _ (List.getElem_mem hk)
  rw [←he] at hb' ⊢
  unfold symDatum at hb' ⊢
  exact binary_valid a _ _ s harity w degree hs hpos hload printer _ C B R S
    hb'.capacity hb'.rewind hb'.buffer hb'.reset hb'.workspace hb'.bufferWorkspace

set_option maxHeartbeats 1000000 in
theorem actualSym_run (printer : WilliamsAlgorithm) (spectrum : ExpanderSpectrumContract)
    (B R S : Nat) (dflt : Datum) (out : List Bool)
    (hb : ∀ d∈symData a r L target s w degree harity hs hpos hload hmon hdegree C,PhysicalBounds printer B R S d) :
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
  have hv:=symData_valid a r L target s w degree harity hs hpos hload hmon hdegree C printer B R S hb
  exact sym_family_run printer spectrum L target r.q _ r.circuits _ dflt S R B _ out hv
    (fun k hk=>uniform_budget printer B R S _ (hv k hk))
    (symData_emits a r L target s w degree harity hs hpos hload hmon hdegree C)

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

set_option maxHeartbeats 1000000 in
theorem thrData_valid (printer : WilliamsAlgorithm) (B R S : Nat)
    (hb : ∀ d∈thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C,
      PhysicalBounds printer B R S d) :
    ∀ k (hk : k<(thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C).length),
      Valid printer B R S (thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C)[k] := by
  intro k hk
  have hm:=List.getElem_mem hk
  change (thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C)[k]∈
    thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C at hm
  simp only [thrData,List.mem_flatMap,List.mem_map] at hm
  obtain ⟨sel,hsel,prime,hprime,sample,hsample,offset,hoffset,he⟩:=hm
  change thrDatum a r L listDen s w degree harity hs hpos hload sel prime sample offset
    (hmon sel prime sample offset) (hdegree sel prime sample offset) C=
    (thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C)[k] at he
  have hb':=hb _ (List.getElem_mem hk)
  rw [←he] at hb' ⊢
  unfold thrDatum at hb' ⊢
  exact binary_valid a _ _ s harity w degree hs hpos hload printer _ C B R S
    hb'.capacity hb'.rewind hb'.buffer hb'.reset hb'.workspace hb'.bufferWorkspace

set_option maxHeartbeats 1000000 in
theorem actualThr_run (printer : WilliamsAlgorithm)
    (B R S : Nat) (dflt : Datum) (out : List Bool)
    (hb : ∀ d∈thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C,PhysicalBounds printer B R S d) :
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
  have hv:=thrData_valid a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C printer B R S hb
  exact thr_family_run printer a r L listDen cutoff _ _ dflt S R B _ out hv
    (fun k hk=>uniform_budget printer B R S _ (hv k hk))
    (thrData_emits a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree C)

end Thr

end NearCubicWires.P1TopDownPaidReusable
