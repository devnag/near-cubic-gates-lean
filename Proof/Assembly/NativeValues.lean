import Proof.Assembly.OrderedCallsSelectedInputs
import Proof.MachineModel.ControllerCappedRuntime
import Proof.MachineModel.TopDownPaidFamilySum
import Proof.Hierarchy.CompetitorRawRecordEmit
import Proof.CaseAnalysis.FinalSingleAppend
import Proof.MachineModel.TopDownPaidFamilyReserves
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace NativeRecipes

noncomputable abbrev datumValue (d : P1TopDownPaidReusable.Datum) : Nat :=
  (selected (CompetitorSelectedCells.cells d.row.odd d.f d.select)).sum

noncomputable abbrev SymRows (sources : EightSources) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (L target : Nat)
 (printer : WilliamsAlgorithm) (S R B b : Nat) (ds : List P1TopDownPaidReusable.Datum) (total denominator : Nat) : Prop :=
let a := decompositionOf sources
let target := fun _ : Nat => target
∃ (s : Nat),
∃ (w : Nat),
∃ (degree : Nat),
∃ (harity : (s+1)/2+s/2=(normalizedLiveSet (symmetricFourfoldOccurrences r) L)ᶜ.card),
∃ (hs : 67 ≤ s),
∃ (hpos : 1 ≤ w),
∃ (hload : 200*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (symmetricFourfoldOccurrences r) L).card+2)) ≤ s),
∃ (hmon : ∀ x∈pairList L target r,
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
      (symmetricFourfoldOccurrences r) (familyPolynomial L target r x.1 x.2)).length<2^w),
∃ (hdegree : ∀ x∈pairList L target r,
    RawMonomialDegreeAtMost degree (familyPolynomial L target r x.1 x.2)),
∃ (c : Nat),
∃ (e : Nat),
∃ (hcache : CompactBounds.radix a (normalizedLiveSet (symmetricFourfoldOccurrences r) L)
    (symmetricFourfoldOccurrences r) ≤ c*(r.q+1)^e),
∃ (hdeg : degree ≤ r.q+1),
let V := driverCapacity printer r.q s c e
ds.Perm (symData a r L target s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e)) ∧
 S=workspace printer V ∧ R=rewind printer V ∧ B=buffer V ∧
 b=P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (symmetricFourfoldOccurrences r) L) (symmetricFourfoldOccurrences r) s harity degree ∧
total=CloseoutFinalC10SupplierAccuracy.rowAnswer (symmetricFourfoldRows (expanderOf sources) L target) r.q r.circuits ∧
 denominator=CloseoutFinalC10SupplierAccuracy.rowDenominator (symmetricFourfoldRows (expanderOf sources) L target) r.q r.circuits

noncomputable abbrev ThrRows (sources : EightSources) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : Nat)
 (printer : WilliamsAlgorithm) (S R B b : Nat) (ds : List P1TopDownPaidReusable.Datum) (total denominator : Nat) : Prop :=
let a := decompositionOf sources
let listDen := CloseoutFinalC10ThresholdRows.listDenominator a r target
let cutoff := CloseoutFinalC10ThresholdRows.primeCutoff a r target
∃ (s : Nat),
∃ (w : Nat),
∃ (degree : Nat),
∃ (harity : (s+1)/2+s/2=(normalizedLiveSet (thresholdFourfoldOccurrences r) L)ᶜ.card),
∃ (hs : 67 ≤ s),
∃ (hpos : 1 ≤ w),
∃ (hload : 200*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+
    w*((normalizedLiveSet (thresholdFourfoldOccurrences r) L).card+2)) ≤ s),
∃ (hmon : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    (CloseoutRowsUniversal.lower a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
      (thresholdFourfoldOccurrences r) (thresholdRow a r sel L listDen prime.val offset.val sample)).length<2^w),
∃ (hdegree : ∀ (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (sample : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) L listDen)
    (offset : Fin prime.val),
    RawMonomialDegreeAtMost degree (thresholdRow a r sel L listDen prime.val offset.val sample)),
∃ (c : Nat),
∃ (e : Nat),
∃ (hcache : CompactBounds.radix a (normalizedLiveSet (thresholdFourfoldOccurrences r) L)
    (thresholdFourfoldOccurrences r) ≤ c*(r.q+1)^e),
∃ (hdeg : degree ≤ r.q+1),
let V := driverCapacity printer r.q s c e
ds.Perm (thrData a r L listDen cutoff s w degree harity hs hpos hload hmon hdegree (headerCapacity r.q s c e)) ∧
 S=workspace printer V ∧ R=rewind printer V ∧ B=buffer V ∧
 b=P1TopDownFamilyShape.commonWidth a (normalizedLiveSet (thresholdFourfoldOccurrences r) L) (thresholdFourfoldOccurrences r) s harity degree ∧
total=C10ThresholdNaturalSum.nativeNumerator a r L listDen cutoff ∧
 denominator=C10ThresholdNaturalSum.nativeDenominator r L listDen cutoff

noncomputable abbrev NativeRows (sources : EightSources) (L target : Nat) (mode : Bool)
 {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
 (atoms : List (C10TotalDecode.Atom pcpp))
 (printer : WilliamsAlgorithm) (S R B b : Nat) (ds : List P1TopDownPaidReusable.Datum)
 (total denominator : Nat) : Prop :=
 (∀ atom∈atoms,C10NaturalModeAtoms.ModeAtom mode atom) ∧
 if mode then SymRows sources ⟨q,atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ L target printer S R B b ds total denominator
 else ThrRows sources ⟨q,atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ L target printer S R B b ds total denominator

noncomputable abbrev ValuesContract : Prop :=
∀ (sources : EightSources) (L target : Nat) (mode : Bool)
 {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
 (atoms : List (C10TotalDecode.Atom pcpp)) (printer : WilliamsAlgorithm)
 (S R B b : Nat) (ds : List P1TopDownPaidReusable.Datum) (total denominator : Nat),
 NativeRows sources L target mode atoms printer S R B b ds total denominator →
 (∀ k (hk:k<ds.length),P1TopDownPaidReusable.Valid printer B R S ds[k]) ∧
 ds.map P1TopDownPaidReusable.Datum.emit=(ds.map datumValue).map (SignedSortKey.binary b) ∧
 (∀ x∈ds.map datumValue,x<2^b) ∧ (ds.map datumValue).sum=total

end NativeRecipes
