import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.CaseAnalysis.FinalPrinterResidue

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.ThresholdCompiler
open NearCubicWires.CanonicalFourfoldRowProgram

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrinterBridge

section Split

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- A.2's reassembly: the `q`-bit input whose live block (coordinates in
`normalizedLiveSet`) is `y` and whose residual block is `z`. -/
def inputOf
    (y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    BitInput request.q :=
  (normalizedLiveExternalInputEquiv
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm (y, z)

theorem inputOf_eq_elim
    (y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    inputOf request liveScale y z =
      fun coordinate =>
        Sum.elim y z
          ((normalizedLiveExternalCoordinateEquiv
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
              coordinate) := by
  unfold inputOf normalizedLiveExternalInputEquiv bitInputSumEquiv
  funext coordinate
  simp [Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

/-- The left summand of the coordinate split enumerates the live set. -/
theorem coordinateEquiv_inl_mem
    (index : Fin (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card) :
    normalizedLiveExternalCoordinateEquiv
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) (Sum.inl index) ∈
      normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale := by
  unfold normalizedLiveExternalCoordinateEquiv
  rw [finSumEquivOfFinset_inl]
  exact Finset.orderEmbOfFin_mem _ rfl index

/-- Off the live set the reassembled input depends on `z` alone. -/
theorem inputOf_congr_of_not_mem
    (y y' : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (coordinate : Fin request.q)
    (hcoordinate :
      coordinate ∉ normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) :
    inputOf request liveScale y z coordinate = inputOf request liveScale y' z coordinate := by
  rw [inputOf_eq_elim, inputOf_eq_elim]
  dsimp only
  rcases hsplit :
      (normalizedLiveExternalCoordinateEquiv
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
          coordinate with index | index
  · exfalso
    apply hcoordinate
    rw [(Equiv.symm_apply_eq _).mp hsplit]
    exact coordinateEquiv_inl_mem request liveScale index
  · rfl

end Split

section Frozen

/-- `frozenScore` reads the input only off the live set (A.2: "\(C_i\) ignores \(I\)"). -/
theorem frozenScore_congr {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (left right : BitInput n)
    (hequal : ∀ index, index ∉ live → left index = right index) :
    frozenScore gate live left = frozenScore gate live right := by
  unfold frozenScore
  apply Finset.sum_congr rfl
  intro index hindex
  rw [hequal index (Finset.mem_sdiff.mp hindex).2]

theorem residualConstant_congr {n : ℕ} (gate : NormalizedThresholdGate n)
    (live : Finset (Fin n)) (left right : BitInput n)
    (hequal : ∀ index, index ∉ live → left index = right index) :
    residualConstant gate live left = residualConstant gate live right := by
  unfold residualConstant
  rw [frozenScore_congr gate live left right hequal]

/-- \(C(z)=\sum_{i\in\text{mask}}C_i(z)\) reads the input only off the live set. -/
theorem occurrenceResidualConstantCount_congr {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (liveScale : ℕ)
    (left right : BitInput q)
    (hequal : ∀ index, index ∉ normalizedLiveSet occurrences liveScale →
      left index = right index)
    (mask : Finset (Fin occurrences.length)) :
    occurrenceResidualConstantCount occurrences liveScale left mask =
      occurrenceResidualConstantCount occurrences liveScale right mask := by
  unfold occurrenceResidualConstantCount occurrenceResidualConstant
  apply Finset.sum_congr rfl
  intro index _
  rw [residualConstant_congr _ _ left right hequal]

end Frozen

section Row

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- `holds`: the residual variable \(Z_i(y,z)\) (A.2) of the coded occurrence `code`,
in the ABI of `encodedFiniteBooleanAssignment` (invalid codes are false). -/
def residualHolds (code : ℕ)
    (y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    Bool :=
  encodedFiniteBooleanAssignment
    (fun index =>
      occurrenceResidualVariable (symmetricFourfoldOccurrences request)
        (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
        (inputOf request liveScale y z) index)
    code

/-- \(\mathbf F(z)\): the tuple of frozen circuit offsets \(C(z)=\sum_{i\in\text{mask}}C_i(z)\),
evaluated on the residual block `z` (the live block is immaterial, `residualOffset_spec`). -/
def residualOffset
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (circuitIndex : Fin request.circuits.length) : ℕ :=
  occurrenceResidualConstantCount (symmetricFourfoldOccurrences request) liveScale
    (inputOf request liveScale (fun _ => false) z)
    (symmetricCircuitMask request circuitIndex)

theorem residualOffset_spec
    (y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
    (circuitIndex : Fin request.circuits.length) :
    occurrenceResidualConstantCount (symmetricFourfoldOccurrences request) liveScale
        (inputOf request liveScale y z) (symmetricCircuitMask request circuitIndex) =
      residualOffset request liveScale z circuitIndex := by
  unfold residualOffset
  exact occurrenceResidualConstantCount_congr _ _ _ _
    (fun coordinate hcoordinate =>
      inputOf_congr_of_not_mem request liveScale y (fun _ => false) z coordinate hcoordinate)
    _

/-- The structural evaluator is `exactPolynomialValue` at a point: same monomial list,
`holds` specialised to `(y, z)`. -/
theorem evaluateStructuralGF2_eq_exactPolynomialValue
    {Row Column : Type} (holds : ℕ → Row → Column → Bool)
    (polynomial : StructuralGF2Polynomial) (y : Row) (z : Column) :
    evaluateStructuralGF2 (fun code => holds code y z) polynomial =
      exactPolynomialValue holds polynomial y z :=
  rfl

/-- **The printed row IS the estimator's row** (A.3, `…_eq_canonical`): at live block `y`
and residual block `z`, the printed polynomial for seed `sample` and offset vector
\(\mathbf F(z)\) evaluates to `canonicalSymmetricFourfoldRow` at the reassembled input. -/
theorem exactPolynomialValue_residualHolds (denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    exactPolynomialValue (residualHolds request liveScale)
        (structuralCanonicalSymmetricFourfoldRow request liveScale denominator sample
          (residualOffset request liveScale z)) y z =
      canonicalSymmetricFourfoldRow request liveScale denominator
        (inputOf request liveScale y z) sample := by
  rw [← evaluateStructuralGF2_eq_exactPolynomialValue]
  exact evaluateStructuralCanonicalSymmetricFourfoldRow_eq_canonical request liveScale
    denominator (inputOf request liveScale y z) sample (residualOffset request liveScale z)
    (fun circuitIndex => (residualOffset_spec request liveScale y z circuitIndex).symm)

/-- \(T_{e,\mathbf F(z)}(z)=\sum_y P_{e,\mathbf F(z)}(y,z)\) (A.13.9): the exact column
count of the printed row is the live-cube sum of the estimator's row. -/
theorem exactColumnCount_residualHolds (denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed
      (symmetricFourfoldOccurrences request) liveScale denominator)
    (z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) :
    exactColumnCount (residualHolds request liveScale)
        (structuralCanonicalSymmetricFourfoldRow request liveScale denominator sample
          (residualOffset request liveScale z)) z =
      ∑ y : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card,
        (canonicalSymmetricFourfoldRow request liveScale denominator
          (inputOf request liveScale y z) sample).toNat := by
  unfold exactColumnCount
  apply Finset.sum_congr rfl
  intro y _
  rw [exactPolynomialValue_residualHolds]

end Row

section Bridge

variable (spectrum : ExpanderSpectrumContract) (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
  (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- `FourfoldRowPreprocessor.aggregation` (SupplierEstimator:4624) and
`FiniteRowAggregation.acceptanceCount` (:4432) unfolded on `symmetricFourfoldRows` (:4915):
the count is the double sum, over the `Fin`-indexed seeds and all `q`-bit inputs, of the
canonical row. -/
theorem acceptanceCount_unfold :
    ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation request).acceptanceCount =
      ∑ index : Fin (Fintype.card
          (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
            (symmetricListDenominator request (targetDenominator request.q)))),
        ∑ input : BitInput request.q,
          (canonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request (targetDenominator request.q)) input
            ((normalizedOccurrenceListSeedFinEquiv (symmetricFourfoldOccurrences request)
              liveScale (symmetricListDenominator request (targetDenominator request.q))).symm
                index)).toNat :=
  rfl

/-- **S5-core (A.13.9, paper.tex:3144–3160).**  The acceptance count of the symmetric
supplier's row family equals, summed over seeds `e` and residual columns `z`, the exact
column count \(T_{e,\mathbf F(z)}(z)\) of the printed polynomial for seed `e` and the
actual offset tuple \(\mathbf F(z)\) = `residualOffset request liveScale z`. -/
theorem acceptanceCount_eq_sum_exactColumnCount :
    ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation request).acceptanceCount =
      ∑ sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request (targetDenominator request.q)),
        ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
          exactColumnCount (residualHolds request liveScale)
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request (targetDenominator request.q)) sample
              (residualOffset request liveScale z)) z := by
  rw [acceptanceCount_unfold]
  rw [Equiv.sum_comp
    (normalizedOccurrenceListSeedFinEquiv (symmetricFourfoldOccurrences request)
      liveScale (symmetricListDenominator request (targetDenominator request.q))).symm
    (fun sample => ∑ input : BitInput request.q,
      (canonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request (targetDenominator request.q)) input sample).toNat)]
  apply Finset.sum_congr rfl
  intro sample _
  rw [← Equiv.sum_comp
    (normalizedLiveExternalInputEquiv
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)).symm
    (fun input : BitInput request.q =>
      (canonicalSymmetricFourfoldRow request liveScale
        (symmetricListDenominator request (targetDenominator request.q)) input sample).toNat)]
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro z _
  rw [exactColumnCount_residualHolds]
  rfl

/-- The same identity with the seeds indexed as the aggregation indexes them
(`Fin (rowCount request)`), for consumers that iterate the row index. -/
theorem acceptanceCount_eq_sum_exactColumnCount_fin :
    ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation request).acceptanceCount =
      ∑ index : Fin ((symmetricFourfoldRows spectrum liveScale targetDenominator).rowCount request),
        ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
          exactColumnCount (residualHolds request liveScale)
            (structuralCanonicalSymmetricFourfoldRow request liveScale
              (symmetricListDenominator request (targetDenominator request.q))
              ((normalizedOccurrenceListSeedFinEquiv (symmetricFourfoldOccurrences request)
                liveScale (symmetricListDenominator request (targetDenominator request.q))).symm
                  index)
              (residualOffset request liveScale z)) z := by
  rw [acceptanceCount_eq_sum_exactColumnCount]
  exact (Equiv.sum_comp
    (normalizedOccurrenceListSeedFinEquiv (symmetricFourfoldOccurrences request)
      liveScale (symmetricListDenominator request (targetDenominator request.q))).symm
    (fun sample =>
      ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        exactColumnCount (residualHolds request liveScale)
          (structuralCanonicalSymmetricFourfoldRow request liveScale
            (symmetricListDenominator request (targetDenominator request.q)) sample
            (residualOffset request liveScale z)) z)).symm

end Bridge

section Arity

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)

/-- \(K=|I|\) is the normalized live count. -/
theorem liveArity_eq :
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card =
      normalizedLiveCount request.q liveScale :=
  normalizedLiveSet_card _ _

/-- The residual arity is \(q-K\). -/
theorem residualArity_eq :
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card =
      request.q - normalizedLiveCount request.q liveScale := by
  rw [Finset.card_compl, Fintype.card_fin, liveArity_eq]

/-- The live cube has \(2^K\) rows. -/
theorem card_liveRow :
    Fintype.card
        (BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card) =
      2 ^ normalizedLiveCount request.q liveScale := by
  rw [card_bitInput, liveArity_eq]

/-- There are \(2^{q-K}\) residual columns. -/
theorem card_residualColumn :
    Fintype.card
        (BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card) =
      2 ^ (request.q - normalizedLiveCount request.q liveScale) := by
  rw [card_bitInput, residualArity_eq]

end Arity

section Residue

variable (spectrum : ExpanderSpectrumContract) (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
  (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- S5 closed through S3b/S3d: with thm:batch's `Q ≥ K + 1`, the acceptance count is the
sum over seeds and residual columns of the least nonnegative residue mod `2^Q` of the
printed signed score `∑_y BinLift_Q(t(y,z))` (`C10PrinterResidue.exactColumnCount_eq_residue`). -/
theorem acceptanceCount_eq_sum_residue (Q : ℕ)
    (hQ : normalizedLiveCount request.q liveScale < Q) :
    ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation request).acceptanceCount =
      ∑ sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
          (symmetricListDenominator request (targetDenominator request.q)),
        ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
          Int.toNat
            ((∑ y : BitInput
                (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card,
              binLift Q (polynomialOccurrenceCount (residualHolds request liveScale)
                (structuralCanonicalSymmetricFourfoldRow request liveScale
                  (symmetricListDenominator request (targetDenominator request.q)) sample
                  (residualOffset request liveScale z)) y z)) % (2 : ℤ) ^ Q) := by
  rw [acceptanceCount_eq_sum_exactColumnCount]
  apply Finset.sum_congr rfl
  intro sample _
  apply Finset.sum_congr rfl
  intro z _
  exact C10PrinterResidue.exactColumnCount_eq_residue _ _ z (card_liveRow request liveScale).le hQ

end Residue

end NearCubicWires.RepairSource.CloseoutFinal.C10PrinterBridge
