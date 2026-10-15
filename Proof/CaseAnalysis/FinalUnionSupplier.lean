import Proof.CaseAnalysis.FinalSupplierAccuracyChain
import Proof.CaseAnalysis.FinalTotalDecode
import Proof.CaseAnalysis.FinalThresholdRows
import Proof.CaseAnalysis.RowsEstimatorParitySymmetric

namespace NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The coproduct family -/

/-- The union of two circuit families, arity by arity.  `CircuitFamily` is
`ℕ → Type` (`Proof/Foundations/SupplierPipeline.lean`), so the coproduct is the
pointwise sum; no structure field obstructs it. -/
abbrev UnionFamily (Left Right : CircuitFamily) : CircuitFamily :=
  fun q => Left q ⊕ Right q

/-- Evaluation of a union atom: the branch's own evaluation. -/
def unionEvaluate {Left Right : CircuitFamily}
    (evalLeft : {q : ℕ} → Left q → BitInput q → Bool)
    (evalRight : {q : ℕ} → Right q → BitInput q → Bool) :
    {q : ℕ} → UnionFamily Left Right q → BitInput q → Bool :=
  fun {_q} atom input =>
    match atom with
    | Sum.inl circuit => evalLeft circuit input
    | Sum.inr circuit => evalRight circuit input

@[simp] theorem unionEvaluate_inl {Left Right : CircuitFamily}
    (evalLeft : {q : ℕ} → Left q → BitInput q → Bool)
    (evalRight : {q : ℕ} → Right q → BitInput q → Bool)
    {q : ℕ} (circuit : Left q) (input : BitInput q) :
    unionEvaluate evalLeft evalRight (Sum.inl circuit) input =
      evalLeft circuit input := rfl

@[simp] theorem unionEvaluate_inr {Left Right : CircuitFamily}
    (evalLeft : {q : ℕ} → Left q → BitInput q → Bool)
    (evalRight : {q : ℕ} → Right q → BitInput q → Bool)
    {q : ℕ} (circuit : Right q) (input : BitInput q) :
    unionEvaluate evalLeft evalRight (Sum.inr circuit) input =
      evalRight circuit input := rfl

/-! ## §2 Splitting a mixed request

A `FourfoldRequest` (`Proof/Foundations/SupplierPipeline.lean`) is an arity and a
LIST of circuits at that arity, so a request at the union family is a MIXED
list: it is not the image of a request at either branch.  It is however the
JOIN of one request per branch, and the AND-four conjunction factors along that
join. -/

/-- The left-branch circuits of a mixed list. -/
def leftCircuits {Left Right : CircuitFamily} {q : ℕ} :
    List (UnionFamily Left Right q) → List (Left q)
  | [] => []
  | Sum.inl circuit :: rest => circuit :: leftCircuits rest
  | Sum.inr _ :: rest => leftCircuits rest

/-- The right-branch circuits of a mixed list. -/
def rightCircuits {Left Right : CircuitFamily} {q : ℕ} :
    List (UnionFamily Left Right q) → List (Right q)
  | [] => []
  | Sum.inl _ :: rest => rightCircuits rest
  | Sum.inr circuit :: rest => circuit :: rightCircuits rest

/-- The left-branch request. -/
def leftRequest {Left Right : CircuitFamily}
    (request : FourfoldRequest (UnionFamily Left Right)) : FourfoldRequest Left :=
  ⟨request.q, leftCircuits request.circuits⟩

/-- The right-branch request. -/
def rightRequest {Left Right : CircuitFamily}
    (request : FourfoldRequest (UnionFamily Left Right)) : FourfoldRequest Right :=
  ⟨request.q, rightCircuits request.circuits⟩

private theorem conjunctionBit_cons {Circuit : Type} {q : ℕ}
    (evaluate : Circuit → BitInput q → Bool) (circuit : Circuit)
    (circuits : List Circuit) (input : BitInput q) :
    conjunctionBit evaluate (circuit :: circuits) input =
      (evaluate circuit input && conjunctionBit evaluate circuits input) := rfl

/-- **The AND-four conjunction factors along the split.**  This is what makes
the coproduct possible at all: the union request's target bit is the AND of the
two branch target bits. -/
theorem conjunctionBit_union {Left Right : CircuitFamily}
    (evalLeft : {q : ℕ} → Left q → BitInput q → Bool)
    (evalRight : {q : ℕ} → Right q → BitInput q → Bool)
    {q : ℕ} (circuits : List (UnionFamily Left Right q)) (input : BitInput q) :
    conjunctionBit (unionEvaluate evalLeft evalRight) circuits input =
      (conjunctionBit evalLeft (leftCircuits circuits) input &&
        conjunctionBit evalRight (rightCircuits circuits) input) := by
  induction circuits with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head with
      | inl circuit =>
          show (unionEvaluate evalLeft evalRight (Sum.inl circuit) input &&
            conjunctionBit (unionEvaluate evalLeft evalRight) tail input) = _
          rw [unionEvaluate_inl, inductionHypothesis]
          show _ = (conjunctionBit evalLeft (circuit :: leftCircuits tail) input &&
            conjunctionBit evalRight (rightCircuits tail) input)
          rw [conjunctionBit_cons, Bool.and_assoc]
      | inr circuit =>
          show (unionEvaluate evalLeft evalRight (Sum.inr circuit) input &&
            conjunctionBit (unionEvaluate evalLeft evalRight) tail input) = _
          rw [unionEvaluate_inr, inductionHypothesis]
          show _ = (conjunctionBit evalLeft (leftCircuits tail) input &&
            conjunctionBit evalRight (circuit :: rightCircuits tail) input)
          rw [conjunctionBit_cons]
          cases evalRight circuit input <;>
            cases conjunctionBit evalLeft (leftCircuits tail) input <;>
            cases conjunctionBit evalRight (rightCircuits tail) input <;> rfl

/-! ## §3 The analytic core: mismatch subadditivity for `&&` -/

private theorem bitAsReal_and_mismatch (a b c d : Bool) :
    bitAsReal ((a && b) != (c && d)) ≤ bitAsReal (a != c) + bitAsReal (b != d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [bitAsReal]

private theorem booleanMean_equiv {Index Target : Type} [Fintype Index]
    [Fintype Target] (enumeration : Index ≃ Target) (value : Target → Bool) :
    booleanMean (fun index => value (enumeration index)) = booleanMean value := by
  have hsum : (∑ index, bitAsReal (value (enumeration index))) =
      ∑ target, bitAsReal (value target) :=
    Equiv.sum_comp enumeration (fun target => bitAsReal (value target))
  unfold booleanMean
  rw [hsum, Fintype.card_congr enumeration]

/-- **The product-row error bound.**  A row that is the conjunction of one left
row and one right row mismatches the conjunction of the two targets only where
one of the factors mismatches, so the product family's mean mismatch is at most
the SUM of the two branch means. -/
private theorem booleanMean_and_le {mA mB : ℕ} (hA : 0 < mA) (hB : 0 < mB)
    (A : Fin mA → Bool) (B : Fin mB → Bool) (targetA targetB : Bool) :
    booleanMean (fun index : Fin (mA * mB) =>
        (A (finProdFinEquiv.symm index).1 && B (finProdFinEquiv.symm index).2) !=
          (targetA && targetB)) ≤
      booleanMean (fun index => A index != targetA) +
        booleanMean (fun index => B index != targetB) := by
  have hmA : (0 : ℝ) < (mA : ℝ) := by exact_mod_cast hA
  have hmB : (0 : ℝ) < (mB : ℝ) := by exact_mod_cast hB
  have hmAne : (mA : ℝ) ≠ 0 := ne_of_gt hmA
  have hmBne : (mB : ℝ) ≠ 0 := ne_of_gt hmB
  have hleftSum :
      (∑ sample : Fin mA × Fin mB, bitAsReal (A sample.1 != targetA)) =
        (mB : ℝ) * ∑ index : Fin mA, bitAsReal (A index != targetA) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hrightSum :
      (∑ sample : Fin mA × Fin mB, bitAsReal (B sample.2 != targetB)) =
        (mA : ℝ) * ∑ index : Fin mB, bitAsReal (B index != targetB) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnumerator :
      (∑ sample : Fin mA × Fin mB,
          bitAsReal ((A sample.1 && B sample.2) != (targetA && targetB))) ≤
        (mB : ℝ) * (∑ index : Fin mA, bitAsReal (A index != targetA)) +
          (mA : ℝ) * ∑ index : Fin mB, bitAsReal (B index != targetB) := by
    rw [← hleftSum, ← hrightSum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun sample _ =>
      bitAsReal_and_mismatch (A sample.1) (B sample.2) targetA targetB
  calc booleanMean (fun index : Fin (mA * mB) =>
          (A (finProdFinEquiv.symm index).1 && B (finProdFinEquiv.symm index).2) !=
            (targetA && targetB))
      = booleanMean (fun sample : Fin mA × Fin mB =>
          (A sample.1 && B sample.2) != (targetA && targetB)) :=
        booleanMean_equiv finProdFinEquiv.symm
          (fun sample : Fin mA × Fin mB =>
            (A sample.1 && B sample.2) != (targetA && targetB))
    _ ≤ booleanMean (fun index => A index != targetA) +
          booleanMean (fun index => B index != targetB) := by
        unfold booleanMean
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (mA : ℝ) * (mB : ℝ))]
        have hexpand :
            ((∑ index : Fin mA, bitAsReal (A index != targetA)) / (mA : ℝ) +
                (∑ index : Fin mB, bitAsReal (B index != targetB)) / (mB : ℝ)) *
              ((mA : ℝ) * (mB : ℝ)) =
            (mB : ℝ) * (∑ index : Fin mA, bitAsReal (A index != targetA)) +
              (mA : ℝ) * ∑ index : Fin mB, bitAsReal (B index != targetB) := by
          field_simp
        rw [hexpand]
        exact hnumerator

/-! ## §4 THE COPRODUCT -/

/-- **The union row preprocessor.**  Rows are pairs (one per branch), the row
count is the PRODUCT of the branch row counts, and the failure is the SUM of the
branch failures.  Nothing here is exact: both branch engines are used verbatim
and neither field can collapse unless the corresponding branch field does. -/
def unionRows {Left Right : CircuitFamily}
    {evalLeft : {q : ℕ} → Left q → BitInput q → Bool}
    {evalRight : {q : ℕ} → Right q → BitInput q → Bool}
    (left : FourfoldRowPreprocessor Left evalLeft)
    (right : FourfoldRowPreprocessor Right evalRight) :
    FourfoldRowPreprocessor (UnionFamily Left Right)
      (unionEvaluate evalLeft evalRight) where
  rowCount request :=
    left.rowCount (leftRequest request) * right.rowCount (rightRequest request)
  rowCountPositive request :=
    Nat.mul_pos (left.rowCountPositive _) (right.rowCountPositive _)
  row request index input :=
    left.row (leftRequest request) (finProdFinEquiv.symm index).1 input &&
      right.row (rightRequest request) (finProdFinEquiv.symm index).2 input
  failure request :=
    left.failure (leftRequest request) + right.failure (rightRequest request)
  failureNonnegative request :=
    add_nonneg (left.failureNonnegative _) (right.failureNonnegative _)
  pointwise request input := by
    have hconj : conjunctionBit (unionEvaluate evalLeft evalRight) request.circuits
          input =
        (conjunctionBit evalLeft (leftRequest request).circuits input &&
          conjunctionBit evalRight (rightRequest request).circuits input) :=
      conjunctionBit_union evalLeft evalRight request.circuits input
    rw [hconj]
    refine le_trans (booleanMean_and_le
      (left.rowCountPositive (leftRequest request))
      (right.rowCountPositive (rightRequest request))
      (fun index => left.row (leftRequest request) index input)
      (fun index => right.row (rightRequest request) index input)
      (conjunctionBit evalLeft (leftRequest request).circuits input)
      (conjunctionBit evalRight (rightRequest request).circuits input)) ?_
    exact add_le_add (left.pointwise (leftRequest request) input)
      (right.pointwise (rightRequest request) input)

/-- The union row count is the product of the branch row counts. -/
theorem unionRows_rowCount {Left Right : CircuitFamily}
    {evalLeft : {q : ℕ} → Left q → BitInput q → Bool}
    {evalRight : {q : ℕ} → Right q → BitInput q → Bool}
    (left : FourfoldRowPreprocessor Left evalLeft)
    (right : FourfoldRowPreprocessor Right evalRight)
    (request : FourfoldRequest (UnionFamily Left Right)) :
    (unionRows left right).rowCount request =
      left.rowCount (leftRequest request) *
        right.rowCount (rightRequest request) := rfl

/-- The union failure is the sum of the branch failures. -/
theorem unionRows_failure {Left Right : CircuitFamily}
    {evalLeft : {q : ℕ} → Left q → BitInput q → Bool}
    {evalRight : {q : ℕ} → Right q → BitInput q → Bool}
    (left : FourfoldRowPreprocessor Left evalLeft)
    (right : FourfoldRowPreprocessor Right evalRight)
    (request : FourfoldRequest (UnionFamily Left Right)) :
    (unionRows left right).failure request =
      left.failure (leftRequest request) +
        right.failure (rightRequest request) := rfl

/-! ## §5 The requested accuracy: one reservation, two branches

`SupplierEstimator.reciprocalUnionDenominator` (`Proof/Supplier/SupplierEstimator.lean`)
reserves a factor of two on top of the caller's requested reciprocal accuracy;
at family size one that is exactly the reservation two summed branch errors
need. -/

/-- The accuracy each BRANCH is asked for, so that the two branch errors sum to
the accuracy the CALLER asked for. -/
def unionTarget (target : ℕ → ℕ) : ℕ → ℕ :=
  fun q => reciprocalUnionDenominator 1 (target q)

/-- **The union failure clears the caller's requested reciprocal accuracy.** -/
theorem unionRows_failure_le {Left Right : CircuitFamily}
    {evalLeft : {q : ℕ} → Left q → BitInput q → Bool}
    {evalRight : {q : ℕ} → Right q → BitInput q → Bool}
    (left : FourfoldRowPreprocessor Left evalLeft)
    (right : FourfoldRowPreprocessor Right evalRight) (target : ℕ → ℕ)
    (hleft : ∀ request : FourfoldRequest Left,
      left.failure request = 1 / ((unionTarget target request.q + 1 : ℕ) : ℝ))
    (hright : ∀ request : FourfoldRequest Right,
      right.failure request = 1 / ((unionTarget target request.q + 1 : ℕ) : ℝ))
    (request : FourfoldRequest (UnionFamily Left Right)) :
    (unionRows left right).failure request ≤
      1 / ((target request.q + 1 : ℕ) : ℝ) := by
  rw [unionRows_failure, hleft, hright]
  simpa [unionTarget, leftRequest, rightRequest] using
    reciprocalUnionBudget 1 (target request.q)

/-! ## §6 The decode union maps into the two-class coproduct

Paper A.8 (`paper.tex:2322`) and C.10 (`paper.tex:4106-4109`): the systematic
code coordinate is not a supplier mode of its own, it is the explicit native
parity circuit.  `normalizedParityCircuit` is that circuit in the symmetric
target class. -/

/-- The two-class union family the decoded atoms live in. -/
abbrev DecodeUnion : CircuitFamily :=
  UnionFamily NormalizedSymmetricThresholdCircuit NormalizedThresholdThresholdCircuit

/-- Its evaluation. -/
abbrev decodeUnionEvaluate :
    {q : ℕ} → DecodeUnion q → BitInput q → Bool :=
  unionEvaluate NormalizedSymmetricThresholdCircuit.eval
    NormalizedThresholdThresholdCircuit.eval

/-- **The atom bridge.**  The three-constructor decode union maps into the
two-class coproduct: the systematic constructor goes to the paper's native
parity circuit, the other two to their own branch. -/
noncomputable def atomToUnion {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} : C10TotalDecode.Atom pcpp → DecodeUnion N
  | C10TotalDecode.Atom.systematic index =>
      Sum.inl (RepairOrdinary.CloseoutRowsEstimatorParity.normalizedParityCircuit
        (pcpp.systematicSupport index))
  | C10TotalDecode.Atom.symmetric atom => Sum.inl atom
  | C10TotalDecode.Atom.threshold atom => Sum.inr atom

/-- **The bridge is semantics-preserving.**  For the systematic constructor this
is `normalizedParityCircuit_eval`; for the other two it is definitional. -/
theorem atomToUnion_eval {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} (atom : C10TotalDecode.Atom pcpp)
    (input : BitInput N) :
    decodeUnionEvaluate (atomToUnion atom) input =
      C10TotalDecode.evaluate atom input := by
  cases atom with
  | systematic index =>
      exact RepairOrdinary.CloseoutRowsEstimatorParity.normalizedParityCircuit_eval
        (pcpp.systematicSupport index) input
  | symmetric atom => rfl
  | threshold atom => rfl

theorem conjunctionBit_atomToUnion {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp))
    (input : BitInput N) :
    conjunctionBit decodeUnionEvaluate (atoms.map atomToUnion) input =
      conjunctionBit C10TotalDecode.evaluate atoms input := by
  induction atoms with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      show (decodeUnionEvaluate (atomToUnion head) input &&
        conjunctionBit decodeUnionEvaluate (tail.map atomToUnion) input) = _
      rw [atomToUnion_eval, inductionHypothesis]
      rfl

/-- **The bridge preserves the paper's `conjunctionProbability`.** -/
theorem conjunctionProbability_atomToUnion {N : ℕ} {circuit : BooleanCircuit N}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp)) :
    conjunctionProbability decodeUnionEvaluate (atoms.map atomToUnion) =
      conjunctionProbability C10TotalDecode.evaluate atoms := by
  unfold conjunctionProbability
  congr 1
  funext input
  exact conjunctionBit_atomToUnion atoms input

/-- **`StageData.answer` at the decode union**: the union rows' rescaled
acceptance count on the image of the mixed atom list. -/
noncomputable def unionAnswer
    (rows : FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate)
    (arity scale : ℕ) {circuit : BooleanCircuit arity}
    {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) : ℕ :=
  C10SupplierWidth.answer rows arity scale (atoms.map atomToUnion)

/-- **`StageData.supplier` at the decode union.** -/
noncomputable def unionSupplier
    (rows : FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate)
    (arity scale : ℕ) {circuit : BooleanCircuit arity}
    {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) : ℚ :=
  (unionAnswer rows arity scale atoms : ℚ) /
    (C10SupplierWidth.denominator arity scale : ℚ)

/-- **`StageBlock.hsupplier` at the decode union**: the answer over the uniform
denominator IS the supplier. -/
theorem unionSupplier_eq
    (rows : FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate)
    (arity scale : ℕ) {circuit : BooleanCircuit arity}
    {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) :
    (unionAnswer rows arity scale atoms : ℚ) /
        (C10SupplierWidth.denominator arity scale : ℚ) =
      unionSupplier rows arity scale atoms := rfl

/-- **`StageBlock.hcount` at the decode union.**  `C10SupplierWidth.answer_lt`
(`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is generic in `rows`, so the
union answer fits the same entry width as either branch's. -/
theorem unionAnswer_lt
    (rows : FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate)
    (coefficientFloor arity scale : ℕ → ℕ)
    {source : PointwisePCPPAlgorithm} (constants : Constants source) (n : ℕ)
    {circuit : BooleanCircuit (arity n)} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) :
    unionAnswer rows (arity n) (scale n) atoms <
      2 ^ C10SupplierWidth.entryWidth coefficientFloor arity scale constants n :=
  C10SupplierWidth.answer_lt rows coefficientFloor arity scale constants n
    (atoms.map atomToUnion)

/-- **`StageBlock.hpoint` at the decode union.**  The union supplier answers
every AND-four call on a MIXED atom list within `failureOf`, the paper's own
failure: the rows' requested reciprocal accuracy plus one ulp of the uniform
denominator. -/
theorem hpoint_of_unionRows
    (rows : FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate)
    (target arity scale : ℕ → ℕ) (n : ℕ) (x : BitInput n) (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    {circuit : BooleanCircuit (arity n)} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp))
    (hrows : rows.failure ⟨arity n, atoms.map atomToUnion⟩ ≤
      1 / ((target (arity n) + 1 : ℕ) : ℝ)) :
    |((unionSupplier rows (arity n) (scale n) atoms : ℚ) : ℝ) -
        conjunctionProbability C10TotalDecode.evaluate atoms| ≤
      C10SupplierAccuracyChain.failureOf target arity scale n x bits ph := by
  rw [← conjunctionProbability_atomToUnion]
  exact C10SupplierAccuracyChain.hpoint_of_rows rows target arity scale n x bits ph
    (atoms.map atomToUnion) hrows

/-! ## §8 The concrete union supplier at the EIGHT SOURCES

SYM: `SupplierEstimator.symmetricFourfoldRows` over `EightSources.expander`.
THR: `CloseoutFinalC10ThresholdRows.thresholdRows` over `EightSources.expander`,
`EightSources.prime` and `EightSources.decomposition` -- the corrected carrier,
with no `ExecutableExactDecompositionAlgorithm`. -/

/-- **THE UNION ROWS.**  A single row preprocessor accurate on lists mixing
native parity atoms, symmetric atoms and threshold atoms, at the eight sources
and nothing else. -/
noncomputable def unionAtomRows (sources : EightSources) (liveScale : ℕ)
    (target : ℕ → ℕ) :
    FourfoldRowPreprocessor DecodeUnion decodeUnionEvaluate :=
  unionRows (symmetricFourfoldRows (expanderOf sources) liveScale
      (unionTarget target))
    (NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows.thresholdRows
      (expanderOf sources) (primeOf sources) (decompositionOf sources) liveScale
      (unionTarget target))

/-- Its row count is the PRODUCT of the two branch row counts, each a function
of the request and of the requested accuracy. -/
theorem unionAtomRows_rowCount (sources : EightSources) (liveScale : ℕ)
    (target : ℕ → ℕ) (request : FourfoldRequest DecodeUnion) :
    (unionAtomRows sources liveScale target).rowCount request =
      (symmetricFourfoldRows (expanderOf sources) liveScale
          (unionTarget target)).rowCount (leftRequest request) *
        (NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows.thresholdRows
            (expanderOf sources) (primeOf sources) (decompositionOf sources)
            liveScale (unionTarget target)).rowCount (rightRequest request) := rfl

/-- **Its failure clears the caller's requested reciprocal accuracy.** -/
theorem unionAtomRows_failure_le (sources : EightSources) (liveScale : ℕ)
    (target : ℕ → ℕ) (request : FourfoldRequest DecodeUnion) :
    (unionAtomRows sources liveScale target).failure request ≤
      1 / ((target request.q + 1 : ℕ) : ℝ) :=
  unionRows_failure_le _ _ target (fun _ => rfl) (fun _ => rfl) request

/-- **`StageBlock.hpoint`, discharged at the eight sources.**  This is the
statement `StageBlock.hpoint` (`Proof/CaseAnalysis/FinalStageContracts.lean`)
asks for, at `S.supplier := unionSupplier (unionAtomRows ...)` and
`S.failure := failureOf target arity scale`, with the quantifier over MIXED
atom lists intact. -/
theorem hpoint_of_unionAtomRows (sources : EightSources) (liveScale : ℕ)
    (target arity scale : ℕ → ℕ) (n : ℕ) (x : BitInput n) (bits : List Bool)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    {circuit : BooleanCircuit (arity n)} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) :
    |((unionSupplier (unionAtomRows sources liveScale target) (arity n) (scale n)
            atoms : ℚ) : ℝ) -
        conjunctionProbability C10TotalDecode.evaluate atoms| ≤
      C10SupplierAccuracyChain.failureOf target arity scale n x bits ph :=
  hpoint_of_unionRows _ target arity scale n x bits ph atoms
    (unionAtomRows_failure_le sources liveScale target _)

end NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
