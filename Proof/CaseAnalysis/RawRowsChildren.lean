import Proof.CaseAnalysis.RawRowsModeDegree
import Proof.Circuits.DecompositionSourceBounds

/-! The exact existing residual-to-child substitution, specialized to the
corrected ordinary source. Its fresh output supplies the actual child bound. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierPrinter SupplierRadix
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def occurrenceExactChildren
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (index : Fin occurrences.length) : List (ExactThresholdGate q) :=
  (algorithm.output ⟨q, CompilerSemantics.nonStrictAsStrict
      (occurrences.get index).gate⟩).children

/-- The one total decoder for pair-coded exact children.  Keeping decoding
here prevents the semantic equation and Boolean assignment paths from
silently disagreeing on malformed addresses. -/
def occurrenceExactChild?
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (code : ℕ) : Option (ExactThresholdGate q) :=
  let address := Nat.unpair code
  if hoccurrence : address.1 < occurrences.length then
    let index : Fin occurrences.length := ⟨address.1, hoccurrence⟩
    if hchild : address.2 <
        (occurrenceExactChildren algorithm occurrences index).length then
      some ((occurrenceExactChildren algorithm occurrences index).get
        ⟨address.2, hchild⟩)
    else
      none
  else
    none

/-- Pair-coded exact-child assignment.  Invalid occurrence or child addresses
are false; generated atoms below use only canonical in-range pairs. -/
def occurrenceExactChildAssignment
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (code : ℕ) : Bool :=
  match occurrenceExactChild? algorithm occurrences code with
  | some child => child.eval input
  | none => false

@[simp] theorem occurrenceExactChildAssignment_pair
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (index : Fin occurrences.length)
    (childIndex :
      Fin (occurrenceExactChildren algorithm occurrences index).length) :
    occurrenceExactChildAssignment algorithm occurrences input
        (Nat.pair index.val childIndex.val) =
      ((occurrenceExactChildren algorithm occurrences index).get
        childIndex).eval input := by
  simp [occurrenceExactChildAssignment, occurrenceExactChild?,
    index.isLt, childIndex.isLt]

/-- Disjointness of the imported decomposition turns its exact-child OR into
linear GF(2) parity. -/
theorem occurrenceExactChildren_parity_eq
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (input : BitInput q) (index : Fin occurrences.length) :
    boolParity
        (fun childIndex :
            Fin (occurrenceExactChildren algorithm occurrences index).length =>
          ((occurrenceExactChildren algorithm occurrences index).get
            childIndex).eval input) =
      (occurrences.get index).eval input := by
  let gate := (occurrences.get index).gate
  let decomposition :=
    algorithm.output ⟨q, CompilerSemantics.nonStrictAsStrict gate⟩
  calc
    boolParity
        (fun childIndex : Fin decomposition.children.length =>
          (decomposition.children.get childIndex).eval input) =
        decomposition.children.any (fun child => child.eval input) :=
      boolParity_finGet_eq_any_of_disjoint decomposition.children
        (fun child => child.eval input) (decomposition.disjoint input)
    _ = (CompilerSemantics.nonStrictAsStrict gate).strictEval input :=
      (decomposition.equivalent input).symm
    _ = gate.eval input :=
      CompilerSemantics.nonStrictAsStrict_eval gate input
    _ = (occurrences.get index).eval input := rfl

/-- One occurrence residual lowered to imported exact-child variables.  A
frozen-one residual is identically zero; otherwise disjoint exact children are
added in GF(2). -/
def structuralOccurrenceResidualAtom
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (index : Fin occurrences.length) : StructuralGF2Polynomial :=
  if constant index then
    structuralGF2Zero
  else
    structuralGF2FinParity fun childIndex :
        Fin (occurrenceExactChildren algorithm occurrences index).length =>
      structuralGF2Variable (Nat.pair index.val childIndex.val)

@[simp] theorem evaluateStructuralOccurrenceResidualAtom
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (constant : Fin occurrences.length → Bool)
    (index : Fin occurrences.length)
    (hconstant :
      constant index =
        occurrenceResidualConstant occurrences live input index) :
    evaluateStructuralGF2
        (occurrenceExactChildAssignment algorithm occurrences input)
        (structuralOccurrenceResidualAtom algorithm occurrences constant index) =
      occurrenceResidualVariable occurrences live input index := by
  cases hresidualConstant :
      occurrenceResidualConstant occurrences live input index with
  | false =>
      have hconstantFalse : constant index = false :=
        hconstant.trans hresidualConstant
      have hresidualGate :
          residualConstant (occurrences.get index).gate live input = false := by
        simpa [occurrenceResidualConstant] using hresidualConstant
      rw [structuralOccurrenceResidualAtom, hconstantFalse]
      simp only [Bool.false_eq_true, ↓reduceIte,
        evaluateStructuralGF2_finParity,
        evaluateStructuralGF2_variable,
        occurrenceExactChildAssignment_pair]
      rw [occurrenceExactChildren_parity_eq]
      unfold occurrenceResidualVariable residualVariable
        SupportedNormalizedGate.eval
      rw [hresidualGate]
      cases (occurrences.get index).gate.eval input <;> rfl
  | true =>
      have hconstantTrue : constant index = true :=
        hconstant.trans hresidualConstant
      have hresidualGate :
          residualConstant (occurrences.get index).gate live input = true := by
        simpa [occurrenceResidualConstant] using hresidualConstant
      have hgate :
          (occurrences.get index).gate.eval input = true :=
        residualConstant_implies_gate (occurrences.get index).gate live input
          hresidualGate
      rw [structuralOccurrenceResidualAtom]
      simp only [hconstantTrue, ↓reduceIte,
        evaluateStructuralGF2_zero]
      unfold occurrenceResidualVariable residualVariable
      rw [hresidualGate, hgate]
      rfl

/-- Total source-code lowering used by structural substitution. -/
def structuralOccurrenceResidualAtomOfCode
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (code : ℕ) : StructuralGF2Polynomial :=
  if hcode : code < occurrences.length then
    structuralOccurrenceResidualAtom algorithm occurrences constant
      ⟨code, hcode⟩
  else
    structuralGF2Zero

/-- The unique exact-child expansion of a canonical structural row. -/
def structuralOccurrenceExactPolynomial
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (constant : Fin occurrences.length → Bool)
    (polynomial : StructuralGF2Polynomial) : StructuralGF2Polynomial :=
  structuralGF2Substitute
    (structuralOccurrenceResidualAtomOfCode algorithm occurrences constant)
    polynomial

@[simp] theorem evaluateStructuralOccurrenceExactPolynomial
    {q : ℕ} (algorithm : DecompositionAlgorithm)
    (occurrences : List (SupportedNormalizedGate q))
    (live : Finset (Fin q)) (input : BitInput q)
    (constant : Fin occurrences.length → Bool)
    (hconstant : ∀ index,
      constant index =
        occurrenceResidualConstant occurrences live input index)
    (polynomial : StructuralGF2Polynomial) :
    evaluateStructuralGF2
        (occurrenceExactChildAssignment algorithm occurrences input)
        (structuralOccurrenceExactPolynomial algorithm occurrences
          constant polynomial) =
      evaluateStructuralGF2
        (encodedFiniteBooleanAssignment fun index =>
          occurrenceResidualVariable occurrences live input index)
        polynomial := by
  rw [structuralOccurrenceExactPolynomial,
    evaluateStructuralGF2_substitute]
  congr 1
  funext code
  by_cases hcode : code < occurrences.length
  · simpa [structuralOccurrenceResidualAtomOfCode,
      encodedFiniteBooleanAssignment, hcode] using
      evaluateStructuralOccurrenceResidualAtom algorithm occurrences live input
        constant ⟨code, hcode⟩ (hconstant ⟨code, hcode⟩)
  · simp [structuralOccurrenceResidualAtomOfCode,
      encodedFiniteBooleanAssignment, hcode]

theorem actual_children_bound {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (i : Fin gs.length) :
    (occurrenceExactChildren a gs i).length ≤
      a.coefficient*(q+(CompilerSemantics.nonStrictAsStrict (gs.get i).gate).encodingBits+1)^a.degree :=
  RepairOrdinary.DecompositionSource.children_bound a ⟨q,_⟩

theorem residualAtom_length {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (constant : Fin gs.length → Bool)
    (i : Fin gs.length) :
    (structuralOccurrenceResidualAtom a gs constant i).length ≤ (occurrenceExactChildren a gs i).length := by
  unfold structuralOccurrenceResidualAtom
  split
  · simp [structuralGF2Zero]
  · rw [parity_length]
    simp [structuralGF2Variable]

theorem residualAtom_degree {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (constant : Fin gs.length → Bool) (code : ℕ) :
    RawMonomialDegreeAtMost 1 (structuralOccurrenceResidualAtomOfCode a gs constant code) := by
  unfold structuralOccurrenceResidualAtomOfCode
  split
  · unfold structuralOccurrenceResidualAtom
    split
    · exact rawDegree_zero _
    · exact rawDegree_parity _ (fun i => rawDegree_variable _)
  · exact rawDegree_zero _

theorem exact_degree {q d : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (constant : Fin gs.length → Bool)
    (P : StructuralGF2Polynomial) (hP : RawMonomialDegreeAtMost d P) :
    RawMonomialDegreeAtMost d (structuralOccurrenceExactPolynomial a gs constant P) :=
  rawDegree_substitute _ (residualAtom_degree a gs constant) P hP

theorem exact_digit_fit {q : ℕ} (a : DecompositionAlgorithm)
    (gs : List (SupportedNormalizedGate q)) (constant : Fin gs.length → Bool)
    (E childBits d : ℕ) (P : StructuralGF2Polynomial)
    (hcount : P.length ≤ 2^E) (hdegree : RawMonomialDegreeAtMost d P)
    (hchildren : ∀ i, (occurrenceExactChildren a gs i).length ≤ 2^childBits) :
    (structuralOccurrenceExactPolynomial a gs constant P).length < 2^(E+childBits*d+1) := by
  apply RepairOrdinary.CloseoutRowsRawOccurrenceBound.digit_fit _ E childBits d _ P hcount hdegree
  intro code
  unfold structuralOccurrenceResidualAtomOfCode
  split
  · exact (residualAtom_length a gs constant _).trans (hchildren _)
  · simp [structuralGF2Zero]

end
end NearCubicWires.RepairSource.CloseoutRawRows
