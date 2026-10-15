import Proof.CaseAnalysis.RawRowsRecurrence

/-! The paper's existing raw list recurrence, applied to the current GF2
constructors. Reuses the mathematical recurrence from ParityCapFirstProofs
without its obsolete executor imports or mode-specific wrappers. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierListPolynomial SupplierListSchedule
open SupplierToeplitz SupplierToeplitzCore SupplierWalkBridge
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def RawMonomialDegreeAtMost
    (degree : ℕ) (polynomial : StructuralGF2Polynomial) : Prop :=
  ∀ monomial ∈ polynomial, monomial.length ≤ degree

theorem rawDegree_zero (degree : ℕ) :
    RawMonomialDegreeAtMost degree structuralGF2Zero := by
  intro monomial hmonomial
  simp [structuralGF2Zero] at hmonomial

theorem rawDegree_scale
    {degree : ℕ} (coefficient : ZMod 2)
    {polynomial : StructuralGF2Polynomial}
    (hdegree : RawMonomialDegreeAtMost degree polynomial) :
    RawMonomialDegreeAtMost degree
      (structuralGF2Scale coefficient polynomial) := by
  intro monomial hmonomial
  by_cases hzero : coefficient = 0
  · simp [structuralGF2Scale, hzero] at hmonomial
  · exact hdegree monomial (by
      simpa [structuralGF2Scale, hzero] using hmonomial)

theorem rawDegree_sum
    {degree : ℕ} {polynomials : List StructuralGF2Polynomial}
    (hpolynomials : ∀ polynomial ∈ polynomials,
      RawMonomialDegreeAtMost degree polynomial) :
    RawMonomialDegreeAtMost degree (structuralGF2Sum polynomials) := by
  intro monomial hmonomial
  unfold structuralGF2Sum at hmonomial
  obtain ⟨polynomial, hpolynomial, hmonomial⟩ :=
    List.mem_flatten.mp hmonomial
  exact hpolynomials polynomial hpolynomial monomial hmonomial

theorem rawDegree_mul
    {leftDegree rightDegree : ℕ}
    {left right : StructuralGF2Polynomial}
    (hleft : RawMonomialDegreeAtMost leftDegree left)
    (hright : RawMonomialDegreeAtMost rightDegree right) :
    RawMonomialDegreeAtMost (leftDegree + rightDegree)
      (structuralGF2Mul left right) := by
  intro monomial hmonomial
  unfold structuralGF2Mul at hmonomial
  obtain ⟨leftMonomial, hleftMonomial, hrightMap⟩ :=
    List.mem_flatMap.mp hmonomial
  obtain ⟨rightMonomial, hrightMonomial, rfl⟩ :=
    List.mem_map.mp hrightMap
  rw [List.length_append]
  exact Nat.add_le_add
    (hleft leftMonomial hleftMonomial)
    (hright rightMonomial hrightMonomial)

theorem rawDegree_elementarySymmetric
    (codes : List ℕ) (degree : ℕ) :
    RawMonomialDegreeAtMost degree
      (structuralGF2ElementarySymmetric codes degree) := by
  intro monomial hmonomial
  exact (List.mem_sublistsLen.mp hmonomial).2.le

theorem rawDegree_shiftedElementarySymmetric
    (codes : List ℕ) (offset degree : ℕ) :
    RawMonomialDegreeAtMost degree
      (structuralGF2ShiftedElementarySymmetric codes offset degree) := by
  unfold structuralGF2ShiftedElementarySymmetric
  apply rawDegree_sum
  intro polynomial hpolynomial
  obtain ⟨indices, hindices, rfl⟩ := List.mem_map.mp hpolynomial
  apply rawDegree_scale
  intro monomial hmonomial
  have hraw := rawDegree_elementarySymmetric codes indices.1 monomial hmonomial
  have hsplit := List.Nat.mem_antidiagonal.mp hindices
  omega

theorem rawDegree_consecutiveWindowIndicator
    (codes : List ℕ) (offset width target : ℕ) :
    RawMonomialDegreeAtMost width
      (structuralGF2ConsecutiveWindowIndicator codes offset width target) := by
  unfold structuralGF2ConsecutiveWindowIndicator
  apply rawDegree_sum
  intro polynomial hpolynomial
  obtain ⟨degree, hdegree, rfl⟩ := List.mem_map.mp hpolynomial
  apply rawDegree_scale
  intro monomial hmonomial
  have hraw :=
    rawDegree_shiftedElementarySymmetric codes offset degree monomial hmonomial
  have hdegreeLe := List.mem_range.mp hdegree
  omega

theorem rawDegree_terminalPolynomialVector
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost terminalWindow
      (structuralTerminalPolynomialVector depth population terminalWindow
        candidate) := by
  unfold structuralTerminalPolynomialVector structuralTerminalWindowPolynomial
  exact rawDegree_consecutiveWindowIndicator _ 0 terminalWindow candidate.val

theorem rawDegree_deltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (parent child : Fin (population + 1)) :
    RawMonomialDegreeAtMost (2 * window level)
      (structuralDeltaFactor label seed window level parent child) := by
  unfold structuralDeltaFactor
  dsimp only
  split
  · exact rawDegree_zero _
  · unfold structuralDeltaWindowPolynomial
    dsimp only
    exact rawDegree_consecutiveWindowIndicator _ _ _ _

theorem rawDegree_combineListLevel
    {rank depth population childDegree : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : StructuralListPolynomialVector population)
    (hchildren : ∀ child,
      RawMonomialDegreeAtMost childDegree (childPolynomials child))
    (parent : Fin (population + 1)) :
    RawMonomialDegreeAtMost (childDegree + 2 * window level)
      (structuralCombineListLevel label seed window level childPolynomials
        parent) := by
  unfold structuralCombineListLevel
  apply rawDegree_sum
  intro polynomial hpolynomial
  simp only [List.mem_ofFn] at hpolynomial
  obtain ⟨child, rfl⟩ := hpolynomial
  exact rawDegree_mul (hchildren child)
    (rawDegree_deltaFactor label seed window level parent child)

def structuralListCoordinateRawDegreeFrom
    (depth : ℕ) (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) : ℕ :=
  if hlevel : level < depth then
    structuralListCoordinateRawDegreeFrom depth window terminalWindow
        (level + 1) +
      2 * window ⟨level, hlevel⟩
  else
    terminalWindow
termination_by depth - level
decreasing_by omega

theorem rawDegree_structuralListPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost
      (structuralListCoordinateRawDegreeFrom depth window terminalWindow level)
      (structuralListPolynomialVectorFrom label seed window terminalWindow level
        candidate) := by
  rw [structuralListPolynomialVectorFrom,
    structuralListCoordinateRawDegreeFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    exact rawDegree_combineListLevel label seed window ⟨level, hlevel⟩ _
      (fun child => rawDegree_structuralListPolynomialVectorFrom label seed
        window terminalWindow (level + 1) child) candidate
  · rw [dif_neg hlevel, dif_neg hlevel]
    exact rawDegree_terminalPolynomialVector depth population terminalWindow
      candidate
termination_by depth - level
decreasing_by omega

def structuralListCoordinateRawDegree
    (depth : ℕ) (window : Fin depth → ℕ) (terminalWindow : ℕ) : ℕ :=
  structuralListCoordinateRawDegreeFrom depth window terminalWindow 0

theorem rawDegree_structuralListPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    RawMonomialDegreeAtMost
      (structuralListCoordinateRawDegree depth window terminalWindow)
      (structuralListPolynomialVector label seed window terminalWindow
        candidate) := by
  unfold structuralListCoordinateRawDegree structuralListPolynomialVector
  exact rawDegree_structuralListPolynomialVectorFrom label seed window
    terminalWindow 0 candidate

theorem structuralListCoordinateRawDegreeFrom_eq_listDegreeFrom
    {depth : ℕ} (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) :
    structuralListCoordinateRawDegreeFrom depth window terminalWindow level =
      listDegreeFrom window terminalWindow level := by
  rw [structuralListCoordinateRawDegreeFrom, listDegreeFrom]
  by_cases hlevel : level < depth
  · rw [dif_pos hlevel, dif_pos hlevel]
    rw [structuralListCoordinateRawDegreeFrom_eq_listDegreeFrom window
      terminalWindow (level + 1)]
  · rw [dif_neg hlevel, dif_neg hlevel]
termination_by depth - level
decreasing_by omega

theorem structuralListCoordinateRawDegree_eq_listDegree
    {depth : ℕ} (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    structuralListCoordinateRawDegree depth window terminalWindow =
      listDegree window terminalWindow := by
  unfold structuralListCoordinateRawDegree listDegree
  exact structuralListCoordinateRawDegreeFrom_eq_listDegreeFrom window
    terminalWindow 0

/-- Existing graded-window summation now applies to the raw emitted monomial
degree, not only to the semantic polynomial. -/
theorem canonicalStructuralRawDegree_cast_le (activeBound : ℕ) :
    let depth := canonicalGradedDepth activeBound
    let window := executableGradedWindow (depth := depth) activeBound
    (structuralListCoordinateRawDegree depth window gradedTerminalWindow : ℝ) ≤
      768 * Real.sqrt activeBound + 130 * depth := by
  dsimp only
  rw [structuralListCoordinateRawDegree_eq_listDegree]
  have hwindow :
      (executableGradedWindow
          (depth := canonicalGradedDepth activeBound) activeBound) =
        gradedWindow activeBound := by
    funext level
    exact executableGradedWindow_eq_gradedWindow activeBound level
  rw [hwindow]
  exact gradedListDegree_cast_le activeBound
    (canonicalGradedDepth activeBound)

end
end NearCubicWires.RepairSource.CloseoutRawRows
