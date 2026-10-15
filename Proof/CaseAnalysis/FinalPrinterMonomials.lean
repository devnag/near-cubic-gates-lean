import Proof.Foundations.SupplierPrinter

set_option autoImplicit false

open Finset
open scoped BigOperators
open NearCubicWires.SupplierPrinter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrinterMonomials

section Reduction

variable {Row Column Equation : Type} [DecidableEq Equation]

/-- The Boolean value of a squarefree monomial given by its coordinate set:
true iff every exact-threshold coordinate of the support holds. -/
def supportValue (holds : Equation → Row → Column → Bool)
    (support : Finset Equation) (row : Row) (column : Column) : Bool :=
  decide (∀ equation ∈ support, holds equation row column = true)

/-- Squarefree reduction: an occurrence list evaluates exactly as its support
(on Boolean inputs \(x^2 = x\)). -/
theorem exactMonomialValue_eq_supportValue
    (holds : Equation → Row → Column → Bool)
    (monomial : List Equation) (row : Row) (column : Column) :
    exactMonomialValue holds monomial row column =
      supportValue holds monomial.toFinset row column := by
  unfold exactMonomialValue supportValue
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_toFinset]

theorem exactMonomialValue_toList
    (holds : Equation → Row → Column → Bool)
    (support : Finset Equation) (row : Row) (column : Column) :
    exactMonomialValue holds support.toList row column =
      supportValue holds support row column := by
  rw [exactMonomialValue_eq_supportValue, Finset.toList_toFinset]

/-- The supports of the given occurrence list. -/
def supports (monomials : List (List Equation)) : List (Finset Equation) :=
  monomials.map List.toFinset

/-- Cancellation over \(\mathbb F_2\): the distinct supports that occur an odd
number of times. -/
def oddSupports (monomials : List (List Equation)) : Finset (Finset Equation) :=
  (supports monomials).toFinset.filter fun support =>
    Odd ((supports monomials).count support)

/-- The canonically combined squarefree monomial list of paper.tex:2791–2792:
one representative per odd-multiplicity support.  This is the list the printer
is handed; `N_mon` is its length. -/
noncomputable def canonicalMonomials
    (monomials : List (List Equation)) : List (List Equation) :=
  (oddSupports monomials).toList.map Finset.toList

/-- The occurrence count, grouped by support with multiplicities. -/
theorem polynomialOccurrenceCount_eq_sum_count
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    polynomialOccurrenceCount holds monomials row column =
      ∑ support ∈ (supports monomials).toFinset,
        (supports monomials).count support *
          (supportValue holds support row column).toNat := by
  unfold polynomialOccurrenceCount
  have hmap :
      (monomials.map fun monomial =>
          (exactMonomialValue holds monomial row column).toNat) =
        (supports monomials).map fun support =>
          (supportValue holds support row column).toNat := by
    unfold supports
    rw [List.map_map]
    apply List.map_congr_left
    intro monomial _
    simp only [Function.comp_apply, exactMonomialValue_eq_supportValue]
  rw [hmap, Finset.sum_list_map_count]
  simp only [smul_eq_mul]

theorem polynomialOccurrenceCount_canonicalMonomials
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    polynomialOccurrenceCount holds (canonicalMonomials monomials) row column =
      ∑ support ∈ oddSupports monomials,
        (supportValue holds support row column).toNat := by
  unfold polynomialOccurrenceCount canonicalMonomials
  rw [List.map_map]
  have hcomp :
      ((fun monomial : List Equation =>
          (exactMonomialValue holds monomial row column).toNat) ∘ Finset.toList) =
        fun support : Finset Equation =>
          (supportValue holds support row column).toNat := by
    funext support
    simp only [Function.comp_apply, exactMonomialValue_toList]
  rw [hcomp, Finset.sum_map_toList]

/-- Cancellation preserves parity of the occurrence count at every point. -/
theorem polynomialOccurrenceCount_canonicalMonomials_mod_two
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    polynomialOccurrenceCount holds (canonicalMonomials monomials) row column % 2 =
      polynomialOccurrenceCount holds monomials row column % 2 := by
  rw [polynomialOccurrenceCount_canonicalMonomials,
    polynomialOccurrenceCount_eq_sum_count]
  unfold oddSupports
  rw [Finset.sum_filter, Finset.sum_nat_mod,
    Finset.sum_nat_mod (supports monomials).toFinset 2
      (fun support => (supports monomials).count support *
        (supportValue holds support row column).toNat)]
  congr 1
  apply Finset.sum_congr rfl
  intro support _
  by_cases hodd : Odd ((supports monomials).count support)
  · rw [if_pos hodd]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.mul_mod, show (2 * k + 1) % 2 = 1 by omega, one_mul, Nat.mod_mod]
  · rw [if_neg hodd]
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
    rw [hk, Nat.mul_mod, show (k + k) % 2 = 0 by omega, zero_mul, Nat.zero_mod]

theorem exactPolynomialValue_canonicalMonomials
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (row : Row) (column : Column) :
    exactPolynomialValue holds (canonicalMonomials monomials) row column =
      exactPolynomialValue holds monomials row column := by
  unfold exactPolynomialValue
  apply decide_eq_decide.mpr
  rw [Nat.odd_iff, Nat.odd_iff,
    polynomialOccurrenceCount_canonicalMonomials_mod_two]

/-- The reduced list computes the same exact column count \(N_P(z)\)
("substitution is \(\mathbb F_2\)-linear", paper.tex:2790–2791). -/
theorem exactColumnCount_canonicalMonomials [Fintype Row]
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (column : Column) :
    exactColumnCount holds (canonicalMonomials monomials) column =
      exactColumnCount holds monomials column := by
  unfold exactColumnCount
  apply Finset.sum_congr rfl
  intro row _
  rw [exactPolynomialValue_canonicalMonomials]

end Reduction

section Count

variable {Equation : Type} [DecidableEq Equation]

/-- Every odd-multiplicity support is a subset of the pool of size at most `d`. -/
theorem oddSupports_subset_biUnion_powersetCard
    (monomials : List (List Equation)) (pool : Finset Equation) (d : ℕ)
    (hpool : ∀ monomial ∈ monomials, ∀ equation ∈ monomial, equation ∈ pool)
    (hdegree : ∀ monomial ∈ monomials, monomial.toFinset.card ≤ d) :
    oddSupports monomials ⊆
      (Finset.range (d + 1)).biUnion fun j => pool.powersetCard j := by
  intro support hsupport
  unfold oddSupports at hsupport
  obtain ⟨hmember, -⟩ := Finset.mem_filter.mp hsupport
  unfold supports at hmember
  obtain ⟨monomial, hmonomial, rfl⟩ :=
    List.mem_map.mp (List.mem_toFinset.mp hmember)
  rw [Finset.mem_biUnion]
  refine ⟨monomial.toFinset.card,
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hdegree monomial hmonomial)), ?_⟩
  rw [Finset.mem_powersetCard]
  exact ⟨fun equation hequation =>
    hpool monomial hmonomial equation (List.mem_toFinset.mp hequation), rfl⟩

/-- `∑_{j≤d} B^j ≤ (B+1)^d`, by induction on `d`. -/
theorem sum_pow_le_succ_pow (B d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), B ^ j ≤ (B + 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hpow : B ^ (d + 1) ≤ (B + 1) ^ d * B := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right B (Nat.pow_le_pow_left (Nat.le_succ B) d)
      calc (∑ j ∈ Finset.range (d + 1), B ^ j) + B ^ (d + 1)
          ≤ (B + 1) ^ d + (B + 1) ^ d * B := Nat.add_le_add ih hpow
        _ = (B + 1) ^ (d + 1) := by ring

/-- The paper's second inequality: `∑_{j=0}^d C(B,j) ≤ (B+1)^d` (paper.tex:2795–2800). -/
theorem sum_choose_le_succ_pow (B d : ℕ) :
    ∑ j ∈ Finset.range (d + 1), B.choose j ≤ (B + 1) ^ d :=
  calc ∑ j ∈ Finset.range (d + 1), B.choose j
      ≤ ∑ j ∈ Finset.range (d + 1), B ^ j :=
        Finset.sum_le_sum fun j _ => Nat.choose_le_pow B j
    _ ≤ (B + 1) ^ d := sum_pow_le_succ_pow B d

/-- The paper's first inequality: `N_mon ≤ ∑_{j=0}^d C(B,j)` (paper.tex:2795–2798). -/
theorem canonicalMonomials_length_le_sum_choose
    (monomials : List (List Equation)) (pool : Finset Equation) (d : ℕ)
    (hpool : ∀ monomial ∈ monomials, ∀ equation ∈ monomial, equation ∈ pool)
    (hdegree : ∀ monomial ∈ monomials, monomial.toFinset.card ≤ d) :
    (canonicalMonomials monomials).length ≤
      ∑ j ∈ Finset.range (d + 1), pool.card.choose j := by
  unfold canonicalMonomials
  rw [List.length_map, Finset.length_toList]
  calc (oddSupports monomials).card
      ≤ ((Finset.range (d + 1)).biUnion fun j => pool.powersetCard j).card :=
        Finset.card_le_card
          (oddSupports_subset_biUnion_powersetCard monomials pool d hpool hdegree)
    _ ≤ ∑ j ∈ Finset.range (d + 1), (pool.powersetCard j).card :=
        Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (d + 1), pool.card.choose j := by
        simp only [Finset.card_powersetCard]

theorem canonicalMonomials_length_le
    (monomials : List (List Equation)) (pool : Finset Equation) (d : ℕ)
    (hpool : ∀ monomial ∈ monomials, ∀ equation ∈ monomial, equation ∈ pool)
    (hdegree : ∀ monomial ∈ monomials, monomial.toFinset.card ≤ d) :
    (canonicalMonomials monomials).length ≤ (pool.card + 1) ^ d :=
  (canonicalMonomials_length_le_sum_choose monomials pool d hpool hdegree).trans
    (sum_choose_le_succ_pow pool.card d)

/-- Every canonical monomial is squarefree. -/
theorem canonicalMonomials_nodup (monomials : List (List Equation)) :
    ∀ monomial ∈ canonicalMonomials monomials, monomial.Nodup := by
  intro monomial hmonomial
  unfold canonicalMonomials at hmonomial
  obtain ⟨support, -, rfl⟩ := List.mem_map.mp hmonomial
  exact Finset.nodup_toList support

/-- Every canonical monomial is drawn from the pool. -/
theorem canonicalMonomials_mem_pool
    (monomials : List (List Equation)) (pool : Finset Equation)
    (hpool : ∀ monomial ∈ monomials, ∀ equation ∈ monomial, equation ∈ pool) :
    ∀ monomial ∈ canonicalMonomials monomials, ∀ equation ∈ monomial,
      equation ∈ pool := by
  intro monomial hmonomial equation hequation
  unfold canonicalMonomials at hmonomial
  obtain ⟨support, hsupport, rfl⟩ := List.mem_map.mp hmonomial
  rw [Finset.mem_toList] at hsupport
  unfold oddSupports at hsupport
  obtain ⟨hmember, -⟩ := Finset.mem_filter.mp hsupport
  unfold supports at hmember
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp (List.mem_toFinset.mp hmember)
  rw [Finset.mem_toList, List.mem_toFinset] at hequation
  exact hpool source hsource equation hequation

/-- Degree is preserved ("substitution … preserves degree", paper.tex:2790–2791):
every canonical monomial has at most `d` coordinates. -/
theorem canonicalMonomials_length_le_degree
    (monomials : List (List Equation)) (d : ℕ)
    (hdegree : ∀ monomial ∈ monomials, monomial.toFinset.card ≤ d) :
    ∀ monomial ∈ canonicalMonomials monomials, monomial.length ≤ d := by
  intro monomial hmonomial
  unfold canonicalMonomials at hmonomial
  obtain ⟨support, hsupport, rfl⟩ := List.mem_map.mp hmonomial
  rw [Finset.mem_toList] at hsupport
  unfold oddSupports at hsupport
  obtain ⟨hmember, -⟩ := Finset.mem_filter.mp hsupport
  unfold supports at hmember
  obtain ⟨source, hsource, rfl⟩ :=
    List.mem_map.mp (List.mem_toFinset.mp hmember)
  rw [Finset.length_toList]
  exact hdegree source hsource

end Count

section Main

variable {Row Column Equation : Type} [Fintype Row] [DecidableEq Equation]

/-- **S3a (thm:batch, paper.tex:2790–2800).**  Squarefree reduction and
cancellation of the row polynomial produce ONE list `canonicalMonomials monomials`
that (i) computes the same exact column count \(N_P(z)\) for every residual
column, and (ii) has at most \((B+1)^d\) monomials, where `B = pool.card` is the
number of distinct exact-threshold coordinates and `d` the degree. -/
theorem monomialCount_le
    (holds : Equation → Row → Column → Bool)
    (monomials : List (List Equation)) (pool : Finset Equation) (d : ℕ)
    (hpool : ∀ monomial ∈ monomials, ∀ equation ∈ monomial, equation ∈ pool)
    (hdegree : ∀ monomial ∈ monomials, monomial.toFinset.card ≤ d) :
    (∀ column : Column,
        exactColumnCount holds (canonicalMonomials monomials) column =
          exactColumnCount holds monomials column) ∧
      (canonicalMonomials monomials).length ≤ (pool.card + 1) ^ d :=
  ⟨fun column => exactColumnCount_canonicalMonomials holds monomials column,
    canonicalMonomials_length_le monomials pool d hpool hdegree⟩

end Main

end NearCubicWires.RepairSource.CloseoutFinal.C10PrinterMonomials
