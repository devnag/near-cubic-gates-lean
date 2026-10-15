import Proof.Supplier.SupplierList
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Consecutive-window indicator polynomials

This module gives the explicit characteristic-two interpolation used by the
zero-advice list.  Elementary symmetric polynomials evaluate on Boolean inputs
to binomial coefficients of the Hamming weight.  A shifted Chu--Vandermonde
identity and triangular Newton interpolation therefore realize every function
on one consecutive weight window without division.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierWindow

abbrev 𝔽₂ := ZMod 2

def bitAssignment {arity : ℕ} (active : Finset (Fin arity)) :
    Fin arity → 𝔽₂ :=
  fun coordinate => if coordinate ∈ active then 1 else 0

theorem aeval_esymm_bitAssignment {arity degree : ℕ}
    (active : Finset (Fin arity)) :
    MvPolynomial.aeval (bitAssignment active)
        (MvPolynomial.esymm (Fin arity) 𝔽₂ degree) =
      (Nat.choose active.card degree : 𝔽₂) := by
  classical
  simp only [MvPolynomial.esymm, map_sum, map_prod,
    MvPolynomial.aeval_X]
  have hproduct (subset : Finset (Fin arity)) :
      (∏ coordinate ∈ subset, bitAssignment active coordinate) =
        if subset ⊆ active then 1 else 0 := by
    by_cases hsubset : subset ⊆ active
    · simp only [if_pos hsubset]
      exact Finset.prod_eq_one fun coordinate hcoordinate => by
        simp [bitAssignment, hsubset hcoordinate]
    · simp only [if_neg hsubset]
      obtain ⟨coordinate, hcoordinate, hmissing⟩ :=
        Set.not_subset.mp hsubset
      have hmissingFinset : coordinate ∉ active := by
        simpa using hmissing
      apply Finset.prod_eq_zero hcoordinate
      simp [bitAssignment, hmissingFinset]
  simp_rw [hproduct]
  rw [← Finset.sum_filter]
  have hfilter :
      (powersetCard degree (Finset.univ : Finset (Fin arity))).filter
          (· ⊆ active) =
        powersetCard degree active := by
    ext subset
    simp [and_comm]
  rw [hfilter]
  simp

/-! ## Division-free triangular interpolation -/

/-- Coefficients in the lower-triangular binomial basis.  The diagonal
coefficient is always one, so this construction works in characteristic two
without division or a field inversion. -/
def triangularCoefficient (value : ℕ → 𝔽₂) (degree : ℕ) : 𝔽₂ :=
  value degree -
    ∑ lower : Fin degree,
      (Nat.choose degree lower.val : 𝔽₂) *
        triangularCoefficient value lower.val
termination_by degree
decreasing_by
  exact lower.isLt

theorem triangularCoefficient_interpolates
    (value : ℕ → 𝔽₂) (point : ℕ) :
  ∑ degree ∈ Finset.range (point + 1),
        (Nat.choose point degree : 𝔽₂) *
          triangularCoefficient value degree =
      value point := by
  rw [Finset.sum_range_succ]
  rw [triangularCoefficient]
  have hprefix :
      (∑ degree ∈ Finset.range point,
          (Nat.choose point degree : 𝔽₂) *
            triangularCoefficient value degree) =
        ∑ lower : Fin point,
          (Nat.choose point (lower : ℕ) : 𝔽₂) *
            triangularCoefficient value (lower : ℕ) := by
    exact (Fin.sum_univ_eq_sum_range
      (fun degree =>
        (Nat.choose point degree : 𝔽₂) *
          triangularCoefficient value degree)
      point).symm
  rw [hprefix]
  simp

theorem shiftedChoose_identity
    (weight offset degree : ℕ) (hoffset : offset ≤ weight) :
    ∑ indices ∈ (antidiagonal degree : Finset (ℕ × ℕ)),
        (Nat.choose weight indices.1 : 𝔽₂) *
          ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) =
      (Nat.choose (weight - offset) degree : 𝔽₂) := by
  have hvandermonde :=
    Ring.add_choose_eq (R := ℤ)
      (r := (weight : ℤ)) (s := -(offset : ℤ))
      degree (Commute.all _ _)
  have hdifference :
      (weight : ℤ) + -(offset : ℤ) = ((weight - offset : ℕ) : ℤ) := by
    omega
  rw [hdifference, Ring.choose_natCast] at hvandermonde
  simp_rw [Ring.choose_natCast] at hvandermonde
  have hcast := congrArg (fun result : ℤ => (result : 𝔽₂))
    hvandermonde.symm
  simpa using hcast

/-- The shifted binomial basis element `choose(weight - offset, degree)`,
expanded in ordinary elementary symmetric polynomials.  Integer generalized
binomial coefficients are reduced only after Chu--Vandermonde is applied. -/
noncomputable def shiftedEsymm (arity offset degree : ℕ) :
    MvPolynomial (Fin arity) 𝔽₂ :=
  ∑ indices ∈ (antidiagonal degree : Finset (ℕ × ℕ)),
    MvPolynomial.C
        ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) *
      MvPolynomial.esymm (Fin arity) 𝔽₂ indices.1

theorem aeval_shiftedEsymm {arity offset degree : ℕ}
    (active : Finset (Fin arity)) (hoffset : offset ≤ active.card) :
    MvPolynomial.aeval (bitAssignment active)
        (shiftedEsymm arity offset degree) =
      (Nat.choose (active.card - offset) degree : 𝔽₂) := by
  classical
  unfold shiftedEsymm
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  simp_rw [aeval_esymm_bitAssignment]
  simpa [mul_comm] using
    shiftedChoose_identity active.card offset degree hoffset

/-! ## Consecutive-window indicators -/

def windowDelta (target point : ℕ) : 𝔽₂ :=
  if point = target then 1 else 0

/-- An explicit polynomial for one target weight inside
`[offset, offset + width]`.  Coefficients above `width` are never needed. -/
noncomputable def consecutiveWindowIndicator
    (arity offset width target : ℕ) :
    MvPolynomial (Fin arity) 𝔽₂ :=
  ∑ degree ∈ Finset.range (width + 1),
    MvPolynomial.C
        (triangularCoefficient (windowDelta target) degree) *
      shiftedEsymm arity offset degree

theorem aeval_consecutiveWindowIndicator
    {arity offset width target : ℕ}
    (active : Finset (Fin arity))
    (hlower : offset ≤ active.card)
    (hupper : active.card ≤ offset + width) :
    MvPolynomial.aeval (bitAssignment active)
        (consecutiveWindowIndicator arity offset width target) =
      if active.card = offset + target then 1 else 0 := by
  classical
  unfold consecutiveWindowIndicator
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  simp_rw [aeval_shiftedEsymm active hlower]
  let point := active.card - offset
  have hpoint : point ≤ width := by
    dsimp [point]
    omega
  have htruncate :
      (∑ degree ∈ Finset.range (width + 1),
          (algebraMap 𝔽₂ 𝔽₂)
              (triangularCoefficient (windowDelta target) degree) *
            (Nat.choose point degree : 𝔽₂)) =
        ∑ degree ∈ Finset.range (point + 1),
          (algebraMap 𝔽₂ 𝔽₂)
              (triangularCoefficient (windowDelta target) degree) *
            (Nat.choose point degree : 𝔽₂) := by
    symm
    apply Finset.sum_subset
    · intro degree hdegree
      simp only [Finset.mem_range] at hdegree ⊢
      omega
    · intro degree hdegreeWide hdegreeNarrow
      have hdegreeLarge : point < degree := by
        simp only [Finset.mem_range, not_lt] at hdegreeNarrow
        omega
      simp [Nat.choose_eq_zero_of_lt hdegreeLarge]
  rw [htruncate]
  have hinterpolation :=
    triangularCoefficient_interpolates (windowDelta target) point
  calc
    (∑ degree ∈ Finset.range (point + 1),
        (algebraMap 𝔽₂ 𝔽₂)
            (triangularCoefficient (windowDelta target) degree) *
          (Nat.choose point degree : 𝔽₂)) =
        windowDelta target point := by
      simpa [mul_comm] using hinterpolation
    _ = if active.card = offset + target then 1 else 0 := by
      unfold windowDelta
      dsimp [point]
      have hequivalence :
          active.card - offset = target ↔
            active.card = offset + target := by
        omega
      simp [hequivalence]

/-! ## Syntactic degree and multilinearity -/

theorem totalDegree_esymm_le (arity degree : ℕ) :
    (MvPolynomial.esymm (Fin arity) 𝔽₂ degree).totalDegree ≤ degree := by
  classical
  unfold MvPolynomial.esymm
  apply MvPolynomial.totalDegree_finsetSum_le
  intro subset hsubset
  calc
    (∏ coordinate ∈ subset,
        MvPolynomial.X coordinate :
          MvPolynomial (Fin arity) 𝔽₂).totalDegree ≤
        ∑ coordinate ∈ subset,
          (MvPolynomial.X coordinate :
            MvPolynomial (Fin arity) 𝔽₂).totalDegree :=
      MvPolynomial.totalDegree_finsetProd subset MvPolynomial.X
    _ = subset.card := by simp
    _ = degree := (Finset.mem_powersetCard.mp hsubset).2

theorem totalDegree_shiftedEsymm_le
    (arity offset degree : ℕ) :
    (shiftedEsymm arity offset degree).totalDegree ≤ degree := by
  classical
  unfold shiftedEsymm
  apply MvPolynomial.totalDegree_finsetSum_le
  intro indices hindices
  have hsum : indices.1 + indices.2 = degree :=
    List.Nat.mem_antidiagonal.mp hindices
  calc
    (MvPolynomial.C
          ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) *
        MvPolynomial.esymm (Fin arity) 𝔽₂ indices.1).totalDegree ≤
        (MvPolynomial.C
          ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) :
            MvPolynomial (Fin arity) 𝔽₂).totalDegree +
          (MvPolynomial.esymm
            (Fin arity) 𝔽₂ indices.1).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ indices.1 := by
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact totalDegree_esymm_le arity indices.1
    _ ≤ degree := by omega

theorem totalDegree_consecutiveWindowIndicator_le
    (arity offset width target : ℕ) :
    (consecutiveWindowIndicator arity offset width target).totalDegree ≤
      width := by
  classical
  unfold consecutiveWindowIndicator
  apply MvPolynomial.totalDegree_finsetSum_le
  intro degree hdegree
  have hdegreeBound : degree ≤ width := by
    simp only [Finset.mem_range] at hdegree
    omega
  calc
    (MvPolynomial.C
          (triangularCoefficient (windowDelta target) degree) *
        shiftedEsymm arity offset degree).totalDegree ≤
        (MvPolynomial.C
          (triangularCoefficient (windowDelta target) degree) :
            MvPolynomial (Fin arity) 𝔽₂).totalDegree +
          (shiftedEsymm arity offset degree).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ degree := by
      simpa using totalDegree_shiftedEsymm_le arity offset degree
    _ ≤ width := hdegreeBound

theorem degreeOf_esymm_le_one
    (arity degree : ℕ) (coordinate : Fin arity) :
    (MvPolynomial.esymm (Fin arity) 𝔽₂ degree).degreeOf coordinate ≤ 1 := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro monomial hmonomial
  rw [MvPolynomial.support_esymm] at hmonomial
  obtain ⟨subset, _hsubset, rfl⟩ := Finset.mem_image.mp hmonomial
  rw [Finset.sum_apply']
  by_cases hcoordinate : coordinate ∈ subset
  · calc
      (∑ member ∈ subset,
          (Finsupp.single member 1 : Fin arity →₀ ℕ) coordinate) =
          (Finsupp.single coordinate 1 : Fin arity →₀ ℕ) coordinate := by
        apply Finset.sum_eq_single coordinate
        · intro member _ hmember
          simp [hmember]
        · intro hmissing
          exact (hmissing hcoordinate).elim
      _ = 1 := by simp
      _ ≤ 1 := le_rfl
  · calc
      (∑ member ∈ subset,
          (Finsupp.single member 1 : Fin arity →₀ ℕ) coordinate) = 0 := by
        apply Finset.sum_eq_zero
        intro member hmember
        have hmemberNe : member ≠ coordinate := by
          intro hequal
          exact hcoordinate (hequal ▸ hmember)
        simp [hmemberNe]
      _ ≤ 1 := Nat.zero_le 1

theorem degreeOf_shiftedEsymm_le_one
    (arity offset degree : ℕ) (coordinate : Fin arity) :
    (shiftedEsymm arity offset degree).degreeOf coordinate ≤ 1 := by
  classical
  unfold shiftedEsymm
  refine (MvPolynomial.degreeOf_sum_le coordinate
    (antidiagonal degree : Finset (ℕ × ℕ))
    (fun indices =>
      MvPolynomial.C
          ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂) *
        MvPolynomial.esymm (Fin arity) 𝔽₂ indices.1)).trans ?_
  apply Finset.sup_le
  intro indices _
  exact (MvPolynomial.degreeOf_C_mul_le
    (MvPolynomial.esymm (Fin arity) 𝔽₂ indices.1)
    coordinate
    ((Ring.choose (-(offset : ℤ)) indices.2 : ℤ) : 𝔽₂)).trans
      (degreeOf_esymm_le_one arity indices.1 coordinate)

theorem degreeOf_consecutiveWindowIndicator_le_one
    (arity offset width target : ℕ) (coordinate : Fin arity) :
    (consecutiveWindowIndicator arity offset width target).degreeOf
      coordinate ≤ 1 := by
  classical
  unfold consecutiveWindowIndicator
  refine (MvPolynomial.degreeOf_sum_le coordinate
    (Finset.range (width + 1))
    (fun degree =>
      MvPolynomial.C
          (triangularCoefficient (windowDelta target) degree) *
        shiftedEsymm arity offset degree)).trans ?_
  apply Finset.sup_le
  intro degree _
  exact (MvPolynomial.degreeOf_C_mul_le
    (shiftedEsymm arity offset degree)
    coordinate
    (triangularCoefficient (windowDelta target) degree)).trans
      (degreeOf_shiftedEsymm_le_one arity offset degree coordinate)

/-- The complete `width + 1`-row window table, in canonical target order. -/
noncomputable def consecutiveWindowIndicators
    (arity offset width : ℕ) :
    Fin (width + 1) → MvPolynomial (Fin arity) 𝔽₂ :=
  fun target =>
    consecutiveWindowIndicator arity offset width target.val

theorem aeval_consecutiveWindowIndicators
    {arity offset width : ℕ}
    (active : Finset (Fin arity))
    (hlower : offset ≤ active.card)
    (hupper : active.card ≤ offset + width)
    (target : Fin (width + 1)) :
    MvPolynomial.aeval (bitAssignment active)
        (consecutiveWindowIndicators arity offset width target) =
      if active.card = offset + target.val then 1 else 0 :=
  aeval_consecutiveWindowIndicator active hlower hupper

theorem totalDegree_consecutiveWindowIndicators_le
    (arity offset width : ℕ) (target : Fin (width + 1)) :
    (consecutiveWindowIndicators arity offset width target).totalDegree ≤
      width :=
  totalDegree_consecutiveWindowIndicator_le
    arity offset width target.val

theorem degreeOf_consecutiveWindowIndicators_le_one
    (arity offset width : ℕ) (target : Fin (width + 1))
    (coordinate : Fin arity) :
    (consecutiveWindowIndicators arity offset width target).degreeOf
      coordinate ≤ 1 :=
  degreeOf_consecutiveWindowIndicator_le_one
    arity offset width target.val coordinate

/-- Elementary numeric bound underlying the `(M+1)^T` monomial ledger. -/
theorem sum_choose_le_add_one_pow (arity width : ℕ) :
    (∑ degree ∈ Finset.range (width + 1), Nat.choose arity degree) ≤
      (arity + 1) ^ width := by
  induction width with
  | zero => simp
  | succ width inductionHypothesis =>
      rw [Finset.sum_range_succ]
      calc
        (∑ degree ∈ Finset.range (width + 1),
            Nat.choose arity degree) +
              Nat.choose arity (width + 1) ≤
            (arity + 1) ^ width + arity ^ (width + 1) :=
          Nat.add_le_add inductionHypothesis
            (Nat.choose_le_pow arity (width + 1))
        _ ≤ (arity + 1) ^ width +
            arity * (arity + 1) ^ width := by
          apply Nat.add_le_add_left
          rw [pow_succ]
          calc
            arity ^ width * arity ≤
                (arity + 1) ^ width * arity :=
              Nat.mul_le_mul_right arity
                (pow_le_pow_left' (by omega) width)
            _ = arity * (arity + 1) ^ width := by
              rw [Nat.mul_comm]
        _ = (arity + 1) ^ (width + 1) := by
          rw [pow_succ]
          ring

noncomputable def squarefreeMonomial {arity : ℕ}
    (subset : Finset (Fin arity)) : Fin arity →₀ ℕ :=
  ∑ coordinate ∈ subset, Finsupp.single coordinate 1

noncomputable def boundedSquarefreeMonomials (arity width : ℕ) :
    Finset (Fin arity →₀ ℕ) :=
  (Finset.range (width + 1)).biUnion fun degree =>
    ((Finset.univ : Finset (Fin arity)).powersetCard degree).image
      squarefreeMonomial

theorem boundedSquarefreeMonomials_card_le (arity width : ℕ) :
    (boundedSquarefreeMonomials arity width).card ≤
      (arity + 1) ^ width := by
  classical
  calc
    (boundedSquarefreeMonomials arity width).card ≤
        ∑ degree ∈ Finset.range (width + 1),
          (((Finset.univ : Finset (Fin arity)).powersetCard degree).image
            squarefreeMonomial).card := by
      unfold boundedSquarefreeMonomials
      exact Finset.card_biUnion_le
    _ ≤ ∑ degree ∈ Finset.range (width + 1),
          ((Finset.univ : Finset (Fin arity)).powersetCard degree).card := by
      exact Finset.sum_le_sum fun degree _ =>
        Finset.card_image_le
    _ = ∑ degree ∈ Finset.range (width + 1),
          Nat.choose arity degree := by simp
    _ ≤ (arity + 1) ^ width :=
      sum_choose_le_add_one_pow arity width

theorem support_consecutiveWindowIndicator_subset
    (arity offset width target : ℕ) :
    (consecutiveWindowIndicator arity offset width target).support ⊆
      boundedSquarefreeMonomials arity width := by
  classical
  intro monomial hmonomial
  have hcoordinate (coordinate : Fin arity) :
      monomial coordinate ≤ 1 :=
    (MvPolynomial.monomial_le_degreeOf coordinate hmonomial).trans
      (degreeOf_consecutiveWindowIndicator_le_one
        arity offset width target coordinate)
  have hone (coordinate : Fin arity)
      (hcoordinateSupport : coordinate ∈ monomial.support) :
      monomial coordinate = 1 := by
    have hnonzero : monomial coordinate ≠ 0 :=
      Finsupp.mem_support_iff.mp hcoordinateSupport
    have hpositive : 0 < monomial coordinate :=
      Nat.pos_of_ne_zero hnonzero
    have hupper := hcoordinate coordinate
    omega
  have hcard : monomial.support.card ≤ width := by
    calc
      monomial.support.card =
          monomial.sum (fun _coordinate exponent => exponent) := by
        rw [Finsupp.sum]
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro coordinate hcoordinateSupport
        exact (hone coordinate hcoordinateSupport).symm
      _ ≤ (consecutiveWindowIndicator
            arity offset width target).totalDegree :=
        MvPolynomial.le_totalDegree hmonomial
      _ ≤ width :=
        totalDegree_consecutiveWindowIndicator_le
          arity offset width target
  have hreconstruct :
      squarefreeMonomial monomial.support = monomial := by
    unfold squarefreeMonomial
    calc
      (∑ coordinate ∈ monomial.support,
          Finsupp.single coordinate 1) =
          monomial.sum Finsupp.single := by
        rw [Finsupp.sum]
        apply Finset.sum_congr rfl
        intro coordinate hcoordinateSupport
        rw [hone coordinate hcoordinateSupport]
      _ = monomial := Finsupp.sum_single monomial
  unfold boundedSquarefreeMonomials
  apply Finset.mem_biUnion.mpr
  refine ⟨monomial.support.card, ?_, ?_⟩
  · simp [hcard]
  · apply Finset.mem_image.mpr
    refine ⟨monomial.support, ?_, hreconstruct⟩
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, rfl⟩

/-- The manuscript's exact squarefree-monomial ledger. -/
theorem consecutiveWindowIndicator_support_card_le
    (arity offset width target : ℕ) :
    (consecutiveWindowIndicator arity offset width target).support.card ≤
      (arity + 1) ^ width :=
  (Finset.card_le_card
    (support_consecutiveWindowIndicator_subset
      arity offset width target)).trans
        (boundedSquarefreeMonomials_card_le arity width)

theorem consecutiveWindowIndicators_support_card_le
    (arity offset width : ℕ) (target : Fin (width + 1)) :
    (consecutiveWindowIndicators arity offset width target).support.card ≤
      (arity + 1) ^ width :=
  consecutiveWindowIndicator_support_card_le
    arity offset width target.val

end NearCubicWires.SupplierWindow
