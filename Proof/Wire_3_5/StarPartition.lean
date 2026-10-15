import Proof.Wire_3_5.Shared.StarPartition
import Proof.Wire_3_5.StarPopulation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires Finset

theorem fin2_add_self (a : Fin 2) : a + a = 0 := by fin_cases a <;> rfl

theorem syndromeVec_add_self {s : ℕ} (d : SyndromeVec s) : d + d = 0 :=
  funext fun t => fin2_add_self (d t)

theorem syndromeVec_add_eq_zero {s : ℕ} {d e : SyndromeVec s} : d + e = 0 ↔ d = e := by
  constructor
  · intro h
    have := congrArg (· + e) h
    simpa [add_assoc, syndromeVec_add_self] using this
  · rintro rfl; exact syndromeVec_add_self d

theorem finFunctionFinEquiv_zero {s : ℕ} : (finFunctionFinEquiv (0 : SyndromeVec s)).val = 0 := by
  rw [finFunctionFinEquiv_apply]; simp

namespace StarParams
variable (P : StarParams)

/-- The block of one error choice: `0` or a unit vector `e_i`. -/
def errBits (e : Option (Fin P.b)) : Fin P.b → Bool := fun i => decide (e = some i)

theorem syndrome_xor (y y' : Fin P.b → Bool) :
    P.syndrome (fun i => xor (y i) (y' i)) = P.syndrome y + P.syndrome y' := by
  unfold syndrome
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  by_cases h1 : y i <;> by_cases h2 : y' i <;> simp [h1, h2, syndromeVec_add_self]

theorem syndrome_errBits_none : P.syndrome (P.errBits none) = 0 := by
  simp [syndrome, errBits]

theorem syndrome_errBits_some (i : Fin P.b) : P.syndrome (P.errBits (some i)) = P.column i := by
  simp [syndrome, errBits]

theorem finFunctionFinEquiv_column (i : Fin P.b) :
    (finFunctionFinEquiv (P.column i)).val = i.val + 1 := by
  simp [column]

theorem column_ne_zero (i : Fin P.b) : P.column i ≠ 0 := by
  intro h
  have := P.finFunctionFinEquiv_column i
  rw [h, finFunctionFinEquiv_zero] at this
  omega

/-- A nonzero syndrome is the column of the coordinate `(its code) − 1`. -/
theorem column_index {d : SyndromeVec P.s} (hd : d ≠ 0) (h : (finFunctionFinEquiv d).val - 1 < P.b) :
    P.column ⟨(finFunctionFinEquiv d).val - 1, h⟩ = d := by
  have hpos : (finFunctionFinEquiv d).val ≠ 0 := by
    intro h0
    apply hd
    apply finFunctionFinEquiv.injective
    apply Fin.ext
    rw [h0, finFunctionFinEquiv_zero]
  unfold column
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only
  omega

theorem syndrome_errorOf (σ : SyndromeVec P.s) (y : Fin P.b → Bool) :
    P.syndrome (fun i => xor (y i) (P.errBits (P.errorOf σ y) i)) = σ := by
  rw [syndrome_xor]
  unfold errorOf
  split_ifs with h
  · rw [syndrome_errBits_none, add_zero]; exact syndromeVec_add_eq_zero.mp h
  · rw [syndrome_errBits_some, column_index P h]
    rw [← add_assoc, syndromeVec_add_self, zero_add]

theorem errorOf_eq_none {σ : SyndromeVec P.s} {y : Fin P.b → Bool} (h : P.syndrome y + σ = 0) :
    P.errorOf σ y = none := by
  unfold errorOf; rw [if_pos h]

theorem errorOf_eq_some {σ : SyndromeVec P.s} {y : Fin P.b → Bool} {i : Fin P.b}
    (h : P.syndrome y + σ = P.column i) : P.errorOf σ y = some i := by
  unfold errorOf
  rw [if_neg (by rw [h]; exact P.column_ne_zero i)]
  congr 1
  apply Fin.ext
  show (finFunctionFinEquiv (P.syndrome y + σ)).val - 1 = i.val
  rw [h, P.finFunctionFinEquiv_column]; omega

theorem errorOf_unique {σ : SyndromeVec P.s} {c : Fin P.b → Bool} (hc : P.syndrome c = σ)
    (e : Option (Fin P.b)) : P.errorOf σ (fun i => xor (c i) (P.errBits e i)) = e := by
  have hs : P.syndrome (fun i => xor (c i) (P.errBits e i)) + σ = P.syndrome (P.errBits e) := by
    rw [syndrome_xor, hc, add_comm σ, add_assoc, syndromeVec_add_self, add_zero]
  cases e with
  | none => exact P.errorOf_eq_none (hs.trans P.syndrome_errBits_none)
  | some i => exact P.errorOf_eq_some (hs.trans (P.syndrome_errBits_some i))

def blockEquiv (σ : SyndromeVec P.s) :
    (Fin P.b → Bool) ≃ {c : Fin P.b → Bool // P.syndrome c = σ} × Option (Fin P.b) where
  toFun y := (⟨fun i => xor (y i) (P.errBits (P.errorOf σ y) i), P.syndrome_errorOf σ y⟩, P.errorOf σ y)
  invFun p := fun i => xor (p.1.1 i) (P.errBits p.2 i)
  left_inv y := by funext i; simp
  right_inv p := by
    obtain ⟨⟨c, hc⟩, e⟩ := p
    have he := P.errorOf_unique hc e
    simp only [he, Prod.mk.injEq, and_true]
    apply Subtype.ext; funext i; simp

theorem card_option_b : Fintype.card (Option (Fin P.b)) = 2 ^ P.s := by
  simp [Fintype.card_option, P.b_succ]

theorem s_le_b : P.s ≤ P.b := by
  have := Nat.lt_two_pow_self (n := P.s); have := P.b_succ; omega

theorem card_coset (σ : SyndromeVec P.s) :
    Fintype.card {c : Fin P.b → Bool // P.syndrome c = σ} = 2 ^ (P.b - P.s) := by
  have h := Fintype.card_congr (P.blockEquiv σ)
  rw [Fintype.card_prod, P.card_option_b] at h
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hb : 2 ^ P.b = 2 ^ (P.b - P.s) * 2 ^ P.s := by rw [← pow_add, Nat.sub_add_cancel P.s_le_b]
  rw [hb] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h).symm

/-! ## The blocks of an input -/

theorem block_cases (J : Fin P.r) : (∃ j, J = P.leftBlock j) ∨ (∃ j, J = P.rightBlock j) := by
  have hr := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  by_cases h : J.val < P.r / 2
  · exact Or.inl ⟨⟨J.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨J.val - P.r / 2, by have := J.isLt; omega⟩, Fin.ext (by simp [rightBlock]; omega)⟩

theorem leftBlock_ne_rightBlock (j j' : Fin (P.r / 2)) : P.leftBlock j ≠ P.rightBlock j' := by
  intro h; have := congrArg Fin.val h; simp [leftBlock, rightBlock] at this; omega

theorem errorVector_blockCoord (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) (J : Fin P.r) (i : Fin P.b) :
    P.errorVector side e (P.blockCoord J i) = decide (∃ j, side j = J ∧ e j = some i) := by
  simp only [errorVector]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, i', he, hc⟩
    obtain ⟨hJ, hi⟩ := P.blockCoord_inj hc
    exact ⟨j, hJ, hi ▸ he⟩
  · rintro ⟨j, hJ, he⟩
    exact ⟨j, i, he, hJ ▸ rfl⟩

theorem blockBits_left_left (u : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.leftBlock u) (P.leftBlock j) = P.errBits (u j) := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j', hj, he⟩; rw [P.leftBlock_inj hj] at he; exact he
  · intro h; exact ⟨j, rfl, h⟩

theorem blockBits_left_right (u : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.leftBlock u) (P.rightBlock j) = P.errBits none := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord, reduceCtorEq, decide_false]
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  intro j' hj; exact absurd hj (P.leftBlock_ne_rightBlock j' j)

theorem blockBits_right_right (v : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.rightBlock v) (P.rightBlock j) = P.errBits (v j) := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j', hj, he⟩; rw [P.rightBlock_inj hj] at he; exact he
  · intro h; exact ⟨j, rfl, h⟩

theorem blockBits_right_left (v : P.Errors) (j : Fin (P.r / 2)) :
    P.blockBits (P.errorVector P.rightBlock v) (P.leftBlock j) = P.errBits none := by
  funext i
  simp only [blockBits, errBits, errorVector_blockCoord, reduceCtorEq, decide_false]
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  intro j' hj; exact absurd hj.symm (P.leftBlock_ne_rightBlock j j')

theorem blockBits_xorInput (x y : BitInput P.n) (J : Fin P.r) :
    P.blockBits (xorInput x y) J = fun i => xor (P.blockBits x J i) (P.blockBits y J i) := rfl

theorem errBits_none_apply (i : Fin P.b) : P.errBits none i = false := by simp [errBits]

theorem center_isCenter (σ : P.Translation) (x : BitInput P.n) : P.IsCenter σ (P.center σ x) := by
  intro J
  rcases P.block_cases J with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h : P.blockBits (P.center σ x) (P.leftBlock j) =
        fun i => xor (P.blockBits x (P.leftBlock j) i)
          (P.errBits (P.errorOf (σ (P.leftBlock j)) (P.blockBits x (P.leftBlock j))) i) := by
      funext i
      simp only [center, blockBits_xorInput, blockBits_left_left, blockBits_right_left, errBits_none_apply,
        Bool.xor_false, leftErrors]
    rw [h]; exact P.syndrome_errorOf _ _
  · have h : P.blockBits (P.center σ x) (P.rightBlock j) =
        fun i => xor (P.blockBits x (P.rightBlock j) i)
          (P.errBits (P.errorOf (σ (P.rightBlock j)) (P.blockBits x (P.rightBlock j))) i) := by
      funext i
      simp only [center, blockBits_xorInput, blockBits_left_right, blockBits_right_right, errBits_none_apply,
        Bool.xor_false, rightErrors]
    rw [h]; exact P.syndrome_errorOf _ _

theorem xorInput_cancel (x a b : BitInput P.n) :
    xorInput (xorInput (xorInput (xorInput x a) b) a) b = x := by
  funext i; simp only [xorInput]; cases x i <;> cases a i <;> cases b i <;> rfl

theorem point_center (σ : P.Translation) (x : BitInput P.n) :
    P.point (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) = x :=
  P.xorInput_cancel _ _ _

theorem leftErrors_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.leftErrors σ (P.point c u v) = u := by
  funext j
  have h : P.blockBits (P.point c u v) (P.leftBlock j) =
      fun i => xor (P.blockBits c (P.leftBlock j) i) (P.errBits (u j) i) := by
    funext i
    simp only [point, blockBits_xorInput, blockBits_left_left, blockBits_right_left, errBits_none_apply,
      Bool.xor_false]
  simp only [leftErrors]; rw [h]; exact P.errorOf_unique (hc _) _

theorem rightErrors_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.rightErrors σ (P.point c u v) = v := by
  funext j
  have h : P.blockBits (P.point c u v) (P.rightBlock j) =
      fun i => xor (P.blockBits c (P.rightBlock j) i) (P.errBits (v j) i) := by
    funext i
    simp only [point, blockBits_xorInput, blockBits_left_right, blockBits_right_right, errBits_none_apply,
      Bool.xor_false]
  simp only [rightErrors]; rw [h]; exact P.errorOf_unique (hc _) _

theorem center_point {σ : P.Translation} {c : BitInput P.n} (hc : P.IsCenter σ c) (u v : P.Errors) :
    P.center σ (P.point c u v) = c := by
  unfold center
  rw [P.leftErrors_point hc, P.rightErrors_point hc]
  exact P.xorInput_cancel _ _ _

def decomposition (σ : P.Translation) : BitInput P.n ≃ {c // P.IsCenter σ c} × P.Errors × P.Errors where
  toFun x := (⟨P.center σ x, P.center_isCenter σ x⟩, P.leftErrors σ x, P.rightErrors σ x)
  invFun p := P.point p.1.1 p.2.1 p.2.2
  left_inv x := P.point_center σ x
  right_inv p := by
    obtain ⟨⟨c, hc⟩, u, v⟩ := p
    simp only [P.center_point hc, P.leftErrors_point hc, P.rightErrors_point hc]

theorem k_le_n : P.k ≤ P.n := by
  unfold k
  calc P.r * P.s ≤ P.r * P.b := Nat.mul_le_mul_left _ P.s_le_b
    _ ≤ P.n := P.r_mul_b_le

theorem r_half_add : P.r / 2 + P.r / 2 = P.r := by have := P.r_even; obtain ⟨m, hm⟩ := this; omega

theorem card_translation : Fintype.card P.Translation = 2 ^ P.k := by
  simp only [Translation, SyndromeVec, Fintype.card_fun, Fintype.card_fin, k]
  rw [← pow_mul, mul_comm]

theorem card_cell : Fintype.card (P.Errors × P.Errors) = 2 ^ P.k := by
  simp only [Fintype.card_prod, StarParams.Errors, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, P.b_succ]
  rw [← pow_mul, ← pow_add, ← mul_add, P.r_half_add, k, mul_comm]

theorem card_centers (σ : P.Translation) : Fintype.card {c // P.IsCenter σ c} = 2 ^ (P.n - P.k) := by
  have h := Fintype.card_congr (P.decomposition σ)
  rw [Fintype.card_prod, P.card_cell] at h
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hn : 2 ^ P.n = 2 ^ (P.n - P.k) * 2 ^ P.k := by rw [← pow_add, Nat.sub_add_cancel P.k_le_n]
  rw [hn] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h).symm

theorem sum_eq_sum_cells {M : Type} [AddCommMonoid M] (σ : P.Translation) (f : BitInput P.n → M) :
    ∑ x, f x = ∑ c ∈ univ.filter (P.IsCenter σ), ∑ u : P.Errors, ∑ v : P.Errors, f (P.point c u v) := by
  rw [← Equiv.sum_comp (P.decomposition σ).symm, Fintype.sum_prod_type,
    Finset.sum_subtype (p := P.IsCenter σ) (univ.filter (P.IsCenter σ)) (fun c => by simp)
      (fun c => ∑ u : P.Errors, ∑ v : P.Errors, f (P.point c u v))]
  apply Finset.sum_congr rfl; intro a _
  rw [Fintype.sum_prod_type]; rfl

/-- The syndromes of all blocks of an input: the partition in which it is a center. -/
def syndromes (c : BitInput P.n) : P.Translation := fun j => P.syndrome (P.blockBits c j)

theorem isCenter_iff (σ : P.Translation) (c : BitInput P.n) : P.IsCenter σ c ↔ P.syndromes c = σ := by
  constructor
  · intro h; funext j; exact h j
  · intro h j; rw [← h]; rfl

/-- Every input is a center of exactly one partition, so the centers of all partitions sum to the cube. -/
theorem sum_translations_centers {M : Type} [AddCommMonoid M] (g : BitInput P.n → M) :
    ∑ σ : P.Translation, ∑ c ∈ univ.filter (P.IsCenter σ), g c = ∑ c, g c := by
  have h : ∀ σ : P.Translation, univ.filter (P.IsCenter σ) = univ.filter fun c => P.syndromes c = σ := by
    intro σ; ext c; simp [P.isCenter_iff]
  simp only [h]
  exact Finset.sum_fiberwise univ P.syndromes g

theorem sum_translations_inputs {M : Type} [AddCommMonoid M]
    (F : BitInput P.n → P.Errors → P.Errors → M) :
    ∑ σ : P.Translation, ∑ x, F (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x) =
      ∑ c, ∑ u : P.Errors, ∑ v : P.Errors, F c u v := by
  rw [← P.sum_translations_centers fun c => ∑ u : P.Errors, ∑ v : P.Errors, F c u v]
  apply Finset.sum_congr rfl; intro σ _
  rw [P.sum_eq_sum_cells σ]
  apply Finset.sum_congr rfl; intro c hc
  have hc' : P.IsCenter σ c := (Finset.mem_filter.mp hc).2
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  rw [P.center_point hc', P.leftErrors_point hc', P.rightErrors_point hc']

theorem average_translations_inputs (F : BitInput P.n → P.Errors → P.Errors → ℝ) :
    (∑ σ : P.Translation, ∑ x, F (P.center σ x) (P.leftErrors σ x) (P.rightErrors σ x)) /
        ((Fintype.card P.Translation : ℝ) * 2 ^ P.n) =
      (∑ c, ∑ u : P.Errors, ∑ v : P.Errors, F c u v) / (2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2) := by
  rw [P.sum_translations_inputs]
  have h1 : (Fintype.card P.Translation : ℝ) = 2 ^ P.k := by rw [P.card_translation]; push_cast; rfl
  have h2 : (Fintype.card P.Errors : ℝ) ^ 2 = 2 ^ P.k := by
    have := P.card_cell; rw [Fintype.card_prod] at this
    rw [sq]; exact_mod_cast this
  rw [h1, h2, mul_comm]

theorem translationAverage_mixed_le (g : NormalizedThresholdGate P.n) :
    (∑ σ : P.Translation, ∑ x, (if mixedDifference g.eval (P.center σ x)
        (P.errorVector P.leftBlock (P.leftErrors σ x)) (P.errorVector P.rightBlock (P.rightErrors σ x)) ≠ 0
        then (1 : ℝ) else 0)) / ((Fintype.card P.Translation : ℝ) * 2 ^ P.n) ≤
      4 * Real.sqrt 2 * (P.r * Real.sqrt P.r) * (gateSupport g).card / (P.n * Real.sqrt P.n) := by
  rw [P.average_translations_inputs (fun c u v => if mixedDifference g.eval c
      (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0 then (1 : ℝ) else 0)]
  have h := starPopulation_holds P g
  have hsum : (∑ c : BitInput P.n, ∑ u : P.Errors, ∑ v : P.Errors, (if mixedDifference g.eval c
      (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0 then (1 : ℝ) else 0)) =
      ((∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
        mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0).card : ℕ) : ℝ) := by
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _
    rw [Finset.card_filter]; push_cast; rfl
  rw [hsum]; exact h

def centerSide (x : Fin P.n) : Bool :=
  decide (x.val < P.r / 2 * P.b ∨ (P.r * P.b ≤ x.val ∧ x.val < P.r * P.b + (P.n - P.r * P.b + 1) / 2))

/-- Left center bits: `b − s` free bits in each of the `r/2` left blocks plus `⌈(n−rb)/2⌉` unblocked ones. -/
def leftCenterBits : ℕ := P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2

/-- Right center bits: `b − s` free bits in each of the `r/2` right blocks plus `⌊(n−rb)/2⌋` unblocked ones. -/
def rightCenterBits : ℕ := P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b) / 2

theorem centerBits_sum : P.leftCenterBits + P.rightCenterBits = P.n - P.k := by
  unfold leftCenterBits rightCenterBits k
  have h1 := P.r_mul_b_le; have h2 := P.s_le_b; have h3 := P.r_half_add
  have e1 : P.r / 2 * (P.b - P.s) + P.r / 2 * (P.b - P.s) = P.r * P.b - P.r * P.s := by
    rw [← add_mul, h3, Nat.mul_sub]
  have e2 : P.r * P.s ≤ P.r * P.b := Nat.mul_le_mul_left _ h2
  omega

theorem centerBits_balanced :
    P.rightCenterBits ≤ P.leftCenterBits ∧ P.leftCenterBits ≤ P.rightCenterBits + 1 := by
  unfold leftCenterBits rightCenterBits; omega

theorem centerSide_leftBlock (j : Fin (P.r / 2)) (i : Fin P.b) :
    P.centerSide (P.blockCoord (P.leftBlock j) i) = true := by
  simp only [centerSide, blockCoord, leftBlock, decide_eq_true_eq]
  left
  have := j.isLt; have := i.isLt
  calc j.val * P.b + i.val < (j.val + 1) * P.b := by nlinarith
    _ ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ (by omega)

theorem centerSide_rightBlock (j : Fin (P.r / 2)) (i : Fin P.b) :
    P.centerSide (P.blockCoord (P.rightBlock j) i) = false := by
  simp only [centerSide, blockCoord, rightBlock, decide_eq_false_iff_not, not_or, not_and, not_lt]
  have := j.isLt; have := i.isLt; have h3 := P.r_half_add
  refine ⟨?_, ?_⟩
  · calc P.r / 2 * P.b ≤ (P.r / 2 + j.val) * P.b := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (P.r / 2 + j.val) * P.b + i.val := Nat.le_add_right _ _
  · intro h
    exfalso
    have : (P.r / 2 + j.val) * P.b + i.val < (P.r / 2 + j.val + 1) * P.b := by nlinarith
    have : (P.r / 2 + j.val + 1) * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## Executable check (test before prove): the decomposition at `n = 8`, `r = 2` (`s = 2`, `b = 3`, `k = 4`) -/

/-- The smallest star: `n = 8`, `r = 2`. -/
def tiny : StarParams := ⟨8, 2, ⟨1, rfl⟩, le_rfl, by norm_num⟩

theorem tiny_s : tiny.s = 2 := by decide

/-- Every input of the tiny star is recovered from its decomposition, in the partition with codes `[1, 2]`. -/
theorem tiny_roundTrip : ∀ x : BitInput 8,
    tiny.point (tiny.center (tiny.translationOfCodes [1, 2]) x)
      (tiny.leftErrors (tiny.translationOfCodes [1, 2]) x) (tiny.rightErrors (tiny.translationOfCodes [1, 2]) x) = x :=
  fun x => tiny.point_center _ x

end StarParams

end NearCubicWires.WireExponent3_5.Shared
