import Proof.Wire_3_5.KWiseMoments

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Shared Finset

/-! ## Polynomial evaluation is `t`-wise uniform (S3.2) -/

section PolyEval
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The evaluation of the coefficient vector `c` at the points `β`: `(Σ_{i<t} c_i β_k^i)_k`, a linear map. -/
def evalMap (t m : ℕ) (β : Fin m → K) : (Fin t → K) →+ (Fin m → K) where
  toFun c k := ∑ i : Fin t, c i * β k ^ (i : ℕ)
  map_zero' := by funext k; simp
  map_add' c d := by funext k; simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq K] in
/-- At `m ≤ t` distinct points the evaluation map is surjective (the Vandermonde matrix is invertible). -/
theorem evalMap_surjective (t m : ℕ) (hm : m ≤ t) (β : Fin m → K) (hβ : Function.Injective β) :
    Function.Surjective (evalMap (K := K) t m β) := by
  intro y
  have hdet : (Matrix.vandermonde β).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hβ
  have hunit : IsUnit (Matrix.vandermonde β) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective (Matrix.vandermonde β).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  obtain ⟨low, hlow⟩ := (Finite.injective_iff_bijective.mp hinj).2 y
  refine ⟨fun i => if h : (i : ℕ) < m then low ⟨i, h⟩ else 0, ?_⟩
  funext k
  rw [← hlow]
  show ∑ i : Fin t, (if h : (i : ℕ) < m then low ⟨i, h⟩ else 0) * β k ^ (i : ℕ) =
    ∑ j : Fin m, Matrix.vandermonde β k j * low j
  simp only [Matrix.vandermonde_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i => (if h : i < m then low ⟨i, h⟩ else 0) * β k ^ i) t,
    ← Finset.sum_range_add_sum_Ico _ hm,
    Finset.sum_eq_zero (s := Finset.Ico m t) (fun i hi => by
      rw [dif_neg (by simp only [Finset.mem_Ico] at hi; omega), zero_mul]),
    add_zero, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dif_pos j.isLt, mul_comm]

theorem polyEvalKWise : PolyEvalKWise := by
  intro K L _ _ _ t label hinj ls hls val
  classical
  set m := ls.card
  let e : Fin m ≃ ls := ls.equivFin.symm
  let β : Fin m → K := fun k => label (e k)
  have hβ : Function.Injective β := fun a b h => e.injective (Subtype.ext (hinj h))
  set E := evalMap (K := K) t m β
  have hsurj := evalMap_surjective t m hls β hβ
  set y : Fin m → K := fun k => val (e k)
  -- the filter is the fiber of `E` over `y`
  have hfib : (Finset.univ.filter fun c : Fin t → K => ∀ l ∈ ls, ∑ i : Fin t, c i * label l ^ (i : ℕ) = val l) =
      Finset.univ.filter fun c => E c = y := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; funext k; exact h _ (e k).2
    · intro h l hl
      have := congrFun h (e.symm ⟨l, hl⟩)
      simpa [E, evalMap, β, y] using this
  rw [hfib]
  -- all fibers have the same size, and there are `|K|^m` of them
  have hall : ∀ z : Fin m → K, (Finset.univ.filter fun c => E c = z).card =
      (Finset.univ.filter fun c => E c = y).card := fun z =>
    AddMonoidHom.card_fiber_eq_of_mem_range E (hsurj z) (hsurj y)
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun c => E c) (s := (Finset.univ : Finset (Fin t → K)))
    (t := (Finset.univ : Finset (Fin m → K))) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl fun z _ => hall z, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [Finset.card_univ] at hsum
  simp only [Fintype.card_fun, Fintype.card_fin] at hsum ⊢
  rw [hsum]; ring

end PolyEval

/-! ## The product formula for at most `t` labels (S3.1) -/

section Product
variable {S L V : Type} [Fintype S] [Fintype V] [DecidableEq V] [DecidableEq L] [Nonempty V]

/-- **The `t`-wise product formula**: for a `t`-wise uniform family and at most `t` labels,
`Σ_s Π_{l∈ls} g_l(f s l) · |V|^{|ls|} = |S| · Π_{l∈ls} Σ_v g_l(v)`. -/
theorem kwise_prod_sum (t : ℕ) (f : S → L → V) (hk : KWiseUniform t f) (ls : Finset L) (hls : ls.card ≤ t)
    (g : L → V → ℝ) :
    (∑ s, ∏ l ∈ ls, g l (f s l)) * (Fintype.card V : ℝ) ^ ls.card =
      Fintype.card S * ∏ l ∈ ls, ∑ v, g l v := by
  classical
  let key : S → (ls → V) := fun s l => f s l
  have hfib : ∀ w : ls → V, ((Finset.univ.filter fun s => key s = w).card : ℝ) * (Fintype.card V : ℝ) ^ ls.card =
      Fintype.card S := by
    intro w
    let val : L → V := fun l => if h : l ∈ ls then w ⟨l, h⟩ else Classical.arbitrary V
    have h := hk ls hls val
    have heq : (Finset.univ.filter fun s => key s = w) = Finset.univ.filter fun s => ∀ l ∈ ls, f s l = val l := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, val]
      constructor
      · intro hs l hl; rw [dif_pos hl, ← hs]
      · intro hs; funext l; have := hs l l.2; rw [dif_pos l.2] at this; exact this
    rw [heq]; exact_mod_cast h
  have hsplit : ∑ s, ∏ l ∈ ls, g l (f s l) = ∑ w : ls → V, ∑ s ∈ Finset.univ.filter (fun s => key s = w),
      ∏ l : ls, g l (w l) := by
    rw [← Finset.sum_fiberwise Finset.univ key]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [← hs, ← Finset.prod_coe_sort]
  rw [hsplit]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_mul]
  have : ∀ w : ls → V, ((Finset.univ.filter fun s => key s = w).card : ℝ) * (∏ l : ls, g l (w l)) *
      (Fintype.card V : ℝ) ^ ls.card = Fintype.card S * ∏ l : ls, g l (w l) := by
    intro w; rw [mul_right_comm, hfib w]
  rw [Finset.sum_congr rfl fun w _ => this w, ← Finset.mul_sum]
  congr 1
  rw [← Finset.prod_coe_sort ls (fun l => ∑ v, g l v), Fintype.prod_sum]

end Product

/-! ## The scalar `2t`-th moment (S3.4, `filt:scalar-moment`) -/

section Moment
variable {S L V : Type} [Fintype S] [Fintype V] [DecidableEq V] [DecidableEq L] [Nonempty V]

/-- `Σ_{m≤t} binom(w,m)·m^{2t}·p^m ≤ (t+1)·t^t·(t+3wp)^t`. -/
theorem sum_choose_pow_le (t w : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ∑ m ∈ Finset.range (t + 1), (w.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m ≤
      (t + 1) * (t : ℝ) ^ t * (t + 3 * w * p) ^ t := by
  have hterm : ∀ m ∈ Finset.range (t + 1),
      (w.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m ≤ (t : ℝ) ^ t * (t + 3 * w * p) ^ t := by
    intro m hm
    have hmt : m ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hch : (w.choose m : ℝ) ≤ (w : ℝ) ^ m / m.factorial := Nat.choose_le_pow_div m w
    have hfac : (m : ℝ) ^ m / m.factorial ≤ 3 ^ m := by
      have := Real.pow_div_factorial_le_exp (m : ℝ) (by positivity) m
      calc (m : ℝ) ^ m / m.factorial ≤ Real.exp m := this
        _ = Real.exp 1 ^ m := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ 3 ^ m := pow_le_pow_left₀ (Real.exp_pos 1).le (by
            have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) m
    have hmm : (m : ℝ) ^ (2 * t) = (m : ℝ) ^ m * (m : ℝ) ^ (2 * t - m) := by
      rw [← pow_add]; congr 1; omega
    have hpow : (m : ℝ) ^ (2 * t - m) ≤ (t : ℝ) ^ (2 * t - m) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hmt) _
    have hbin : (3 * w * p) ^ m * (t : ℝ) ^ (t - m) ≤ (t + 3 * w * p) ^ t := by
      have h1 : (3 * w * p) ^ m ≤ (t + 3 * w * p) ^ m :=
        pow_le_pow_left₀ (by positivity) (by linarith [show (0 : ℝ) ≤ t by positivity]) m
      have h2 : (t : ℝ) ^ (t - m) ≤ (t + 3 * w * p) ^ (t - m) :=
        pow_le_pow_left₀ (by positivity) (by nlinarith [show (0 : ℝ) ≤ 3 * w * p by positivity]) _
      calc (3 * w * p) ^ m * (t : ℝ) ^ (t - m) ≤ (t + 3 * w * p) ^ m * (t + 3 * w * p) ^ (t - m) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (t + 3 * w * p) ^ t := by rw [← pow_add]; congr 1; omega
    calc (w.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m
        ≤ ((w : ℝ) ^ m / m.factorial) * ((m : ℝ) ^ m * (m : ℝ) ^ (2 * t - m)) * p ^ m := by
          rw [hmm]; gcongr
      _ = ((m : ℝ) ^ m / m.factorial) * ((w : ℝ) ^ m * p ^ m) * (m : ℝ) ^ (2 * t - m) := by ring
      _ ≤ 3 ^ m * ((w : ℝ) ^ m * p ^ m) * (t : ℝ) ^ (2 * t - m) := by gcongr
      _ = (3 * w * p) ^ m * (t : ℝ) ^ (t - m) * (t : ℝ) ^ t := by
          rw [mul_pow, mul_pow, show 2 * t - m = (t - m) + t by omega, pow_add]; ring
      _ ≤ (t + 3 * w * p) ^ t * (t : ℝ) ^ t := by gcongr
      _ = (t : ℝ) ^ t * (t + 3 * w * p) ^ t := by ring
  calc ∑ m ∈ Finset.range (t + 1), (w.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m
      ≤ ∑ _m ∈ Finset.range (t + 1), (t : ℝ) ^ t * (t + 3 * w * p) ^ t := Finset.sum_le_sum hterm
    _ = (t + 1) * (t : ℝ) ^ t * (t + 3 * w * p) ^ t := by simp; ring

/-- One index map's term: the product over its image with fiber multiplicities. -/
theorem prod_comp_image {n : ℕ} (A : Finset L) (F : Fin n → A) (x : L → ℝ) :
    ∏ k, x (F k : L) = ∏ l ∈ Finset.univ.image (fun k => (F k : L)), x l ^ (Finset.univ.filter fun k => (F k : L) = l).card :=
  Finset.prod_comp x (fun k => (F k : L))

theorem sum_maps_le (t : ℕ) (A : Finset L) (p : ℝ) (hp : 0 ≤ p) :
    ∑ F : Fin (2 * t) → A, (if ∀ l ∈ Finset.univ.image (fun k => (F k : L)),
          2 ≤ (Finset.univ.filter fun k => (F k : L) = l).card
        then p ^ (Finset.univ.image (fun k => (F k : L))).card else 0) ≤
      ∑ m ∈ Finset.range (t + 1), (A.card.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m := by
  set img : (Fin (2 * t) → A) → Finset L := fun F => Finset.univ.image (fun k => (F k : L))
  set G : (Fin (2 * t) → A) → ℝ := fun F => if ∀ l ∈ img F,
        2 ≤ (Finset.univ.filter fun k => (F k : L) = l).card then p ^ (img F).card else 0
  change ∑ F, G F ≤ _
  have hmaps : ∀ F ∈ (Finset.univ : Finset (Fin (2 * t) → A)), img F ∈ A.powerset := by
    intro F _
    simp only [Finset.mem_powerset, img]
    intro l hl; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl; exact (F k).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- per image `T`
  have hper : ∀ T ∈ A.powerset, ∑ F ∈ Finset.univ.filter (fun F => img F = T), G F ≤
      if T.card ≤ t then (T.card : ℝ) ^ (2 * t) * p ^ T.card else 0 := by
    intro T hT
    have hTA : T ⊆ A := Finset.mem_powerset.mp hT
    -- a nonzero term forces `|T| ≤ t`
    have hsmall : ∀ F, img F = T → G F ≠ 0 → T.card ≤ t := by
      intro F hF hG
      simp only [G] at hG
      split_ifs at hG with hall
      · have hsum := Finset.card_eq_sum_card_image (fun k => (F k : L)) (Finset.univ : Finset (Fin (2 * t)))
        simp only [Finset.card_univ, Fintype.card_fin] at hsum
        have : ∑ l ∈ img F, 2 ≤ ∑ l ∈ img F, (Finset.univ.filter fun k => (F k : L) = l).card :=
          Finset.sum_le_sum hall
        simp only [Finset.sum_const, smul_eq_mul] at this
        rw [← hF]
        change 2 * t = _ at hsum
        simp only [img] at this ⊢
        omega
      · exact absurd rfl hG
    have hGle : ∀ F, img F = T → G F ≤ if T.card ≤ t then p ^ T.card else 0 := by
      intro F hF
      by_cases hG : G F = 0
      · rw [hG]; split_ifs <;> positivity
      · rw [if_pos (hsmall F hF hG)]
        simp only [G] at hG ⊢
        split_ifs at hG ⊢ with hall
        · rw [hF]
        · exact absurd rfl hG
    -- the number of maps with image `T` is at most `|T|^{2t}`
    have hcount : ((Finset.univ.filter fun F => img F = T).card : ℝ) ≤ (T.card : ℝ) ^ (2 * t) := by
      have hsub : (Finset.univ.filter fun F => img F = T) ⊆
          Fintype.piFinset (fun _ : Fin (2 * t) => A.attach.filter (fun a : A => (a : L) ∈ T)) := by
        intro F hF
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
        simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_attach, true_and]
        intro k; rw [← hF]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
      have hcard : (A.attach.filter (fun a : A => (a : L) ∈ T)).card = T.card := by
        refine Finset.card_bij (fun (a : A) _ => (a : L)) ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_filter] at ha; exact ha.2
        · intro a _ b _ h; exact Subtype.ext h
        · intro l hl; exact ⟨⟨l, hTA hl⟩, by simp [hl], rfl⟩
      have := Finset.card_le_card hsub
      rw [Fintype.card_piFinset, Finset.prod_const, hcard, Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    calc ∑ F ∈ Finset.univ.filter (fun F => img F = T), G F
        ≤ ∑ _F ∈ Finset.univ.filter (fun F => img F = T), (if T.card ≤ t then p ^ T.card else 0) :=
          Finset.sum_le_sum fun F hF => hGle F (Finset.mem_filter.mp hF).2
      _ = ((Finset.univ.filter fun F => img F = T).card : ℝ) * (if T.card ≤ t then p ^ T.card else 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ if T.card ≤ t then (T.card : ℝ) ^ (2 * t) * p ^ T.card else 0 := by
          split_ifs
          · exact mul_le_mul_of_nonneg_right hcount (by positivity)
          · simp
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_powerset]
  have hinner : ∀ j ∈ Finset.range (A.card + 1), ∑ T ∈ Finset.powersetCard j A,
      (if T.card ≤ t then (T.card : ℝ) ^ (2 * t) * p ^ T.card else 0) =
        (A.card.choose j : ℝ) * (if j ≤ t then (j : ℝ) ^ (2 * t) * p ^ j else 0) := by
    intro j _
    rw [Finset.sum_congr rfl fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2], Finset.sum_const,
      Finset.card_powersetCard, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner]
  have hfilter : ∑ j ∈ Finset.range (A.card + 1), (A.card.choose j : ℝ) * (if j ≤ t then (j : ℝ) ^ (2 * t) * p ^ j else 0) =
      ∑ j ∈ (Finset.range (A.card + 1)).filter (· ≤ t), (A.card.choose j : ℝ) * ((j : ℝ) ^ (2 * t) * p ^ j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hfilter]
  calc ∑ j ∈ (Finset.range (A.card + 1)).filter (· ≤ t), (A.card.choose j : ℝ) * ((j : ℝ) ^ (2 * t) * p ^ j)
      ≤ ∑ j ∈ Finset.range (t + 1), (A.card.choose j : ℝ) * ((j : ℝ) ^ (2 * t) * p ^ j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega) (fun j _ _ => by positivity)
    _ = ∑ m ∈ Finset.range (t + 1), (A.card.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m :=
        Finset.sum_congr rfl fun j _ => by ring

theorem kwise_moment_sum_le (t : ℕ) (f : S → L → V) (hk : KWiseUniform (2 * t) f) (A : Finset L)
    (φ : L → V → ℝ) (hbound : ∀ l v, |φ l v| ≤ 1) (hcent : ∀ l, ∑ v, φ l v = 0) (p : ℝ) (hp : 0 ≤ p)
    (hvar : ∀ l, ∑ v, φ l v ^ 2 ≤ p * Fintype.card V) :
    ∑ s, (∑ l ∈ A, φ l (f s l)) ^ (2 * t) ≤
      Fintype.card S * ∑ m ∈ Finset.range (t + 1), (A.card.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m := by
  have hV : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  -- expand the power over index maps `F : Fin (2t) → A`
  have hexp : ∀ s, (∑ l ∈ A, φ l (f s l)) ^ (2 * t) = ∑ F : Fin (2 * t) → A, ∏ k, φ (F k) (f s (F k)) := by
    intro s
    rw [← Finset.sum_coe_sort A, Fintype.sum_pow]
  simp only [hexp]
  rw [Finset.sum_comm]
  -- each map's expectation
  have hterm : ∀ F : Fin (2 * t) → A,
      ∑ s, ∏ k, φ (F k) (f s (F k)) ≤
        Fintype.card S * (if ∀ l ∈ Finset.univ.image (fun k => (F k : L)),
            2 ≤ (Finset.univ.filter fun k => (F k : L) = l).card
          then p ^ (Finset.univ.image (fun k => (F k : L))).card else 0) := by
    intro F
    set I := Finset.univ.image (fun k => (F k : L))
    set mult : L → ℕ := fun l => (Finset.univ.filter fun k => (F k : L) = l).card
    have hI : I.card ≤ 2 * t := (Finset.card_image_le).trans (by simp)
    have hprod : ∀ s, ∏ k, φ (F k) (f s (F k)) = ∏ l ∈ I, φ l (f s l) ^ mult l := by
      intro s; exact Finset.prod_comp (fun l => φ l (f s l)) (fun k => (F k : L))
    simp only [hprod]
    have hformula := kwise_prod_sum (2 * t) f hk I hI (fun l v => φ l v ^ mult l)
    have hpow : (0 : ℝ) < (Fintype.card V : ℝ) ^ I.card := by positivity
    have heq : ∑ s, ∏ l ∈ I, φ l (f s l) ^ mult l =
        Fintype.card S * ∏ l ∈ I, ((∑ v, φ l v ^ mult l) / Fintype.card V) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, ← mul_div_assoc, eq_div_iff hpow.ne', hformula]
    rw [heq]
    have hmult_pos : ∀ l ∈ I, 1 ≤ mult l := by
      intro l hl
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.card_pos.mpr ⟨k, by simp⟩
    split_ifs with hall
    · -- every fiber has size at least two: each factor is at most `p` in absolute value
      have hfac : ∀ l ∈ I, |(∑ v, φ l v ^ mult l) / Fintype.card V| ≤ p := by
        intro l hl
        rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
        calc |∑ v, φ l v ^ mult l| ≤ ∑ v, |φ l v ^ mult l| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ v, φ l v ^ 2 := Finset.sum_le_sum fun v _ => by
              rw [abs_pow]
              have h1 := hbound l v
              have h2 : 2 ≤ mult l := hall l hl
              calc |φ l v| ^ mult l ≤ |φ l v| ^ 2 := pow_le_pow_of_le_one (abs_nonneg _) h1 h2
                _ = φ l v ^ 2 := sq_abs _
          _ ≤ p * Fintype.card V := hvar l
      have habs : |∏ l ∈ I, ((∑ v, φ l v ^ mult l) / Fintype.card V)| ≤ p ^ I.card := by
        rw [Finset.abs_prod]
        calc ∏ l ∈ I, |(∑ v, φ l v ^ mult l) / Fintype.card V| ≤ ∏ _l ∈ I, p :=
              Finset.prod_le_prod (fun l _ => abs_nonneg _) hfac
          _ = p ^ I.card := by simp
      have := le_abs_self (∏ l ∈ I, ((∑ v, φ l v ^ mult l) / Fintype.card V))
      have hS : (0 : ℝ) ≤ Fintype.card S := by positivity
      nlinarith
    · -- a fiber of size one: the centred factor vanishes
      push Not at hall
      obtain ⟨l, hl, hlt⟩ := hall
      have h1 : mult l = 1 := by have := hmult_pos l hl; simp only [mult] at this ⊢; omega
      rw [Finset.prod_eq_zero hl (by rw [h1]; simp [hcent l])]
  -- sum over index maps, grouped by the image
  calc ∑ F : Fin (2 * t) → A, ∑ s, ∏ k, φ (F k) (f s (F k))
      ≤ ∑ F : Fin (2 * t) → A, Fintype.card S * (if ∀ l ∈ Finset.univ.image (fun k => (F k : L)),
            2 ≤ (Finset.univ.filter fun k => (F k : L) = l).card
          then p ^ (Finset.univ.image (fun k => (F k : L))).card else 0) := Finset.sum_le_sum fun F _ => hterm F
    _ = Fintype.card S * ∑ F : Fin (2 * t) → A, (if ∀ l ∈ Finset.univ.image (fun k => (F k : L)),
            2 ≤ (Finset.univ.filter fun k => (F k : L) = l).card
          then p ^ (Finset.univ.image (fun k => (F k : L))).card else 0) := by rw [Finset.mul_sum]
    _ ≤ Fintype.card S * ∑ m ∈ Finset.range (t + 1), (A.card.choose m : ℝ) * (m : ℝ) ^ (2 * t) * p ^ m := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_maps_le t A p hp

/-- **The scalar `2t`-th moment, explicit** (`filt:scalar-moment`): `E_s(Σ_{l∈A}φ_l)^{2t} ≤ (t+1)·t^t·(t+3|A|p)^t`, i.e.
`‖δ‖_{2t} ≤ 4(√(t|A|p) + t)`. -/
theorem kwise_moment_le (t : ℕ) (f : S → L → V) (hk : KWiseUniform (2 * t) f) (A : Finset L)
    (φ : L → V → ℝ) (hbound : ∀ l v, |φ l v| ≤ 1) (hcent : ∀ l, ∑ v, φ l v = 0) (p : ℝ) (hp : 0 ≤ p)
    (hvar : ∀ l, ∑ v, φ l v ^ 2 ≤ p * Fintype.card V) :
    ∑ s, (∑ l ∈ A, φ l (f s l)) ^ (2 * t) ≤
      Fintype.card S * ((t + 1) * (t : ℝ) ^ t * (t + 3 * A.card * p) ^ t) :=
  (kwise_moment_sum_le t f hk A φ hbound hcent p hp hvar).trans
    (mul_le_mul_of_nonneg_left (sum_choose_pow_le t A.card p hp) (by positivity))

end Moment

end NearCubicWires.WireExponent3_5.Filters
