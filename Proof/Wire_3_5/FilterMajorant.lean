import Proof.Wire_3_5.FilterKWise
import Proof.Wire_3_5.FilterGap
import Proof.Wire_3_5.ListPoly
import Proof.Wire_3_5.GFExists

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Lists Finset

/-- The parameters of `filt:majorant`: `M` coordinates per population, `A` populations, at most `B_*` ones per
population, the moment order `2t`, and the depth `J`. -/
structure MajorantParams where
  M : ℕ
  A : ℕ
  Bstar : ℕ
  t : ℕ
  J : ℕ

namespace MajorantParams
variable (P : MajorantParams)

/-- The field dimension `ℓ₀ = max(J+1, ⌈log₂M⌉, 1)`: the coordinates' labels are distinct and have `J+1` bits. -/
def ell0 : ℕ := max (P.J + 1) (Nat.clog 2 P.M)

theorem ell0_ne_zero : P.ell0 ≠ 0 := by unfold ell0; omega

theorem J_lt_ell0 : P.J < P.ell0 := by unfold ell0; omega

theorem M_le_two_pow : P.M ≤ 2 ^ P.ell0 :=
  (Nat.le_pow_clog (by norm_num) P.M).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

abbrev K : Type := GaloisField 2 P.ell0

def refMod : ℕ := GF.firstPrimitive P.ell0

theorem refCert : GF.PrimitiveCert P.refMod P.ell0 :=
  GF.firstPrimitive_cert P.ell0 (Nat.one_le_iff_ne_zero.mpr P.ell0_ne_zero)

theorem refFinite : Finite (AdjoinRoot (GF.toPoly P.refMod)) :=
  Nat.finite_of_card_ne_zero (by rw [GF.natCard_ref _ _ P.refCert.2.1]; positivity)

noncomputable def refCoord : AdjoinRoot (GF.toPoly P.refMod) ≃ₗ[ZMod 2] (Fin P.ell0 → ZMod 2) :=
  haveI := P.refFinite
  LinearEquiv.ofBijective ((GF.projK P.refMod P.ell0 P.refCert.2.1 P.ell0).toZModLinearMap 2)
    ((GF.projK_surjective P.refMod P.ell0 P.refCert.2.1 P.ell0 le_rfl).bijective_of_nat_card_le
      (by rw [GF.natCard_ref _ _ P.refCert.2.1]; simp [Nat.card_eq_fintype_card, ZMod.card]))

noncomputable def coord : P.K ≃ₗ[ZMod 2] (Fin P.ell0 → ZMod 2) :=
  letI := GF.fact_irreducible P.refMod P.ell0 P.refCert
  (GF.refAlgEquivGalois P.refMod P.ell0 P.refCert).symm.toLinearEquiv.trans P.refCoord

/-- **The labels are machine bits**: the label coordinates of the field element represented by the bit vector `a` are
the bits of `a` (the C4 machine reads labels off its representatives). -/
theorem coord_rep (a : ℕ) (ha : a < 2 ^ P.ell0) (b : Fin P.ell0) :
    letI := GF.fact_irreducible P.refMod P.ell0 P.refCert
    P.coord (GF.refAlgEquivGalois P.refMod P.ell0 P.refCert (GF.rep P.refMod a)) b = GF.bitF (a.testBit b) := by
  letI := GF.fact_irreducible P.refMod P.ell0 P.refCert
  have h : (GF.refAlgEquivGalois P.refMod P.ell0 P.refCert).symm
      (GF.refAlgEquivGalois P.refMod P.ell0 P.refCert (GF.rep P.refMod a)) = GF.rep P.refMod a :=
    AlgEquiv.symm_apply_apply _ _
  show P.refCoord ((GF.refAlgEquivGalois P.refMod P.ell0 P.refCert).symm
      (GF.refAlgEquivGalois P.refMod P.ell0 P.refCert (GF.rep P.refMod a))) b = _
  rw [h]
  exact GF.projK_rep P.refMod P.ell0 P.refCert.2.1 P.ell0 a ha b

/-- The evaluation point of coordinate `i`: the field element whose basis coordinates are the bits of `i`. -/
noncomputable def point (i : Fin P.M) : P.K := P.coord.symm fun b => if (i : ℕ).testBit b then 1 else 0

theorem point_injective : Function.Injective P.point := by
  intro i i' h
  have h2 := congrArg P.coord h
  simp only [point, LinearEquiv.apply_symm_apply] at h2
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < P.ell0
  · have := congrFun h2 ⟨b, hb⟩
    simp only at this
    cases h1 : (i : ℕ).testBit b <;> cases h3 : (i' : ℕ).testBit b <;> simp_all
  · have hle : 2 ^ P.ell0 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hi := i.isLt; have hi' := i'.isLt; have hM := P.M_le_two_pow
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

abbrev Seed : Type := Fin (2 * P.t) → P.K

/-- The hash value of coordinate `i`: the polynomial evaluated at its point. -/
noncomputable def value (h : P.Seed) (i : Fin P.M) : P.K := ∑ r : Fin (2 * P.t), h r * P.point i ^ (r : ℕ)

theorem value_kwise : KWiseUniform (2 * P.t) P.value := polyEvalKWise (2 * P.t) P.point P.point_injective

def PrefixZero (j : ℕ) (v : P.K) : Prop := ∀ b : Fin P.ell0, (b : ℕ) < j → P.coord v b = 0

noncomputable instance instDecidablePrefixZero (j : ℕ) (v : P.K) : Decidable (P.PrefixZero j v) :=
  inferInstanceAs (Decidable (∀ b : Fin P.ell0, (b : ℕ) < j → P.coord v b = 0))

/-- `#{v ∈ 𝕂 : first j coordinates vanish} = 2^{ℓ₀−j}`. -/
theorem card_prefixZero (j : ℕ) (hj : j ≤ P.ell0) :
    (Finset.univ.filter fun v : P.K => P.PrefixZero j v).card = 2 ^ (P.ell0 - j) := by
  have hbij : (Finset.univ.filter fun v : P.K => P.PrefixZero j v).card =
      (Fintype.piFinset fun b : Fin P.ell0 => if (b : ℕ) < j then ({0} : Finset (ZMod 2)) else Finset.univ).card := by
    refine Finset.card_bij (fun v _ => P.coord v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, PrefixZero] at hv
      simp only [Fintype.mem_piFinset]
      intro b; split_ifs with hb
      · simp [hv b hb]
      · exact Finset.mem_univ _
    · intro v _ v' _ h; exact P.coord.injective h
    · intro y hy
      simp only [Fintype.mem_piFinset] at hy
      refine ⟨P.coord.symm y, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, PrefixZero, LinearEquiv.apply_symm_apply]
      intro b hb; have := hy b; rw [if_pos hb] at this; simpa using this
  rw [hbij, Fintype.card_piFinset]
  have : ∀ b : Fin P.ell0, (if (b : ℕ) < j then ({0} : Finset (ZMod 2)) else Finset.univ).card =
      if (b : ℕ) < j then 1 else 2 := by
    intro b; split_ifs <;> simp [ZMod.card]
  rw [Finset.prod_congr rfl fun b _ => this b, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter fun b : Fin P.ell0 => ¬ (b : ℕ) < j) = Finset.univ.filter fun b : Fin P.ell0 => j ≤ (b : ℕ) := by
    ext b; simp
  rw [this]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin P.ell0))) (fun b => (b : ℕ) < j)
  have hlt : (Finset.univ.filter fun b : Fin P.ell0 => (b : ℕ) < j).card = j := by
    rw [Fin.card_filter_val_lt]; exact min_eq_right hj
  simp only [Finset.card_univ, Fintype.card_fin, hlt, not_lt] at hc
  omega

/-- The nested hash: coordinate `i` lies in `𝓛_j` iff the first `j` label bits of its value vanish. -/
noncomputable def inLevel (h : P.Seed) (j i : ℕ) : Bool :=
  if hi : i < P.M then decide (P.PrefixZero j (P.value h ⟨i, hi⟩)) else true

/-- The windows `W_j = 16t + 20(⌊s/2^{⌊j/2⌋}⌋ + 1)`, `s = ⌊√(tB_*)⌋ + 1`. -/
def W (j : ℕ) : ℕ := 16 * P.t + 20 * ((Nat.sqrt (P.t * P.Bstar) + 1) / 2 ^ (j / 2) + 1)

theorem W_ge (j : ℕ) : 20 ≤ P.W j := by
  have hx : 20 ≤ 20 * ((Nat.sqrt (P.t * P.Bstar) + 1) / 2 ^ (j / 2) + 1) := Nat.le_mul_of_pos_right 20 (Nat.succ_pos _)
  unfold W; omega

/-- The count lists of `list:repair` at the hash. -/
noncomputable def data (h : P.Seed) : ListData := ⟨P.M, P.J, P.W, P.inLevel h⟩

theorem inLevel_zero (h : P.Seed) (i : ℕ) : P.inLevel h 0 i = true := by
  unfold inLevel; split_ifs <;> simp [PrefixZero]

theorem inLevel_nest (h : P.Seed) (j i : ℕ) (hi : P.inLevel h (j + 1) i = true) : P.inLevel h j i = true := by
  unfold inLevel at hi ⊢
  split_ifs at hi ⊢ with hM
  · simp only [decide_eq_true_eq, PrefixZero] at hi ⊢
    intro b hb; exact hi b (by omega)
  · rfl

/-- The active coordinates of a population (`Z_i = 1`, `i < M`). -/
def active (Z : List Bool) : Finset (Fin P.M) := Finset.univ.filter fun i => Z.getD i false = true

/-- The level signs `φ_j`: `+1` on `𝓛_j ∖ 𝓛_{j+1}`, `−1` on `𝓛_{j+1}`, `0` elsewhere, so that `δ_j = Σ_{active} φ_j`. -/
noncomputable def sign (j : ℕ) (v : P.K) : ℝ :=
  (if P.PrefixZero j v ∧ ¬ P.PrefixZero (j + 1) v then 1 else 0) - (if P.PrefixZero (j + 1) v then 1 else 0)

theorem levelCount_eq (h : P.Seed) (j : ℕ) (Z : List Bool) (hZ : Z.length ≤ P.M) :
    ((P.data h).levelCount j Z : ℝ) = ∑ i ∈ P.active Z, if P.PrefixZero j (P.value h i) then 1 else 0 := by
  unfold ListData.levelCount
  simp only [data]
  rw [Finset.card_filter]
  push_cast
  unfold active
  rw [Finset.sum_filter]
  have hfin : (∑ i : Fin P.M, if Z.getD (i : ℕ) false = true then
        (if P.PrefixZero j (P.value h i) then (1 : ℝ) else 0) else 0) =
      ∑ i ∈ Finset.range P.M, (if hi : i < P.M then (if Z.getD i false = true then
        (if P.PrefixZero j (P.value h ⟨i, hi⟩) then (1 : ℝ) else 0) else 0) else 0) := by
    rw [Finset.sum_range]; exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]
  rw [hfin, ← Finset.sum_range_add_sum_Ico _ hZ, Finset.sum_eq_zero (s := Finset.Ico Z.length P.M) (fun i hi => by
    simp only [Finset.mem_Ico] at hi
    rw [dif_pos hi.2, List.getD_eq_default _ _ (by omega)]; simp), add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiM : i < P.M := by simp only [Finset.mem_range] at hi; omega
  rw [dif_pos hiM]
  simp only [inLevel, dif_pos hiM, decide_eq_true_eq, ite_and]

/-- **`δ_j = Σ_{i active} φ_j(value_i)`** (with nesting). -/
theorem levelDelta_eq (h : P.Seed) (j : ℕ) (Z : List Bool) (hZ : Z.length ≤ P.M) :
    ((P.data h).levelDelta j Z : ℝ) = ∑ i ∈ P.active Z, P.sign j (P.value h i) := by
  unfold ListData.levelDelta
  push_cast
  rw [P.levelCount_eq h j Z hZ, P.levelCount_eq h (j + 1) Z hZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold sign
  have hn : P.PrefixZero (j + 1) (P.value h i) → P.PrefixZero j (P.value h i) := fun h1 b hb => h1 b (by omega)
  by_cases h0 : P.PrefixZero j (P.value h i)
  · by_cases h1 : P.PrefixZero (j + 1) (P.value h i)
    · norm_num [h0, h1]
    · norm_num [h0, h1]
  · have h1 : ¬ P.PrefixZero (j + 1) (P.value h i) := fun h1 => h0 (hn h1)
    norm_num [h0, h1]

theorem sign_abs_le (j : ℕ) (v : P.K) : |P.sign j v| ≤ 1 := by
  unfold sign; split_ifs <;> norm_num

theorem sum_sign (j : ℕ) (hj : j + 1 ≤ P.ell0) : ∑ v : P.K, P.sign j v = 0 := by
  have h0 := P.card_prefixZero j (by omega)
  have h1 := P.card_prefixZero (j + 1) hj
  unfold sign
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  have hsplit : (Finset.univ.filter fun v : P.K => P.PrefixZero j v ∧ ¬ P.PrefixZero (j + 1) v).card +
      (Finset.univ.filter fun v : P.K => P.PrefixZero (j + 1) v).card =
      (Finset.univ.filter fun v : P.K => P.PrefixZero j v).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | h); exact h; exact fun b hb => h b (by omega)
      · intro h; by_cases h' : P.PrefixZero (j + 1) v; right; exact h'; left; exact ⟨h, h'⟩
    · rw [Finset.disjoint_filter]; intro v _ ⟨_, h⟩ h'; exact h h'
  have e : 2 ^ (P.ell0 - j) = 2 ^ (P.ell0 - (j + 1)) + 2 ^ (P.ell0 - (j + 1)) := by
    rw [← two_mul, ← pow_succ']; congr 1; omega
  rw [h0, h1, e] at hsplit
  have : (Finset.univ.filter fun v : P.K => P.PrefixZero j v ∧ ¬ P.PrefixZero (j + 1) v).card =
      (Finset.univ.filter fun v : P.K => P.PrefixZero (j + 1) v).card := by rw [h1]; omega
  rw [this]; ring

theorem sum_sign_sq (j : ℕ) (hj : j + 1 ≤ P.ell0) :
    ∑ v : P.K, P.sign j v ^ 2 ≤ (1 / 2 ^ j : ℝ) * Fintype.card P.K := by
  have h0 := P.card_prefixZero j (by omega)
  have hsq : ∀ v, P.sign j v ^ 2 = if P.PrefixZero j v then 1 else 0 := by
    intro v; unfold sign
    have hn : P.PrefixZero (j + 1) v → P.PrefixZero j v := fun h1 b hb => h1 b (by omega)
    by_cases a : P.PrefixZero j v
    · by_cases b : P.PrefixZero (j + 1) v
      · norm_num [a, b]
      · norm_num [a, b]
    · have b : ¬ P.PrefixZero (j + 1) v := fun b => a (hn b)
      norm_num [a, b]
  simp only [hsq, Finset.sum_boole, h0]
  rw [card_galoisField _ P.ell0_ne_zero]
  push_cast
  rw [show (2 : ℝ) ^ P.ell0 = 2 ^ (P.ell0 - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel (by omega)]]
  field_simp
  exact le_refl _

/-- **The level moment** (`filt:scalar-moment` at the hash): `Σ_h δ_j^{2t} ≤ |seeds|·(t+1)t^t(t+3|active|2^{−j})^t`. -/
theorem sum_delta_pow_le (j : ℕ) (hj : j + 1 ≤ P.ell0) (Z : List Bool) (hZ : Z.length ≤ P.M) :
    ∑ h : P.Seed, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) ≤
      Fintype.card P.Seed * ((P.t + 1) * (P.t : ℝ) ^ P.t * (P.t + 3 * (P.active Z).card * (1 / 2 ^ j)) ^ P.t) := by
  simp only [P.levelDelta_eq _ j Z hZ]
  exact kwise_moment_le P.t P.value P.value_kwise (P.active Z) (fun _ v => P.sign j v)
    (fun _ v => P.sign_abs_le j v) (fun _ => P.sum_sign j hj) (1 / 2 ^ j) (by positivity) (fun _ => P.sum_sign_sq j hj)

/-- `W_j²·2^j ≥ 128t(t·2^j + 3B_*)`. -/
theorem W_sq_ge (j : ℕ) : 128 * P.t * (P.t * 2 ^ j + 3 * P.Bstar) ≤ P.W j ^ 2 * 2 ^ j := by
  obtain ⟨q, hq⟩ : ∃ q, q = j / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs0⟩ : ∃ s, s = Nat.sqrt (P.t * P.Bstar) + 1 := ⟨_, rfl⟩
  have hW : P.W j = 16 * P.t + 20 * (s / 2 ^ q + 1) := by unfold W; rw [hq, hs0]
  have hs : P.t * P.Bstar ≤ s ^ 2 := by rw [hs0]; exact (Nat.lt_succ_sqrt' _).le
  have hfl : s ≤ (s / 2 ^ q + 1) * 2 ^ q := by
    have := Nat.lt_div_mul_add (a := s) (Nat.two_pow_pos q); nlinarith
  have hWq : 16 * P.t * 2 ^ q + 20 * s ≤ P.W j * 2 ^ q := by rw [hW]; nlinarith
  have hj1 : 2 ^ (2 * q) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj2 : 2 ^ j ≤ 2 * 2 ^ (2 * q) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (2 ^ q) ^ 2 = 2 ^ (2 * q) := by rw [← pow_mul, mul_comm]
  have hsq : (16 * P.t * 2 ^ q + 20 * s) ^ 2 ≤ (P.W j * 2 ^ q) ^ 2 := Nat.pow_le_pow_left hWq 2
  have e1 : 256 * P.t ^ 2 * 2 ^ (2 * q) + 400 * s ^ 2 ≤ (16 * P.t * 2 ^ q + 20 * s) ^ 2 := by
    have hexp : (16 * P.t * 2 ^ q + 20 * s) ^ 2 =
        256 * P.t ^ 2 * (2 ^ q) ^ 2 + 640 * P.t * 2 ^ q * s + 400 * s ^ 2 := by ring
    rw [hexp, h4]; linarith [Nat.zero_le (640 * P.t * 2 ^ q * s)]
  have e2 : (P.W j * 2 ^ q) ^ 2 = P.W j ^ 2 * 2 ^ (2 * q) := by rw [mul_pow, h4]
  have e3 : P.W j ^ 2 * 2 ^ (2 * q) ≤ P.W j ^ 2 * 2 ^ j := Nat.mul_le_mul_left _ hj1
  have e4 : 128 * P.t ^ 2 * 2 ^ j ≤ 256 * P.t ^ 2 * 2 ^ (2 * q) := by
    have := Nat.mul_le_mul_left (128 * P.t ^ 2) hj2; linarith
  have e5 : 384 * (P.t * P.Bstar) ≤ 400 * s ^ 2 :=
    calc 384 * (P.t * P.Bstar) ≤ 384 * s ^ 2 := Nat.mul_le_mul_left _ hs
      _ ≤ 400 * s ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
  calc 128 * P.t * (P.t * 2 ^ j + 3 * P.Bstar) = 128 * P.t ^ 2 * 2 ^ j + 384 * (P.t * P.Bstar) := by ring
    _ ≤ 256 * P.t ^ 2 * 2 ^ (2 * q) + 400 * s ^ 2 := by linarith
    _ ≤ (16 * P.t * 2 ^ q + 20 * s) ^ 2 := e1
    _ ≤ (P.W j * 2 ^ q) ^ 2 := hsq
    _ = P.W j ^ 2 * 2 ^ (2 * q) := e2
    _ ≤ P.W j ^ 2 * 2 ^ j := e3

/-- **The level ratio**: `Σ_h (δ_j/W_j)^{2t} ≤ |seeds|·8^{−2t}` when the population has at most `B_*` ones. -/
theorem sum_ratio_le (j : ℕ) (hj : j + 1 ≤ P.ell0) (Z : List Bool) (hZ : Z.length ≤ P.M)
    (hw : (P.active Z).card ≤ P.Bstar) :
    ∑ h : P.Seed, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) ≤
      Fintype.card P.Seed * (1 / 64) ^ P.t := by
  have hWpos : (0 : ℝ) < P.W j := by exact_mod_cast (show 0 < P.W j by have := P.W_ge j; omega)
  rw [← Finset.sum_div, div_le_iff₀ (pow_pos hWpos _)]
  refine (P.sum_delta_pow_le j hj Z hZ).trans ?_
  -- `(t+1)t^t(t+3λ)^t ≤ 64^{−t}·W^{2t}`, from `W² ≥ 128t(t+3λ)`
  have hlam : (P.active Z).card * (1 / 2 ^ j : ℝ) ≤ P.Bstar * (1 / 2 ^ j) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hw) (by positivity)
  have hW2 : 128 * (P.t : ℝ) * (P.t + 3 * P.Bstar * (1 / 2 ^ j)) ≤ (P.W j : ℝ) ^ 2 := by
    have := P.W_sq_ge j
    have h' : (128 * P.t * (P.t * 2 ^ j + 3 * P.Bstar) : ℝ) ≤ (P.W j : ℝ) ^ 2 * 2 ^ j := by exact_mod_cast this
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [show (128 * P.t * (P.t + 3 * P.Bstar * (1 / 2 ^ j)) : ℝ) = (128 * P.t * (P.t * 2 ^ j + 3 * P.Bstar)) / 2 ^ j by
      field_simp]
    rw [div_le_iff₀ h2]; exact h'
  have hbase : (0 : ℝ) ≤ P.t + 3 * (P.active Z).card * (1 / 2 ^ j) := by positivity
  have hmono : (P.t + 3 * (P.active Z).card * (1 / 2 ^ j) : ℝ) ≤ P.t + 3 * P.Bstar * (1 / 2 ^ j) := by linarith
  have ht1 : ((P.t : ℝ) + 1) ≤ 2 ^ P.t := by
    have := Nat.lt_two_pow_self (n := P.t); exact_mod_cast Nat.succ_le_of_lt this
  have key : (P.t + 1) * (P.t : ℝ) ^ P.t * (P.t + 3 * (P.active Z).card * (1 / 2 ^ j)) ^ P.t ≤
      (1 / 64) ^ P.t * (P.W j : ℝ) ^ (2 * P.t) := by
    have h64 : (0 : ℝ) < 64 ^ P.t := by positivity
    have hstep : 64 ^ P.t * ((P.t + 1) * (P.t : ℝ) ^ P.t * (P.t + 3 * (P.active Z).card * (1 / 2 ^ j)) ^ P.t) ≤
        (P.W j : ℝ) ^ (2 * P.t) := by
      calc 64 ^ P.t * ((P.t + 1) * (P.t : ℝ) ^ P.t * (P.t + 3 * (P.active Z).card * (1 / 2 ^ j)) ^ P.t)
          ≤ 64 ^ P.t * (2 ^ P.t * (P.t : ℝ) ^ P.t * (P.t + 3 * P.Bstar * (1 / 2 ^ j)) ^ P.t) := by gcongr
        _ = (128 * (P.t : ℝ) * (P.t + 3 * P.Bstar * (1 / 2 ^ j))) ^ P.t := by
            rw [mul_pow, mul_pow, show (128 : ℝ) = 64 * 2 by norm_num, mul_pow]; ring
        _ ≤ ((P.W j : ℝ) ^ 2) ^ P.t := by gcongr
        _ = (P.W j : ℝ) ^ (2 * P.t) := by rw [← pow_mul]
    rw [one_div_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ h64, mul_comm]
    exact hstep
  calc (Fintype.card P.Seed : ℝ) * ((P.t + 1) * (P.t : ℝ) ^ P.t * (P.t + 3 * (P.active Z).card * (1 / 2 ^ j)) ^ P.t)
      ≤ Fintype.card P.Seed * ((1 / 64) ^ P.t * (P.W j : ℝ) ^ (2 * P.t)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- The terminal count's mean: `Σ_h c_J = |seeds|·|active|·2^{−J}`. -/
theorem sum_terminal (Z : List Bool) (hZ : Z.length ≤ P.M) (ht : 1 ≤ P.t) :
    ∑ h : P.Seed, ((P.data h).levelCount P.J Z : ℝ) = Fintype.card P.Seed * ((P.active Z).card * (1 / 2 ^ P.J)) := by
  simp only [P.levelCount_eq _ P.J Z hZ]
  rw [Finset.sum_comm]
  have hone : ∀ i ∈ P.active Z, ∑ h : P.Seed, (if P.PrefixZero P.J (P.value h i) then (1 : ℝ) else 0) =
      Fintype.card P.Seed * (1 / 2 ^ P.J) := by
    intro i _
    have := kwise_prod_sum (2 * P.t) P.value P.value_kwise {i} (by simp; omega)
      (fun _ v => if P.PrefixZero P.J v then (1 : ℝ) else 0)
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one] at this
    have hKsum : (∑ v : P.K, if P.PrefixZero P.J v then (1 : ℝ) else 0) = 2 ^ (P.ell0 - P.J) := by
      rw [Finset.sum_boole, P.card_prefixZero P.J P.J_lt_ell0.le]; push_cast; rfl
    rw [hKsum, card_galoisField _ P.ell0_ne_zero] at this
    push_cast at this
    rw [show (2 : ℝ) ^ P.ell0 = 2 ^ (P.ell0 - P.J) * 2 ^ P.J by
      rw [← pow_add, Nat.sub_add_cancel P.J_lt_ell0.le]] at this
    have h2 : (0 : ℝ) < 2 ^ (P.ell0 - P.J) := by positivity
    have h3 : (0 : ℝ) < 2 ^ P.J := by positivity
    field_simp
    nlinarith [this]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul]
  ring

/-! ## The majorant -/

noncomputable def H (Zs : List (List Bool)) (h : P.Seed) : ℝ :=
  (Zs.map fun Z => ((P.data h).levelCount P.J Z : ℝ) +
    ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t)).sum

theorem term_nonneg (h : P.Seed) (Z : List Bool) :
    0 ≤ ((P.data h).levelCount P.J Z : ℝ) +
      ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) := by
  apply add_nonneg (by positivity)
  exact Finset.sum_nonneg fun j _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)

theorem H_nonneg (Zs : List (List Bool)) (h : P.Seed) : 0 ≤ P.H Zs h :=
  List.sum_nonneg fun x hx => by
    obtain ⟨Z, _, rfl⟩ := List.mem_map.mp hx; exact P.term_nonneg h Z

theorem H_dominates (ht : 1 ≤ P.t) (Zs : List (List Bool)) (h : P.Seed) (Z : List Bool) (hZ : Z ∈ Zs)
    (hbad : ¬ (P.data h).Good Z) : 1 ≤ P.H Zs h := by
  have hterm : 1 ≤ ((P.data h).levelCount P.J Z : ℝ) +
      ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) := by
    unfold ListData.Good at hbad
    simp only [not_and_or, not_forall, not_le] at hbad
    rcases hbad with hc | ⟨j, hj, hδ⟩
    · have hc' : (P.data h).levelCount P.J Z ≠ 0 := hc
      have : (1 : ℝ) ≤ (P.data h).levelCount P.J Z := by
        have : 1 ≤ (P.data h).levelCount P.J Z := Nat.one_le_iff_ne_zero.mpr hc'
        exact_mod_cast this
      have hs : 0 ≤ ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) :=
        Finset.sum_nonneg fun j _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)
      linarith
    · have hWpos : (0 : ℝ) < P.W j := by exact_mod_cast (show 0 < P.W j by unfold W; omega)
      have hlt : (P.W j : ℝ) < |((P.data h).levelDelta j Z : ℝ)| := by
        have : ((P.W j : ℤ) : ℝ) < ((|(P.data h).levelDelta j Z| : ℤ) : ℝ) := by exact_mod_cast hδ
        push_cast at this; exact this
      have hone : 1 ≤ ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) := by
        rw [le_div_iff₀ (by positivity), one_mul, pow_mul, pow_mul, ← sq_abs ((P.data h).levelDelta j Z : ℝ)]
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hWpos.le hlt.le 2) _
      have hsingle := Finset.single_le_sum (s := Finset.range P.J) (f := fun j => ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) /
        (P.W j : ℝ) ^ (2 * P.t)) (fun j _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity))
        (Finset.mem_range.mpr hj)
      have : (0 : ℝ) ≤ (P.data h).levelCount P.J Z := by positivity
      linarith
  unfold H
  have hle := List.single_le_sum (l := Zs.map fun Z => ((P.data h).levelCount P.J Z : ℝ) +
    ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t))
    (fun x hx => by obtain ⟨Z, _, rfl⟩ := List.mem_map.mp hx; exact P.term_nonneg h Z) _
    (List.mem_map.mpr ⟨Z, hZ, rfl⟩)
  linarith

theorem sum_H_le (ht : 1 ≤ P.t) (Zs : List (List Bool)) (hZs : ∀ Z ∈ Zs, Z.length ≤ P.M ∧ (P.active Z).card ≤ P.Bstar) :
    ∑ h : P.Seed, P.H Zs h ≤
      Fintype.card P.Seed * (Zs.length * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := by
  unfold H
  induction Zs with
  | nil => simp
  | cons Z Zs ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, List.length_cons]
    have hZ := hZs Z (List.mem_cons_self ..)
    have ih' := ih fun Z' hZ' => hZs Z' (List.mem_cons_of_mem _ hZ')
    have h1 := P.sum_terminal Z hZ.1 ht
    have h2 : ∑ h : P.Seed, ∑ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) /
        (P.W j : ℝ) ^ (2 * P.t) ≤ Fintype.card P.Seed * (P.J * (1 / 64) ^ P.t) := by
      rw [Finset.sum_comm]
      calc ∑ j ∈ Finset.range P.J, ∑ h : P.Seed, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t)
          ≤ ∑ _j ∈ Finset.range P.J, (Fintype.card P.Seed : ℝ) * (1 / 64) ^ P.t :=
            Finset.sum_le_sum fun j hj => P.sum_ratio_le j (by
              have := Finset.mem_range.mp hj; have := P.J_lt_ell0; omega) Z hZ.1 hZ.2
        _ = Fintype.card P.Seed * (P.J * (1 / 64) ^ P.t) := by simp; ring
    have hact : ((P.active Z).card : ℝ) * (1 / 2 ^ P.J) ≤ P.Bstar * (1 / 2 ^ P.J) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hZ.2) (by positivity)
    have hS : (0 : ℝ) ≤ Fintype.card P.Seed := by positivity
    rw [h1]
    push_cast
    nlinarith

theorem H_le_max (Zs : List (List Bool)) (hZs : ∀ Z ∈ Zs, Z.length ≤ P.M) (h : P.Seed) :
    P.H Zs h ≤ Zs.length * (P.M + P.J * (P.M : ℝ) ^ (2 * P.t)) := by
  unfold H
  induction Zs with
  | nil => simp
  | cons Z Zs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ih' := ih fun Z' hZ' => hZs Z' (List.mem_cons_of_mem _ hZ')
    have hZ := hZs Z (List.mem_cons_self ..)
    have hc : ((P.data h).levelCount P.J Z : ℝ) ≤ P.M := by
      exact_mod_cast ((P.data h).levelCount_le P.J Z).trans hZ
    have hd : ∀ j ∈ Finset.range P.J, ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t) ≤
        (P.M : ℝ) ^ (2 * P.t) := by
      intro j _
      have hWpos : (1 : ℝ) ≤ P.W j := by exact_mod_cast (show 1 ≤ P.W j by have := P.W_ge j; omega)
      have hδ : |((P.data h).levelDelta j Z : ℝ)| ≤ P.M := by
        unfold ListData.levelDelta
        have a := (P.data h).levelCount_le j Z
        have b := (P.data h).levelCount_le (j + 1) Z
        have hj1 : (P.data h).levelCount (j + 1) Z ≤ (P.data h).levelCount j Z := by
          unfold ListData.levelCount
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, hi.2.1, P.inLevel_nest h j i hi.2.2⟩
        push_cast
        rw [abs_le]
        constructor <;> push_cast <;> [skip; skip] <;>
          (have : ((P.data h).levelCount j Z : ℝ) ≤ P.M := by exact_mod_cast a.trans hZ) <;>
          (have : ((P.data h).levelCount (j + 1) Z : ℝ) ≤ (P.data h).levelCount j Z := by exact_mod_cast hj1) <;>
          (have : (0 : ℝ) ≤ (P.data h).levelCount (j + 1) Z := by positivity) <;> linarith
      calc ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) / (P.W j : ℝ) ^ (2 * P.t)
          ≤ ((P.data h).levelDelta j Z : ℝ) ^ (2 * P.t) := div_le_self (by rw [pow_mul]; positivity)
            (one_le_pow₀ hWpos)
        _ = |((P.data h).levelDelta j Z : ℝ)| ^ (2 * P.t) := by rw [pow_mul, pow_mul, sq_abs]
        _ ≤ (P.M : ℝ) ^ (2 * P.t) := pow_le_pow_left₀ (abs_nonneg _) hδ _
    have hsum := Finset.sum_le_sum hd
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    push_cast
    nlinarith

theorem sum_W_le : ∑ j ∈ Finset.range P.J, P.W j ≤ (16 * P.t + 20) * P.J + 80 * (Nat.sqrt (P.t * P.Bstar) + 1) := by
  have hreal : (∑ j ∈ Finset.range P.J, (((Nat.sqrt (P.t * P.Bstar) + 1) / 2 ^ (j / 2) : ℕ) : ℝ)) ≤
      4 * ((Nat.sqrt (P.t * P.Bstar) + 1 : ℕ) : ℝ) := by
    set s := Nat.sqrt (P.t * P.Bstar) + 1
    have hterm : ∀ j, ((s / 2 ^ (j / 2) : ℕ) : ℝ) ≤ s * (1 / 2 : ℝ) ^ (j / 2) := by
      intro j
      have := Nat.cast_div_le (α := ℝ) (m := s) (n := 2 ^ (j / 2))
      push_cast at this
      rw [one_div_pow, mul_one_div]; exact this
    have hgeo : ∀ Q, ∑ j ∈ Finset.range (2 * Q), (1 / 2 : ℝ) ^ (j / 2) = 4 - 4 * (1 / 2) ^ Q := by
      intro Q
      induction Q with
      | zero => simp
      | succ Q ih =>
        rw [show 2 * (Q + 1) = 2 * Q + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        have e1 : (2 * Q) / 2 = Q := by omega
        have e2 : (2 * Q + 1) / 2 = Q := by omega
        rw [e1, e2, pow_succ]; ring
    calc (∑ j ∈ Finset.range P.J, ((s / 2 ^ (j / 2) : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.range P.J, s * (1 / 2 : ℝ) ^ (j / 2) := Finset.sum_le_sum fun j _ => hterm j
      _ ≤ ∑ j ∈ Finset.range (2 * P.J), s * (1 / 2 : ℝ) ^ (j / 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by
            simp only [Finset.mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
      _ = s * (4 - 4 * (1 / 2) ^ P.J) := by rw [← Finset.mul_sum, hgeo]
      _ ≤ 4 * s := by
          have : (0 : ℝ) ≤ (1 / 2) ^ P.J := by positivity
          have : (0 : ℝ) ≤ s := by positivity
          nlinarith
  have hnat : ∑ j ∈ Finset.range P.J, (Nat.sqrt (P.t * P.Bstar) + 1) / 2 ^ (j / 2) ≤
      4 * (Nat.sqrt (P.t * P.Bstar) + 1) := by exact_mod_cast hreal
  unfold W
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  nlinarith

theorem two_pow_ell_le (h : P.Seed) (j : ℕ) : 2 ^ (P.data h).ell j - 1 ≤ 4 * P.W j := by
  have hW := P.W_ge j
  have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := 2 * P.W j + 1) (by omega)
  have hpos : 0 < Nat.clog 2 (2 * P.W j + 1) := Nat.clog_pos (by norm_num) (by omega)
  have heq : 2 ^ Nat.clog 2 (2 * P.W j + 1) = 2 ^ (Nat.clog 2 (2 * P.W j + 1)).pred * 2 := by
    rw [← pow_succ, Nat.pred_eq_sub_one]; congr 1
  show 2 ^ Nat.clog 2 (2 * P.W j + 1) - 1 ≤ 4 * P.W j
  omega

theorem lists_degree (h : P.Seed) (L s : ℕ) :
    ((P.data h).polyStates L s).totalDegree ≤ 4 * ((16 * P.t + 20) * P.J + 80 * (Nat.sqrt (P.t * P.Bstar) + 1)) ∧
      ∀ z : Fin L → Bool, MvPolynomial.eval (fun i => bitF2 (z i)) ((P.data h).polyStates L s) =
        (P.data h).listStates (List.ofFn z) s := by
  obtain ⟨hdeg, heval⟩ := (P.data h).listStates_poly (P.inLevel_nest h) L s
  refine ⟨hdeg.trans ?_, heval⟩
  calc ∑ j ∈ Finset.range (P.data h).J, (2 ^ (P.data h).ell j - 1) ≤ ∑ j ∈ Finset.range P.J, 4 * P.W j :=
        Finset.sum_le_sum fun j _ => P.two_pow_ell_le h j
    _ = 4 * ∑ j ∈ Finset.range P.J, P.W j := by rw [Finset.mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ P.sum_W_le

theorem lists_fail_le (ht : 1 ≤ P.t) (Zs : List (List Bool))
    (hZs : ∀ Z ∈ Zs, Z.length ≤ P.M ∧ (P.active Z).card ≤ P.Bstar) :
    SupplierPipeline.booleanMean (fun h : P.Seed => decide (∃ Z ∈ Zs, (P.data h).listReport Z ≠ Z.count true)) ≤
      Zs.length * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t) := by
  unfold SupplierPipeline.booleanMean
  have hS : (0 : ℝ) < Fintype.card P.Seed := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hS]
  have hpt : ∀ h : P.Seed, bitAsReal (decide (∃ Z ∈ Zs, (P.data h).listReport Z ≠ Z.count true)) ≤ P.H Zs h := by
    intro h
    by_cases hf : ∃ Z ∈ Zs, (P.data h).listReport Z ≠ Z.count true
    · simp only [hf, decide_true, bitAsReal, if_true]
      obtain ⟨Z, hZ, hne⟩ := hf
      apply P.H_dominates ht Zs h Z hZ
      intro hgood
      exact hne ((P.data h).listReport_eq_count (P.inLevel_zero h) (P.inLevel_nest h) Z (hZs Z hZ).1 hgood)
    · simp only [hf, decide_false, bitAsReal]; exact P.H_nonneg Zs h
  calc ∑ h, bitAsReal (decide (∃ Z ∈ Zs, (P.data h).listReport Z ≠ Z.count true)) ≤ ∑ h, P.H Zs h :=
        Finset.sum_le_sum fun h _ => hpt h
    _ ≤ Fintype.card P.Seed * (Zs.length * (P.Bstar * (1 / 2 ^ P.J) + P.J * (1 / 64) ^ P.t)) := P.sum_H_le ht Zs hZs
    _ = _ := by ring

theorem card_seed : Fintype.card P.Seed = 2 ^ (2 * P.t * P.ell0) := by
  rw [Fintype.card_fun, Fintype.card_fin, card_galoisField _ P.ell0_ne_zero, ← pow_mul, mul_comm]

end MajorantParams

end NearCubicWires.WireExponent3_5.Filters
