import Proof.Wire_3_5.SamplerSeed
import Proof.Wire_3_5.GFTrace
import Proof.Wire_3_5.FilterSoftGauss

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.WireExponent3_5.Filters Finset

theorem je_fmul_eq : JoinElimination.fmul = GF2.fmul := rfl

/-- The reference power is the field power. -/
theorem fpow_spec (p ℓ x : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hx : x < 2 ^ ℓ) :
    ∀ i, JoinElimination.fpow p ℓ x i < 2 ^ ℓ ∧ rep p (JoinElimination.fpow p ℓ x i) = rep p x ^ i
  | 0 => ⟨Nat.one_lt_two_pow (by omega), by simp [JoinElimination.fpow]⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := fpow_spec p ℓ x hp hℓ hx i
    obtain ⟨h3, h4⟩ := fmul_spec p ℓ _ x hp h1 hx
    simp only [JoinElimination.fpow, je_fmul_eq]
    exact ⟨h3, by rw [h4, h2, pow_succ]⟩

/-- The coefficient `a_i` of a seed: bits `[iℓ, (i+1)ℓ)`. -/
def seedCoeff (ℓ seed i : ℕ) : ℕ := (seed >>> (i * ℓ)) % 2 ^ ℓ

theorem seedCoeff_lt (ℓ seed i : ℕ) : seedCoeff ℓ seed i < 2 ^ ℓ := Nat.mod_lt _ (Nat.two_pow_pos ℓ)

theorem testBit_seedCoeff (ℓ seed i t : ℕ) (ht : t < ℓ) :
    (seedCoeff ℓ seed i).testBit t = seed.testBit (i * ℓ + t) := by
  unfold seedCoeff
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht]

/-- The reference generator's fold. -/
def genFold (p ℓ seed lam m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc i => acc ^^^ JoinElimination.fmul p ℓ ((seed >>> (i * ℓ)) % 2 ^ ℓ)
    (JoinElimination.fpow p ℓ lam i)) 0

theorem gen_eq (p ℓ twoH seed lam : ℕ) : JoinElimination.gen p ℓ twoH seed lam = genFold p ℓ seed lam twoH := rfl

/-- **The reference generator is `Σ_i a_iλ^i` in the field.** -/
theorem gen_spec (p ℓ seed lam : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hlam : lam < 2 ^ ℓ) :
    ∀ m, genFold p ℓ seed lam m < 2 ^ ℓ ∧
      rep p (genFold p ℓ seed lam m) = ∑ i ∈ Finset.range m, rep p (seedCoeff ℓ seed i) * rep p lam ^ i
  | 0 => by simp [genFold]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := gen_spec p ℓ seed lam hp hℓ hlam m
    obtain ⟨h3, h4⟩ := fpow_spec p ℓ lam hp hℓ hlam m
    obtain ⟨h5, h6⟩ := fmul_spec p ℓ (seedCoeff ℓ seed m) _ hp (seedCoeff_lt ℓ seed m) h3
    unfold genFold at h1 h2 ⊢
    simp only [je_fmul_eq] at h1 h2 ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨Nat.xor_lt_two_pow h1 h5, ?_⟩
    rw [rep_xor, h2, Finset.sum_range_succ]
    unfold seedCoeff at h6
    rw [h6, h4]
    rfl

/-- The coefficient of seed bit `j` in output bit `c`: bit `c` of `x^{j mod ℓ}·λ^{⌊j/ℓ⌋}`. -/
def coeffBit (p ℓ lam c j : ℕ) : Bool :=
  (JoinElimination.fmul p ℓ (2 ^ (j % ℓ)) (JoinElimination.fpow p ℓ lam (j / ℓ))).testBit c

theorem sum_range_mul (ℓ : ℕ) (f : ℕ → ZMod 2) :
    ∀ m, ∑ j ∈ Finset.range (m * ℓ), f j = ∑ i ∈ Finset.range m, ∑ t ∈ Finset.range ℓ, f (i * ℓ + t)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul ℓ f m, Finset.sum_range_succ]

theorem gen_bit (p ℓ twoH seed lam c : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hlam : lam < 2 ^ ℓ) (hc : c < ℓ) :
    bitF ((JoinElimination.gen p ℓ twoH seed lam).testBit c) =
      ∑ j ∈ Finset.range (twoH * ℓ), bitF (seed.testBit j) * bitF (coeffBit p ℓ lam c j) := by
  set L := (projK p ℓ hp ℓ).toZModLinearMap 2
  obtain ⟨hg1, hg2⟩ := gen_spec p ℓ seed lam hp hℓ hlam twoH
  have hL : ∀ a, a < 2 ^ ℓ → L (rep p a) ⟨c, hc⟩ = bitF (a.testBit c) := fun a ha =>
    projK_rep p ℓ hp ℓ a ha ⟨c, hc⟩
  -- expand each coefficient in the power basis
  have hexp : rep p (genFold p ℓ seed lam twoH) = ∑ i ∈ Finset.range twoH, ∑ t ∈ Finset.range ℓ,
      bitF (seed.testBit (i * ℓ + t)) •
        rep p (JoinElimination.fmul p ℓ (2 ^ t) (JoinElimination.fpow p ℓ lam i)) := by
    rw [hg2]
    apply Finset.sum_congr rfl; intro i _
    rw [rep_eq_sum p (seedCoeff ℓ seed i) ℓ (seedCoeff_lt ℓ seed i), Finset.sum_mul]
    apply Finset.sum_congr rfl; intro t ht
    have ht' := Finset.mem_range.mp ht
    obtain ⟨h3, h4⟩ := fpow_spec p ℓ lam hp hℓ hlam i
    have h5 := (fmul_spec p ℓ (2 ^ t) _ hp (Nat.pow_lt_pow_right (by norm_num) ht') h3).2
    rw [je_fmul_eq, h5, rep_two_pow, h4, testBit_seedCoeff ℓ seed i t ht', smul_mul_assoc]
  rw [gen_eq, ← hL _ hg1, hexp, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_range_mul ℓ (fun j => bitF (seed.testBit j) * bitF (coeffBit p ℓ lam c j)) twoH]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro t ht
  have ht' := Finset.mem_range.mp ht
  obtain ⟨h3, _⟩ := fpow_spec p ℓ lam hp hℓ hlam i
  have hlt := (fmul_spec p ℓ (2 ^ t) _ hp (Nat.pow_lt_pow_right (by norm_num) ht') h3).1
  rw [← je_fmul_eq] at hlt
  rw [hL _ hlt]
  unfold coeffBit
  have hmod : (i * ℓ + t) % ℓ = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht']
  have hdiv : (i * ℓ + t) / ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht', zero_add]
  rw [hmod, hdiv]

/-! ## The rows of `system` -/

theorem testBit_or_fold (f : ℕ → Bool) :
    ∀ n j, ((List.range n).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0).testBit j =
      decide (j < n ∧ f j = true)
  | 0, j => by simp
  | n + 1, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := testBit_or_fold f n j
    split_ifs with h
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hj : j = n
      · subst hj; simp [h]
      · have : n ≠ j := fun e => hj e.symm
        simp only [this, decide_false, Bool.or_false]
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rw [ih]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
        · exact h1
        · exact absurd h2 h

theorem or_fold_lt (f : ℕ → Bool) (n : ℕ) :
    (List.range n).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0 < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_or_fold]
  simp; omega

theorem bitF_xor_fold (f : ℕ → Bool) :
    ∀ n, bitF ((List.range n).foldl (fun acc j => xor acc (f j)) false) = ∑ j ∈ Finset.range n, bitF (f j)
  | 0 => by simp [bitF]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, bitF_add, bitF_xor_fold f n,
      Finset.sum_range_succ]

theorem bitF_and (a b : Bool) : bitF (a && b) = bitF a * bitF b := by cases a <;> cases b <;> decide

theorem rowDot_eq (n m : ℕ) (x : Fin n → ZMod 2) : rowDot m x = ∑ i : Fin n, bitF (m.testBit i) * x i := by
  unfold rowDot
  apply Finset.sum_congr rfl; intro i _
  cases m.testBit i <;> simp [bitF]

theorem zmod2_add_iff (a b c : ZMod 2) : a + b = c ↔ b = c + a := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  constructor
  · intro h
    rw [← h]
    calc b = b + 0 := (add_zero b).symm
      _ = b + (a + a) := by rw [h2]
      _ = a + b + a := by ring
  · intro h
    rw [h]
    calc a + (c + a) = c + (a + a) := by ring
      _ = c := by rw [h2, add_zero]

theorem testBit_seed (pre plen r j : ℕ) :
    (pre % 2 ^ plen + (r <<< plen)).testBit j = if j < plen then pre.testBit j else r.testBit (j - plen) := by
  have hlt : pre % 2 ^ plen < 2 ^ plen := Nat.mod_lt _ (Nat.two_pow_pos plen)
  rw [Nat.shiftLeft_eq, add_comm, mul_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or,
    Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow]
  by_cases hj : j < plen
  · simp [hj, show ¬ plen ≤ j by omega]
  · simp [hj, show plen ≤ j by omega]

/-- The completion `r` of the free bits as an `𝔽₂` vector. -/
def freeVec (rest r : ℕ) : Fin rest → ZMod 2 := fun j => bitF (r.testBit j)

theorem rowSat_iff (p ℓ twoH plen pre lam target c r : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) (hlam : lam < 2 ^ ℓ)
    (hc : c < ℓ) (hplen : plen ≤ twoH * ℓ) :
    RowSat (freeVec (twoH * ℓ - plen) r)
      ((List.range (twoH * ℓ - plen)).foldl (fun acc j => if coeffBit p ℓ lam c (plen + j) then acc ||| (1 <<< j)
        else acc) 0,
       xor (target.testBit c) ((List.range plen).foldl (fun acc j => xor acc (coeffBit p ℓ lam c j && pre.testBit j))
        false)) ↔
      (JoinElimination.gen p ℓ twoH (pre % 2 ^ plen + (r <<< plen)) lam).testBit c = target.testBit c := by
  set rest := twoH * ℓ - plen
  set seed := pre % 2 ^ plen + (r <<< plen)
  unfold RowSat
  rw [rowDot_eq]
  simp only [testBit_or_fold, freeVec]
  rw [show bitF2 = bitF from rfl, bitF_add, bitF_xor_fold]
  simp only [bitF_and]
  have hfree : ∑ i : Fin rest, bitF (decide (i.val < rest ∧ coeffBit p ℓ lam c (plen + i.val) = true)) *
      bitF (r.testBit i) = ∑ j ∈ Finset.range rest, bitF (seed.testBit (plen + j)) * bitF (coeffBit p ℓ lam c (plen + j)) := by
    rw [Finset.sum_range (fun j => bitF (seed.testBit (plen + j)) * bitF (coeffBit p ℓ lam c (plen + j)))]
    apply Finset.sum_congr rfl; intro i _
    rw [testBit_seed, if_neg (by omega), show plen + i.val - plen = i.val by omega]
    simp only [i.isLt, true_and]
    cases coeffBit p ℓ lam c (plen + i.val) <;> simp [bitF, mul_comm]
  have hfix : ∑ j ∈ Finset.range plen, bitF (coeffBit p ℓ lam c j) * bitF (pre.testBit j) =
      ∑ j ∈ Finset.range plen, bitF (seed.testBit j) * bitF (coeffBit p ℓ lam c j) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [testBit_seed, if_pos (Finset.mem_range.mp hj), mul_comm]
  have htot := gen_bit p ℓ twoH seed lam c hp hℓ hlam hc
  rw [show twoH * ℓ = plen + rest by omega, Finset.sum_range_add] at htot
  rw [hfree, hfix, ← zmod2_add_iff, ← htot]
  exact ⟨fun h => bitF_injective h, fun h => by rw [h]⟩

/-! ## The elimination form is the completion count -/

theorem length_filter_range (P : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter P).length = ((Finset.range n).filter fun r => P r = true).card := by
  rw [Finset.card_filter, Finset.sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    congr 1
    rw [List.filter_cons, List.filter_nil]
    split_ifs <;> rfl

/-- The bits of a vector as a number (below `2^n`). -/
noncomputable def ofVec {n : ℕ} (y : Fin n → ZMod 2) : ℕ :=
  Finset.equivBitIndices.symm ((Finset.univ.filter fun i : Fin n => y i ≠ 0).map Fin.valEmbedding)

theorem testBit_ofVec {n : ℕ} (y : Fin n → ZMod 2) (i : ℕ) :
    (ofVec y).testBit i = decide (∃ h : i < n, y ⟨i, h⟩ ≠ 0) := by
  unfold ofVec
  rw [testBit_equivBitIndices_symm]
  congr 1
  apply propext
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨h, hy⟩; exact ⟨⟨i, h⟩, hy, rfl⟩

theorem ofVec_lt {n : ℕ} (y : Fin n → ZMod 2) : ofVec y < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_ofVec]
  simp only [decide_eq_false_iff_not, not_exists]
  intro h; omega

theorem freeVec_ofVec {n : ℕ} (y : Fin n → ZMod 2) : freeVec n (ofVec y) = y := by
  funext i
  unfold freeVec
  rw [testBit_ofVec]
  by_cases hy : y i = 0
  · simp [hy, bitF]
  · have : ∃ h : i.val < n, y ⟨i.val, h⟩ ≠ 0 := ⟨i.isLt, hy⟩
    simp only [this, decide_true, bitF, if_true]
    exact (zmod2_ne_zero _ hy).symm

theorem freeVec_injOn {n : ℕ} (r r' : ℕ) (hr : r < 2 ^ n) (hr' : r' < 2 ^ n) (h : freeVec n r = freeVec n r') :
    r = r' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact bitF_injective (congrFun h ⟨i, hi⟩)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The constraint check of `condProbBrute` at one completion. -/
def consOk (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) (r : ℕ) : Bool :=
  cons.all fun c => decide (JoinElimination.proj k (JoinElimination.gen p ℓ twoH (pre % 2 ^ plen + (r <<< plen)) c.1)
    = c.2)

theorem proj_eq_iff (k v w : ℕ) (hw : w < 2 ^ k) :
    JoinElimination.proj k v = w ↔ ∀ c < k, v.testBit c = w.testBit c := by
  unfold JoinElimination.proj
  constructor
  · intro h c hc
    rw [← h, Nat.testBit_mod_two_pow]; simp [hc]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro c
    rw [Nat.testBit_mod_two_pow]
    by_cases hc : c < k
    · simp [hc, h c hc]
    · simp only [hc, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem condProbGauss_eq_brute (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ)
    (hk : k ≤ ℓ) (hplen : plen ≤ twoH * ℓ) (hcons : ∀ c ∈ cons, c.1 < 2 ^ ℓ ∧ c.2 < 2 ^ k) :
    JoinElimination.condProbGauss p ℓ twoH k plen pre cons = JoinElimination.condProbBrute p ℓ twoH k plen pre cons := by
  set rest := twoH * ℓ - plen
  set rows := JoinElimination.system p ℓ twoH k plen pre cons
  have hmask : ∀ row ∈ rows, row.1 < 2 ^ rest := by
    intro row hrow
    simp only [rows, JoinElimination.system, List.mem_flatMap, List.mem_map, List.mem_range] at hrow
    obtain ⟨con, _, c, _, rfl⟩ := hrow
    exact or_fold_lt _ _
  have hsol : (solutions rest rows).card = ((Finset.range (2 ^ rest)).filter fun r =>
      consOk p ℓ twoH k plen pre cons r = true).card := by
    symm
    apply Finset.card_bij (fun r _ => freeVec rest r)
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]
      intro row hrow
      simp only [rows, JoinElimination.system, List.mem_flatMap, List.mem_map, List.mem_range] at hrow
      obtain ⟨con, hcon, c, hc, rfl⟩ := hrow
      have hok := hr.2
      simp only [consOk, List.all_eq_true, decide_eq_true_eq] at hok
      have := (proj_eq_iff k _ con.2 (hcons con hcon).2).mp (hok con hcon) c hc
      exact (rowSat_iff p ℓ twoH plen pre con.1 con.2 c r hp hℓ (hcons con hcon).1 (by omega) hplen).mpr this
    · intro r hr r' hr' h
      simp only [Finset.mem_filter, Finset.mem_range] at hr hr'
      exact freeVec_injOn r r' hr.1 hr'.1 h
    · intro y hy
      refine ⟨ofVec y, ?_, freeVec_ofVec y⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ofVec_lt y, ?_⟩
      simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [consOk, List.all_eq_true, decide_eq_true_eq]
      intro con hcon
      rw [proj_eq_iff k _ con.2 (hcons con hcon).2]
      intro c hc
      have hrow := hy _ (by
        simp only [rows, JoinElimination.system, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨con, hcon, c, hc, rfl⟩)
      rw [← freeVec_ofVec y] at hrow
      exact (rowSat_iff p ℓ twoH plen pre con.1 con.2 c (ofVec y) hp hℓ (hcons con hcon).1 (by omega) hplen).mp hrow
  have hg := gauss_solutions_card rest rows hmask
  unfold JoinElimination.condProbGauss JoinElimination.condProbBrute
  simp only
  rw [Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  rw [← hg, hsol, length_filter_range]
  rfl

/-! ## The reference generator is the generator of `samp:seed` -/

/-- The coefficients of a seed number. -/
noncomputable def decodeNat (P : SeedParams) (seed : ℕ) : P.Seed := fun i => rep P.modulus (seedCoeff P.ell seed i)

theorem pos_eq_gen (P : SeedParams) (seed : ℕ) (j : Fin P.Q) :
    P.pos (decodeNat P seed) j =
      P.cellEquiv (fun b => bitF ((JoinElimination.gen P.modulus P.ell 8 seed j).testBit b)) := by
  have hp := P.cert.2.1
  have hj : (j : ℕ) < 2 ^ P.ell := lt_of_lt_of_le j.isLt P.Q_le
  obtain ⟨h1, h2⟩ := gen_spec P.modulus P.ell seed j hp P.one_le_ell hj 8
  unfold SeedParams.pos
  congr 1
  funext b
  have hb : (b : ℕ) < P.ell := lt_of_lt_of_le b.isLt P.k_le
  have := projK_rep P.modulus P.ell hp (2 * P.kh) _ h1 b
  rw [gen_eq, ← this, h2]
  unfold SeedParams.proj SeedParams.value SeedParams.label decodeNat
  congr 2

end NearCubicWires.WireExponent3_5.Sampler
