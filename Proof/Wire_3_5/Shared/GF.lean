import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF2

/-- One LFSR step: multiplication by `x` modulo `p` (bit `ℓ` of `p` set). -/
def lfsr (p ℓ a : ℕ) : ℕ := if (2 * a).testBit ℓ then (2 * a) ^^^ p else 2 * a

def lfsrPow (p ℓ : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => lfsr p ℓ (lfsrPow p ℓ n)

/-- The first return of the LFSR orbit of `1` to `1` (or `0` if none within `2^ℓ`). -/
def period (p ℓ : ℕ) : ℕ :=
  ((List.range (2 ^ ℓ)).find? (fun j => j ≠ 0 && lfsrPow p ℓ j == 1)).getD 0

/-- **The certificate is sound in any finite commutative ring**: a unit of order `|R| - 1` makes
`R` a field (all nonzero elements are its powers). Applied to `R = F₂[x]/(p)`, `g = x`, the LFSR
period test replaces an irreducibility proof. -/
theorem isField_of_unit_of_order {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    [Nontrivial R] (g : R) (hg : IsUnit g) (hord : orderOf g = Fintype.card R - 1) : IsField R := by
  classical
  let S : Finset R := (Finset.range (orderOf g)).image (g ^ ·)
  have hcardS : S.card = orderOf g := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab
  have hsub : S ⊆ Finset.univ.erase 0 := by
    intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_erase.mpr ⟨(hg.pow j).ne_zero, Finset.mem_univ _⟩
  have hcardT : (Finset.univ.erase (0 : R)).card = Fintype.card R - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have heq : S = Finset.univ.erase 0 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardT, hcardS, hord])
  refine ⟨exists_pair_ne R, mul_comm, fun {a} ha => ?_⟩
  have hmem : a ∈ S := by rw [heq]; exact Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨u, hu⟩ := hg.pow j
  exact ⟨↑u⁻¹, by rw [← hu, Units.mul_inv]⟩

end NearCubicWires.WireExponent3_5.GF2

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial NearCubicWires.WireExponent3_5.GF2

/-- **The polynomial of a bit vector**: `Σ_{i : a_i = 1} X^i`. -/
noncomputable def toPoly (a : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range a, if a.testBit i then (X : (ZMod 2)[X]) ^ i else 0

/-- The bit value as an element of `𝔽₂`. -/
def bitF (b : Bool) : ZMod 2 := if b then 1 else 0

theorem testBit_ge_self (a i : ℕ) (hi : a ≤ i) : a.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hi))

/-- **Coefficient `i` is bit `i`.** -/
theorem coeff_toPoly (a i : ℕ) : (toPoly a).coeff i = bitF (a.testBit i) := by
  unfold toPoly
  rw [Polynomial.finsetSum_coeff]
  have h : ∀ j ∈ Finset.range a, (if a.testBit j then (X : (ZMod 2)[X]) ^ j else 0).coeff i =
      if j = i then bitF (a.testBit i) else 0 := by
    intro j _
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      unfold bitF
      split_ifs <;> simp
    · rw [if_neg hj]
      have hij : i ≠ j := fun h => hj h.symm
      split_ifs <;> simp [coeff_X_pow, hij]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hi
  · rfl
  · rw [testBit_ge_self a i (by simp at hi; omega)]
    rfl

theorem bitF_add (x y : Bool) : bitF (xor x y) = bitF x + bitF y := by
  cases x <;> cases y <;> decide

theorem bitF_injective : Function.Injective bitF := by
  intro x y h
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

theorem toPoly_injective : Function.Injective toPoly := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  apply bitF_injective
  rw [← coeff_toPoly, ← coeff_toPoly, h]

@[simp] theorem toPoly_zero : toPoly 0 = 0 := by simp [toPoly]

/-- **Exclusive-or is addition.** -/
theorem toPoly_xor (a b : ℕ) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext i
  rw [coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, Nat.testBit_xor, bitF_add]

theorem toPoly_two_pow (b : ℕ) : toPoly (2 ^ b) = X ^ b := by
  ext i
  rw [coeff_toPoly, coeff_X_pow, Nat.testBit_two_pow]
  by_cases h : b = i
  · subst h; simp [bitF]
  · have h' : i ≠ b := fun e => h e.symm
    simp [bitF, h, h']

@[simp] theorem toPoly_one : toPoly 1 = 1 := by
  simpa using toPoly_two_pow 0

/-- **A left shift is multiplication by `X^i`.** -/
theorem toPoly_two_pow_mul (i a : ℕ) : toPoly (2 ^ i * a) = X ^ i * toPoly a := by
  ext j
  rw [coeff_toPoly, Nat.testBit_two_pow_mul, coeff_X_pow_mul', coeff_toPoly]
  by_cases h : i ≤ j
  · simp [h]
  · simp [h, bitF]

theorem toPoly_two_mul (a : ℕ) : toPoly (2 * a) = X * toPoly a := by
  simpa using toPoly_two_pow_mul 1 a

/-- **`a < 2^ℓ` gives `deg < ℓ`.** -/
theorem degree_toPoly_lt (a ℓ : ℕ) (ha : a < 2 ^ ℓ) : (toPoly a).degree < ℓ := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hm))]
  rfl

/-- A number below `2^{ℓ+1}` whose bit `ℓ` is clear is below `2^ℓ`. -/
theorem lt_of_testBit_false (x ℓ : ℕ) (hx : x < 2 ^ (ℓ + 1)) (hb : x.testBit ℓ = false) : x < 2 ^ ℓ := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with rfl | hi'
  · exact hb
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi'))

/-- The exclusive-or of two numbers below `2^{ℓ+1}` with equal bit `ℓ` is below `2^ℓ`. -/
theorem lt_two_pow_of_testBit_eq (x y ℓ : ℕ) (hx : x < 2 ^ (ℓ + 1)) (hy : y < 2 ^ (ℓ + 1))
    (h : x.testBit ℓ = y.testBit ℓ) : x ^^^ y < 2 ^ ℓ := by
  apply lt_of_testBit_false _ _ (Nat.xor_lt_two_pow hx hy)
  rw [Nat.testBit_xor, h]
  simp

/-- A modulus of degree `ℓ`: bit `ℓ` set and `p < 2^{ℓ+1}`. -/
def ModulusOk (p ℓ : ℕ) : Prop := p.testBit ℓ = true ∧ p < 2 ^ (ℓ + 1)

theorem natDegree_toPoly (p ℓ : ℕ) (hp : ModulusOk p ℓ) : (toPoly p).natDegree = ℓ := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_toPoly, Nat.testBit_lt_two_pow (lt_of_lt_of_le hp.2 (Nat.pow_le_pow_right (by norm_num) hN))]
    rfl
  · rw [coeff_toPoly, hp.1]
    decide

/-- **The modulus polynomial is monic of degree `ℓ`.** -/
theorem toPoly_monic (p ℓ : ℕ) (hp : ModulusOk p ℓ) : (toPoly p).Monic := by
  unfold Monic leadingCoeff
  rw [natDegree_toPoly p ℓ hp, coeff_toPoly, hp.1]
  rfl

/-- The field element of an `ℓ`-bit vector: its polynomial modulo `p`. -/
noncomputable def rep (p a : ℕ) : AdjoinRoot (toPoly p) := AdjoinRoot.mk (toPoly p) (toPoly a)

noncomputable abbrev xRoot (p : ℕ) : AdjoinRoot (toPoly p) := AdjoinRoot.root (toPoly p)

theorem rep_xor (p a b : ℕ) : rep p (a ^^^ b) = rep p a + rep p b := by
  simp [rep, toPoly_xor]

@[simp] theorem rep_zero (p : ℕ) : rep p 0 = 0 := by simp [rep]

@[simp] theorem rep_one (p : ℕ) : rep p 1 = 1 := by simp [rep]

theorem rep_two_pow (p b : ℕ) : rep p (2 ^ b) = xRoot p ^ b := by
  simp [rep, toPoly_two_pow, AdjoinRoot.mk_X]

theorem rep_self (p : ℕ) : rep p p = 0 := AdjoinRoot.mk_self

theorem rep_two_mul (p a : ℕ) : rep p (2 * a) = xRoot p * rep p a := by
  simp [rep, toPoly_two_mul, AdjoinRoot.mk_X]

/-- **One LFSR step is multiplication by `x`** (shift, and xor the modulus when bit `ℓ` appears). -/
theorem lfsr_spec (p ℓ a : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) :
    lfsr p ℓ a < 2 ^ ℓ ∧ rep p (lfsr p ℓ a) = xRoot p * rep p a := by
  have h2a : 2 * a < 2 ^ (ℓ + 1) := by rw [pow_succ]; omega
  unfold lfsr
  split_ifs with hb
  · refine ⟨lt_two_pow_of_testBit_eq _ _ _ h2a hp.2 (by rw [hb, hp.1]), ?_⟩
    rw [rep_xor, rep_self, add_zero, rep_two_mul]
  · exact ⟨lt_of_testBit_false _ _ h2a (by simpa using hb), rep_two_mul p a⟩

/-- **The LFSR orbit of `1` is the powers of `x`.** -/
theorem lfsrPow_spec (p ℓ : ℕ) (hp : ModulusOk p ℓ) (hℓ : 1 ≤ ℓ) :
    ∀ j, lfsrPow p ℓ j < 2 ^ ℓ ∧ rep p (lfsrPow p ℓ j) = xRoot p ^ j
  | 0 => ⟨Nat.one_lt_two_pow (by omega), by simp [lfsrPow]⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := lfsrPow_spec p ℓ hp hℓ j
    obtain ⟨h3, h4⟩ := lfsr_spec p ℓ _ hp h1
    refine ⟨by simpa [lfsrPow] using h3, ?_⟩
    simp only [lfsrPow]
    rw [h4, h2, pow_succ, mul_comm]

/-! ## The bijection with `Fin (2^ℓ)` -/

/-- **Distinct `ℓ`-bit vectors are distinct field elements.** -/
theorem rep_injOn (p ℓ a b : ℕ) (hp : ModulusOk p ℓ) (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : rep p a = rep p b) : a = b := by
  apply toPoly_injective
  have hd := AdjoinRoot.mk_eq_mk.mp h
  have hdeg : (toPoly a - toPoly b).degree < (toPoly p).degree := by
    rw [degree_eq_natDegree (toPoly_monic p ℓ hp).ne_zero, natDegree_toPoly p ℓ hp]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_toPoly_lt a ℓ ha) (degree_toPoly_lt b ℓ hb))
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hd hdeg)

/-- The bit vector of a polynomial of degree `< ℓ`. -/
noncomputable def ofPoly (f : (ZMod 2)[X]) (ℓ : ℕ) : ℕ :=
  Finset.equivBitIndices.symm ((Finset.range ℓ).filter fun i => f.coeff i ≠ 0)

theorem testBit_equivBitIndices_symm (S : Finset ℕ) (i : ℕ) :
    (Finset.equivBitIndices.symm S).testBit i = decide (i ∈ S) := by
  have h := Finset.equivBitIndices.apply_symm_apply S
  conv_rhs => rw [← h]
  simp only [Finset.equivBitIndices_apply, List.mem_toFinset, Nat.mem_bitIndices]
  cases (Finset.equivBitIndices.symm S).testBit i <;> rfl

theorem zmod2_ne_zero (z : ZMod 2) (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

theorem toPoly_ofPoly (f : (ZMod 2)[X]) (ℓ : ℕ) (hf : f.degree < ℓ) : toPoly (ofPoly f ℓ) = f := by
  ext i
  rw [coeff_toPoly, ofPoly, testBit_equivBitIndices_symm]
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hi : i < ℓ
  · by_cases hc : f.coeff i = 0
    · simp [hc, bitF]
    · simp [hi, bitF, zmod2_ne_zero _ hc]
  · have hc : f.coeff i = 0 := (degree_lt_iff_coeff_zero f ℓ).mp hf i (by omega)
    simp [hi, hc, bitF]

theorem ofPoly_lt (f : (ZMod 2)[X]) (ℓ : ℕ) : ofPoly f ℓ < 2 ^ ℓ := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [ofPoly, testBit_equivBitIndices_symm]
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_false_iff_not, not_and]
  intro h; omega

theorem rep_surj (p ℓ : ℕ) (hp : ModulusOk p ℓ) (y : AdjoinRoot (toPoly p)) :
    ∃ a < 2 ^ ℓ, rep p a = y := by
  have hm := toPoly_monic p ℓ hp
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  have hdeg : (f %ₘ toPoly p).degree < ℓ := by
    have := degree_modByMonic_lt f hm
    rwa [degree_eq_natDegree hm.ne_zero, natDegree_toPoly p ℓ hp] at this
  refine ⟨ofPoly (f %ₘ toPoly p) ℓ, ofPoly_lt _ _, ?_⟩
  rw [rep, toPoly_ofPoly _ _ hdeg]
  have := AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk (toPoly p) f)
  rwa [AdjoinRoot.modByMonicHom_mk] at this

/-- **The `ℓ`-bit vectors are the field**: `Fin (2^ℓ) ≃ 𝔽₂[X]/(p)`. -/
noncomputable def encEquiv (p ℓ : ℕ) (hp : ModulusOk p ℓ) : Fin (2 ^ ℓ) ≃ AdjoinRoot (toPoly p) :=
  Equiv.ofBijective (fun a => rep p a)
    ⟨fun a b h => Fin.ext (rep_injOn p ℓ a b hp a.isLt b.isLt h),
     fun y => let ⟨a, ha, h⟩ := rep_surj p ℓ hp y; ⟨⟨a, ha⟩, h⟩⟩

theorem encEquiv_apply (p ℓ : ℕ) (hp : ModulusOk p ℓ) (a : Fin (2 ^ ℓ)) : encEquiv p ℓ hp a = rep p a := rfl

/-- `|𝔽₂[X]/(p)| = 2^ℓ`. -/
theorem natCard_ref (p ℓ : ℕ) (hp : ModulusOk p ℓ) : Nat.card (AdjoinRoot (toPoly p)) = 2 ^ ℓ := by
  rw [← Nat.card_congr (encEquiv p ℓ hp), Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## The period certificate -/

/-- **The primitive-modulus certificate** (decidable; the machine's search tests it): degree `ℓ ≥ 1` and the LFSR orbit
of `1` has period exactly `2^ℓ − 1`. -/
def PrimitiveCert (p ℓ : ℕ) : Prop := 1 ≤ ℓ ∧ ModulusOk p ℓ ∧ period p ℓ = 2 ^ ℓ - 1

instance (p ℓ : ℕ) : Decidable (PrimitiveCert p ℓ) := by unfold PrimitiveCert ModulusOk; infer_instance

theorem orderOf_root (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : orderOf (xRoot p) = 2 ^ ℓ - 1 := by
  obtain ⟨hℓ, hp, hper⟩ := hc
  have htwo : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hpos : 0 < 2 ^ ℓ - 1 := by omega
  unfold period at hper
  cases hfind : (List.range (2 ^ ℓ)).find? (fun j => j ≠ 0 && lfsrPow p ℓ j == 1) with
  | none => rw [hfind] at hper; simp at hper; omega
  | some i =>
    rw [hfind] at hper
    simp only [Option.getD_some] at hper
    subst hper
    rw [List.find?_range_eq_some] at hfind
    obtain ⟨hpi, _, hbefore⟩ := hfind
    rw [orderOf_eq_iff hpos]
    constructor
    · have h1 : lfsrPow p ℓ (2 ^ ℓ - 1) = 1 := by simp at hpi; exact hpi.2
      rw [← (lfsrPow_spec p ℓ hp hℓ _).2, h1, rep_one]
    · intro m hm hm0 hroot
      have hnot := hbefore m hm
      have h1 : lfsrPow p ℓ m = 1 := by
        apply rep_injOn p ℓ _ _ hp (lfsrPow_spec p ℓ hp hℓ m).1 (Nat.one_lt_two_pow (by omega))
        rw [(lfsrPow_spec p ℓ hp hℓ m).2, hroot, rep_one]
      simp [h1] at hnot
      omega

/-- **The certificate makes `𝔽₂[X]/(p)` a field** (`GF2.isField_of_unit_of_order`; no irreducibility test). -/
theorem isField_ref (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : IsField (AdjoinRoot (toPoly p)) := by
  classical
  have hp := hc.2.1
  letI : Fintype (AdjoinRoot (toPoly p)) := Fintype.ofEquiv _ (encEquiv p ℓ hp)
  have hcard : Fintype.card (AdjoinRoot (toPoly p)) = 2 ^ ℓ := by
    rw [← Nat.card_eq_fintype_card, natCard_ref p ℓ hp]
  haveI : Nontrivial (AdjoinRoot (toPoly p)) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_two_pow (by have := hc.1; omega)
  have hord := orderOf_root p ℓ hc
  have hunit : IsUnit (xRoot p) := by
    have hpow : xRoot p ^ (2 ^ ℓ - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    apply IsUnit.of_pow_eq_one hpow
    have : 2 ≤ 2 ^ ℓ := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hc.1
    omega
  exact isField_of_unit_of_order (xRoot p) hunit (by rw [hord, hcard])

/-- **The certified modulus is irreducible** (a consequence of the field property, not a test). -/
theorem irreducible_ref (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : Irreducible (toPoly p) := by
  have hmax := Ideal.Quotient.maximal_of_isField _ (isField_ref p ℓ hc)
  have hne : toPoly p ≠ 0 := (toPoly_monic p ℓ hc.2.1).ne_zero
  exact ((Ideal.span_singleton_prime hne).mp hmax.isPrime).irreducible

theorem fact_irreducible (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) : Fact (Irreducible (toPoly p)) :=
  ⟨irreducible_ref p ℓ hc⟩

noncomputable def refAlgEquivGalois (p ℓ : ℕ) (hc : PrimitiveCert p ℓ) :
    letI := fact_irreducible p ℓ hc
    AdjoinRoot (toPoly p) ≃ₐ[ZMod 2] GaloisField 2 ℓ :=
  letI := fact_irreducible p ℓ hc
  GaloisField.algEquivGaloisField 2 ℓ (natCard_ref p ℓ hc.2.1)

/-- **The modulus search** (the ref of the machine's `2^{O(ℓ)}` preprocessing): the first `p ∈ [2^ℓ, 2^{ℓ+1})` that
passes the period certificate. -/
def firstPrimitive (ℓ : ℕ) : ℕ :=
  2 ^ ℓ + ((List.range (2 ^ ℓ)).find? fun j => decide (PrimitiveCert (2 ^ ℓ + j) ℓ)).getD 0

end NearCubicWires.WireExponent3_5.GF
