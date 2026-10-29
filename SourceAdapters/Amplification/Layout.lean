import SourceAdapters.Amplification.Dyadic
import SourceAdapters.Amplification.ListDecode

/-!
# A01 steps 1, 3, 5: the rounded characteristic-two parameters and the binary-cube layout

 ("Full-range amplification interface"): "in the construction of [STV, Lemmas 25 and 28] choose a
binary extension field, rounding its size up to the required scale, and round the number of polynomial variables
up. The evaluation domain is then `F^m`; concatenation with a Hadamard block indexes the binary codeword by a
product of binary cubes. Its length is a power of two, with no padding of the codeword, and remains
`poly(2^n, 1/δ)`. … Since `S < U(n)`, we have `1/δ = 2^{O(n)}`, so the output has `O(n)` input bits."

STV's choices (text (`sec:overview-ae`), Lemma 25): "|F| = (c log k)²/ε³ … H ⊆ F of cardinality (log k)/ε and m = (log k)/
(log |H|)", with `k = 2^n` the message length. Rounded here, all in integer arithmetic, for `δ = 2^(-k-2)`
(`dyadicAcc k`) and an integer `C ≥ c²` where `c` is Theorem 29's constant:

* `h = k + 2 + size n` (`|H| = 2^h ≥ n/δ`), `m = ⌈n/h⌉` (so `m·h ≥ n`: `H^m` holds the `2^n` message positions);
* `d = m(2^h − 1)` (total degree of the low-degree extension);
* `t = h + 6k + 12 + size m + size C` (`|F| = 2^t`; then `c·√(d/2^t) < δ³`, Theorem 29's condition at the
  agreement `δ³` delivered by `exists_good_slot`, `thm29_condition`);
* output arity `ℓ = (m+1)·t`: the codeword is indexed by `F^m × 𝔽₂^t` (blocks × Hadamard positions), laid out on
  `Fin ℓ → Bool` by the computable bijection `layoutEquiv`, which preserves agreement counts
  (`card_agree_layout`). `arity_le`: `ℓ ≤ (44 + size C)·(n + k + 1)`, i.e. `O(n)` when `k = O(n)`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset

/-- `log₂|H|`. -/
def hParam (n k : ℕ) : ℕ := k + 2 + Nat.size n

/-- The number of variables `m = ⌈n/h⌉`. -/
def mParam (n k : ℕ) : ℕ := (n + hParam n k - 1) / hParam n k

/-- The total degree `d = m(2^h − 1)` of the low-degree extension. -/
def dParam (n k : ℕ) : ℕ := mParam n k * (2 ^ hParam n k - 1)

/-- `log₂|F|`. -/
def tParam (C n k : ℕ) : ℕ := hParam n k + 6 * k + 12 + Nat.size (mParam n k) + Nat.size C

/-- The output arity `ℓ = (m + 1)·t`. -/
def arityParam (C n k : ℕ) : ℕ := (mParam n k + 1) * tParam C n k

theorem one_le_hParam (n k : ℕ) : 1 ≤ hParam n k := by unfold hParam; omega

/-- The grid `H^m` holds the message positions: `n ≤ m·h`. -/
theorem le_mParam_mul (n k : ℕ) : n ≤ mParam n k * hParam n k := by
  have h1 := one_le_hParam n k
  unfold mParam
  set h := hParam n k
  have := Nat.div_add_mod (n + h - 1) h
  have := Nat.mod_lt (n + h - 1) (show 0 < h by omega)
  have e : (n + h - 1) / h * h = h * ((n + h - 1) / h) := Nat.mul_comm _ _
  omega

theorem mParam_mul_le (n k : ℕ) : mParam n k * hParam n k ≤ n + hParam n k := by
  unfold mParam
  have := Nat.div_mul_le_self (n + hParam n k - 1) (hParam n k)
  omega

theorem mParam_le (n k : ℕ) : mParam n k ≤ n := by
  have h1 := one_le_hParam n k
  unfold mParam
  set h := hParam n k
  have h2 : n + h - 1 < (n + 1) * h := by
    have : n ≤ n * h := Nat.le_mul_of_pos_right n h1
    rw [add_mul, one_mul]; omega
  have := (Nat.div_lt_iff_lt_mul (show 0 < h by omega)).mpr h2
  omega

theorem size_le_hParam (n k : ℕ) : Nat.size n ≤ hParam n k := by unfold hParam; omega

/-- **Theorem 29's condition after rounding** (integer form): `C·d·2^(6k+12) < 2^t`. -/
theorem thm29_condition_nat (C n k : ℕ) : C * dParam n k * 2 ^ (6 * k + 12) < 2 ^ tParam C n k := by
  set h := hParam n k
  set m := mParam n k
  have hC : C < 2 ^ Nat.size C := Nat.lt_size_self C
  have hm : m < 2 ^ Nat.size m := Nat.lt_size_self m
  have hd : dParam n k ≤ m * 2 ^ h := by
    unfold dParam; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hCm : C * m < 2 ^ Nat.size C * 2 ^ Nat.size m := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0, zero_mul]; positivity
    · calc C * m < C * 2 ^ Nat.size m := Nat.mul_lt_mul_of_pos_left hm h0
        _ ≤ 2 ^ Nat.size C * 2 ^ Nat.size m := Nat.mul_le_mul_right _ hC.le
  have ht : 2 ^ tParam C n k = 2 ^ Nat.size C * 2 ^ Nat.size m * (2 ^ h * 2 ^ (6 * k + 12)) := by
    unfold tParam; rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [ht]
  calc C * dParam n k * 2 ^ (6 * k + 12) ≤ C * (m * 2 ^ h) * 2 ^ (6 * k + 12) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
    _ = C * m * (2 ^ h * 2 ^ (6 * k + 12)) := by ring
    _ < 2 ^ Nat.size C * 2 ^ Nat.size m * (2 ^ h * 2 ^ (6 * k + 12)) :=
        Nat.mul_lt_mul_of_pos_right hCm (by positivity)

/-- **Theorem 29's condition after rounding**: `c·√(d/|F|) < δ³` for every real `c` with `c² ≤ C`, where
`|F| = 2^t` and `δ = 2^(-k-2)` (STV text l.951 "provided ε > c√(d/|F|)", strict). -/
theorem thm29_condition (c : ℝ) (C n k : ℕ) (hcC : c ^ 2 ≤ C) :
    c * Real.sqrt ((dParam n k : ℝ) / 2 ^ tParam C n k) < dyadicAcc k ^ 3 := by
  have hδ : 0 < dyadicAcc k ^ 3 := pow_pos (dyadicAcc_pos k) 3
  rcases le_or_gt c 0 with hc | hc
  · have : c * Real.sqrt ((dParam n k : ℝ) / 2 ^ tParam C n k) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (Real.sqrt_nonneg _)
    linarith
  · rw [← lt_div_iff₀' hc, Real.sqrt_lt' (by positivity)]
    have hnat := thm29_condition_nat C n k
    have hreal : (C : ℝ) * dParam n k * 2 ^ (6 * k + 12) < 2 ^ tParam C n k := by exact_mod_cast hnat
    have hT : (0 : ℝ) < 2 ^ tParam C n k := by positivity
    have hd0 : (0 : ℝ) ≤ dParam n k := by positivity
    have e : (dyadicAcc k ^ 3 / c) ^ 2 = 1 / (c ^ 2 * 2 ^ (6 * k + 12)) := by
      unfold dyadicAcc
      field_simp
      ring
    rw [e, div_lt_div_iff₀ hT (by positivity)]
    have h1 : c ^ 2 * (dParam n k : ℝ) ≤ C * dParam n k := mul_le_mul_of_nonneg_right hcC hd0
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ (6 * k + 12))
    nlinarith

/-- **The output arity is `O(n + k)`**: `ℓ ≤ (44 + size C)·(n + k + 1)`. -/
theorem arity_le (C n k : ℕ) : arityParam C n k ≤ (44 + Nat.size C) * (n + k + 1) := by
  have hmh := mParam_mul_le n k
  have hm := mParam_le n k
  have hsm : Nat.size (mParam n k) ≤ hParam n k :=
    (Nat.size_le_size hm).trans (size_le_hParam n k)
  have hk : k ≤ hParam n k := by unfold hParam; omega
  have hh : hParam n k ≤ k + 2 + n := by
    have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n)); unfold hParam; omega
  have ht : tParam C n k ≤ 8 * hParam n k + 12 + Nat.size C := by unfold tParam; omega
  unfold arityParam
  set h := hParam n k
  set m := mParam n k
  set s := Nat.size C
  calc (m + 1) * tParam C n k ≤ (m + 1) * (8 * h + 12 + s) := Nat.mul_le_mul_left _ ht
    _ = 8 * (m * h) + (12 + s) * m + 8 * h + 12 + s := by ring
    _ ≤ 8 * (n + h) + (12 + s) * n + 8 * h + 12 + s := by
        have := Nat.mul_le_mul_left (12 + s) hm
        omega
    _ ≤ (44 + s) * (n + k + 1) := by nlinarith

/-! ## The binary-cube layout -/

/-- The codeword domain `F^m × 𝔽₂^t` (block, Hadamard position) laid out on `ℓ = (m+1)·t` bits. -/
def layoutEquiv (m t : ℕ) : (Fin m → Fin t → Bool) × (Fin t → Bool) ≃ (Fin ((m + 1) * t) → Bool) :=
  (Equiv.prodComm _ _).trans <| (Fin.consEquiv fun _ : Fin (m + 1) => Fin t → Bool).trans <|
    (Equiv.curry (Fin (m + 1)) (Fin t) Bool).symm.trans <| Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool)

/-- Counting along a bijection. -/
theorem card_filter_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter fun a => P (e a)).card := by
  rw [← card_map e.toEmbedding]
  congr 1
  ext b
  simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
  exact ⟨fun h => ⟨e.symm b, by simpa using h, by simp⟩, fun ⟨a, ha, hab⟩ => hab ▸ ha⟩

/-- The concatenated codeword of the inner symbols `Y` at a point of the domain. -/
def hadConcat {m t : ℕ} (Y : (Fin m → Fin t → Bool) → Fin t → Bool) (p : (Fin m → Fin t → Bool) × (Fin t → Bool)) :
    Bool :=
  had (Y p.1) p.2

/-- **The layout preserves agreement**: the agreement of a function `g` on `ℓ` bits with the laid-out codeword is
the sum over blocks of the Hadamard agreements of the blocks of `g`. -/
theorem card_agree_layout {m t : ℕ} (Y : (Fin m → Fin t → Bool) → Fin t → Bool)
    (g : (Fin ((m + 1) * t) → Bool) → Bool) :
    (univ.filter fun w => g w = hadConcat Y ((layoutEquiv m t).symm w)).card =
      ∑ z, agreeCount (fun u => g (layoutEquiv m t (z, u))) (Y z) := by
  rw [card_filter_equiv (layoutEquiv m t)]
  simp only [Equiv.symm_apply_apply]
  rw [card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  rw [agreeCount, card_filter]
  rfl

/-- The domain has `2^(t·m)·2^t = 2^ℓ` points. -/
theorem card_domain (m t : ℕ) :
    Fintype.card (Fin m → Fin t → Bool) * 2 ^ t = 2 ^ ((m + 1) * t) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]; congr 1; ring

end NearCubicGates.Adapters.Amplification
