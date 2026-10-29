import NineInputs
import SourceAdapters.ShortPCP.LemmaC1

/-!
# Randomness and proof length of one sub-verifier run

The proof of `thm:short-pcp-ours`, Step 2(a), combines BCGT13 Lemmas C.2–C.5
with the proved fixed-tuple recursion bounds of `lem:rs-recursion`.
For the transcribed verifiers, every branch of `vRS` uses `rand_{RS,=}(κ)` or
κ coins and at most `(2^η+1)(2^κ+2·length_{RS,=}(κ))` proof elements; `vVRS`
adds κ coins and 2^κ elements. The degree hypotheses bound the number of blocks.

At the tuple `(2,4,0,1)`, the internal theorem `lemmaC1` in `LemmaC1.lean`
proves the needed bounds on `rand_{RS,=}` and `length_{RS,=}`. The general
published Lemma C.1 is not a premise of this module.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open NearCubicGates.Published.BCGT13

variable {F : Type} [Field F] [DecidableEq F]

/-- `m_{κ,η,d} ≤ 2^η` for `d < 2^κ`, `η ≤ κ` (Algorithm 14 notes: "b(d+1)/(d_{κ,η}+1)c ∈ {0, …, 2^η}"). -/
theorem mKED_le (κ η d : ℕ) (hηκ : η ≤ κ) (hd : d < 2 ^ κ) : mKED κ η d ≤ 2 ^ η := by
  unfold mKED dKE
  have hsplit : 2 ^ κ = 2 ^ (κ - η) * 2 ^ η := by rw [← pow_add, Nat.sub_add_cancel hηκ]
  have hdiv : 2 ^ κ / 2 ^ η = 2 ^ (κ - η) := by
    rw [hsplit, Nat.mul_div_cancel _ (by positivity)]
  rw [hdiv, Nat.sub_add_cancel (Nat.one_le_two_pow)]
  apply Nat.div_le_of_le_mul
  rw [← hsplit]
  omega

/-- Every branch of `V_RS` uses at most `max(rand_{RS,=}(κ), κ)` coins (Lemmas C.2–C.4 as computations). -/
theorem vRS_rand_le (T : Tuple) (B : List F) (O : F) (d : ℕ) :
    (vRS T B O d).rand ≤ max (randEq T B.length) B.length := by
  unfold vRS
  split_ifs
  · simp
  · simp [vLt]
  · simp [vEq]
  · simp only [vGt]
    split <;> omega

/-- `V_VRS` uses at most `max(rand_{RS,=}(κ), κ)` coins (Lemma C.5 as a computation). -/
theorem vVRS_rand_le (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) :
    (vVRS T B O BH OH d).rand ≤ max (randEq T B.length) B.length := by
  simp only [vVRS]
  have := vRS_rand_le T B O (d - 2 ^ BH.length)
  omega

/-- Every branch of `V_RS` has a proof of at most `(2^η + 1)(2^κ + 2·length_{RS,=}(κ))` field elements. -/
theorem vRS_length_le (T : Tuple) (B : List F) (O : F) (d : ℕ) (hd : d < 2 ^ B.length) :
    (vRS T B O d).length ≤ (2 ^ T.η + 1) * (2 ^ B.length + 2 * lengthEq T B.length) := by
  have hbase : 2 * lengthEq T B.length ≤ (2 ^ T.η + 1) * (2 ^ B.length + 2 * lengthEq T B.length) := by
    nlinarith [Nat.one_le_two_pow (n := T.η)]
  unfold vRS
  split_ifs with h1 h2 h3
  · simp
  · simpa [vLt] using hbase
  · simp only [vEq]; omega
  · simp only [vGt]
    have hm := mKED_le B.length T.η d (by omega) hd
    have hm' : mKED B.length T.η d * (2 ^ B.length + lengthEq T B.length) ≤
        2 ^ T.η * (2 ^ B.length + 2 * lengthEq T B.length) :=
      Nat.mul_le_mul hm (by omega)
    split
    · simp only [vLt]; nlinarith
    · nlinarith

/-- `V_VRS` has a proof of at most `2^κ + (2^η + 1)(2^κ + 2·length_{RS,=}(κ))` field elements. -/
theorem vVRS_length_le (T : Tuple) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) (hd : d < 2 ^ B.length) :
    (vVRS T B O BH OH d).length ≤ 2 ^ B.length + (2 ^ T.η + 1) * (2 ^ B.length + 2 * lengthEq T B.length) := by
  simp only [vVRS]
  have := vRS_length_le T B O (d - 2 ^ BH.length) (lt_of_le_of_lt (Nat.sub_le _ _) hd)
  omega

/-- **Item 1 for one run** (proof of `thm:short-pcp-ours`) at the tuple `(2, 4, 0, 1)`: by the proved fixed-tuple recursion (`lemmaC1`; `lem:rs-recursion`),
`max(rand_{RS,=}(κ), κ) ≤ κ + (μ+2)·log₂(2κ) = κ + 3·log₂(2κ)`. -/
theorem rand_le_of_C1 (κ : ℕ) (hκ : 1 ≤ κ) :
    ((max (randEq ⟨2, 4, 0, 1⟩ κ) κ : ℕ) : ℝ) ≤ κ + 3 * Real.logb 2 (2 * κ) := by
  have hr := (lemmaC1 κ hκ).1
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hlog : 0 ≤ Real.logb 2 (2 * κ) := Real.logb_nonneg (by norm_num) (by linarith)
  rcases le_total (randEq ⟨2, 4, 0, 1⟩ κ) κ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; exact hr

/-- **Item 2 for one run** (proof of `thm:short-pcp-ours`) at the tuple `(2, 4, 0, 1)` (`η = 2`): by the proved fixed-tuple recursion (`lemmaC1`; `lem:rs-recursion`),
`2^κ + (2^η+1)(2^κ + 2·length_{RS,=}(κ)) ≤ (3·2^η + 4)·2^κ·κ^{1+max(μ+1−γ,γ)} = 16·2^κ·κ^3`, a bound on both
`V_RS` and `V_VRS` proofs. -/
theorem length_le_of_C1 (κ : ℕ) (hκ : 1 ≤ κ) :
    2 ^ κ + (4 + 1) * (2 ^ κ + 2 * lengthEq ⟨2, 4, 0, 1⟩ κ) ≤ (3 * 4 + 4) * (2 ^ κ * κ ^ 3) := by
  have hl := (lemmaC1 κ hκ).2
  have hpow : 1 ≤ κ ^ 3 := Nat.one_le_pow _ _ hκ
  have h2 : 2 ^ κ ≤ 2 ^ κ * κ ^ 3 := Nat.le_mul_of_pos_right _ hpow
  set P := 2 ^ κ * κ ^ 3
  have : (4 + 1) * (2 ^ κ + 2 * lengthEq ⟨2, 4, 0, 1⟩ κ) ≤ (4 + 1) * (3 * P) :=
    Nat.mul_le_mul_left _ (by omega)
  nlinarith

end NearCubicGates.Adapters.ShortPCP
