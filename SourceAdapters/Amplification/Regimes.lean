import SourceAdapters.Amplification.GateAReconstruct
import SourceAdapters.Amplification.Shannon
import SourceAdapters.Amplification.Parity
import Proof.Gates.Main.Amplifier

/-!
# A04: the middle regime — strictness, the size inequality, and hardness from the reconstruction bound

`app:sources`, "Full-range amplification interface": "In the remaining regime `n^c < S = S(n) < U(n)` … A circuit of size at most `S^{1/c}` with
agreement at least `1/2 + ε` would have agreement strictly greater than `1/2 + δ`. After increasing the absolute
constant `A` to absorb `8^a`, reconstruction gives size at most `A n^a S^{(a+1)/c} + n + 2 < S`. The strict
inequality holds uniformly in this regime from a fixed onset: dividing by `S > n^c` bounds the left side by
`A/n^{c−2a−1} + (n+2)/n^c < 1`. This contradicts the premise and proves the required strict agreement bound."

* `ReconstructionBound C A a` is A02 ("An `s'`-node circuit agreeing with the encoded function on
  more than a `1/2 + δ` fraction yields an exact circuit for the original `n`-input function with at most
  `A(n/δ)^a s' + n + 2` nodes"), stated for the rounded code `stvEncode` with `n/δ = n·2^(k+2)`.
  `ReconstructionObligation` (`STV.Theorem29 → ∃ C A a, …`) is the A02 hypothesis; it is a
  hypothesis of `middle_regime_hard` only.
* `size_inequality`: for integers `c ≥ 2a + 2`, from the onset `n0 = 2A·8^a + 4`,
  `A(n·2^(k+2))^a·s' + n + 2 < S` whenever `n^c < S`, `2^(c(k−1)) < S` and `s' ≤ S^{1/c}` (the paper requires `c > 2a+2`;
  `c ≥ 2a + 2` suffices).
* `middle_regime_hard`: the target's `CannotBeApproximated` for `stvEncode` at `k = dyadicExp c S`, for every `f`
  without circuits of size `S`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open Finset Polynomial NearCubicWires NearCubicWires.Bindings.CLW20Lemma39 NearCubicGates.Published.STV

/-- **A02** for the rounded code: a circuit `B` with agreement more than `1/2 + δ` with `stvEncode msg` yields a
circuit for `msg` of at most `A·(n/δ)^a·|B| + n + 2` nodes, `1/δ = 2^(k+2)`. -/
def ReconstructionBound (C A a : ℕ) : Prop :=
  ∀ (n k : ℕ) (q : (ZMod 2)[X]) [Fact (Irreducible q)] (hq : q.Monic) (ht : q.natDegree = tParam C n k)
    (msg : BoolFunction n) (B : BooleanCircuit ((mParam n k + 1) * tParam C n k)),
    (1 / 2 + dyadicAcc k) * 2 ^ ((mParam n k + 1) * tParam C n k) <
      ((univ.filter fun w => B.eval w = stvEncode C n k hq ht msg w).card : ℝ) →
    HasCircuitOfSize msg (A * (n * 2 ^ (k + 2)) ^ a * B.size + n + 2)

/-- The A02 hypothesis: the reconstruction bound from the published Theorem 29. -/
def ReconstructionObligation : Prop :=
  Theorem29 → ∃ C A a : ℕ, ReconstructionBound C A a

/-- **The size inequality** (`app:sources`, "Full-range amplification interface"). -/
theorem size_inequality (A a c : ℕ) (hc : 2 * a + 2 ≤ c) (n : ℕ) (hn : 2 * A * 8 ^ a + 4 ≤ n)
    (S k s' : ℕ) (hS : (n : ℝ) ^ c < S) (hk : 2 ^ (c * (k - 1)) < S) (hk1 : 1 ≤ k)
    (hs : (s' : ℝ) ≤ (S : ℝ) ^ ((1 : ℝ) / c)) :
    A * (n * 2 ^ (k + 2)) ^ a * s' + n + 2 < S := by
  have hc0 : c ≠ 0 := by omega
  set σ := (S : ℝ) ^ ((1 : ℝ) / c) with hσ
  have hS0 : (0 : ℝ) ≤ S := by positivity
  have hσc : σ ^ c = S := by
    rw [hσ, one_div]; exact Real.rpow_inv_natCast_pow hS0 hc0
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnσ : (n : ℝ) < σ := by
    rw [← hσc] at hS
    exact lt_of_pow_lt_pow_left₀ c hσ0 hS
  have hkσ : (2 : ℝ) ^ (k - 1) < σ := by
    have : ((2 : ℝ) ^ (k - 1)) ^ c < σ ^ c := by
      rw [hσc, ← pow_mul, mul_comm]; exact_mod_cast hk
    exact lt_of_pow_lt_pow_left₀ c hσ0 this
  have h2k : (2 : ℝ) ^ (k + 2) = 8 * 2 ^ (k - 1) := by
    rw [show k + 2 = (k - 1) + 3 by omega, pow_add]; ring
  have hX : (n : ℝ) * 2 ^ (k + 2) ≤ 8 * n * σ := by rw [h2k]; nlinarith
  have hσ1 : (1 : ℝ) ≤ σ := by linarith
  -- the main term
  have hmain : (A : ℝ) * ((n : ℝ) * 2 ^ (k + 2)) ^ a * s' ≤ A * 8 ^ a * n ^ a * σ ^ (a + 1) := by
    have h1 : ((n : ℝ) * 2 ^ (k + 2)) ^ a ≤ (8 * n * σ) ^ a := pow_le_pow_left₀ (by positivity) hX a
    calc (A : ℝ) * ((n : ℝ) * 2 ^ (k + 2)) ^ a * s' ≤ A * (8 * n * σ) ^ a * σ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hs (by positivity) (by positivity)
      _ = A * 8 ^ a * n ^ a * σ ^ (a + 1) := by ring
  have hpow : (n : ℝ) ^ (a + 1) * σ ^ (a + 1) ≤ σ ^ c := by
    calc (n : ℝ) ^ (a + 1) * σ ^ (a + 1) ≤ σ ^ (a + 1) * σ ^ (a + 1) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnσ.le _) (by positivity)
      _ = σ ^ (2 * a + 2) := by rw [← pow_add]; ring_nf
      _ ≤ σ ^ c := pow_le_pow_right₀ hσ1 hc
  have hA : (2 : ℝ) * A * 8 ^ a ≤ n := by exact_mod_cast (show 2 * A * 8 ^ a ≤ n by omega)
  have hhalf1 : (A : ℝ) * 8 ^ a * n ^ a * σ ^ (a + 1) ≤ σ ^ c / 2 := by
    have : (A : ℝ) * 8 ^ a * n ^ a * σ ^ (a + 1) * (2 * n) ≤ σ ^ c * n := by
      calc (A : ℝ) * 8 ^ a * n ^ a * σ ^ (a + 1) * (2 * n) = (2 * A * 8 ^ a) * (n ^ (a + 1) * σ ^ (a + 1)) := by ring
        _ ≤ n * σ ^ c := mul_le_mul hA hpow (by positivity) (by positivity)
        _ = σ ^ c * n := by ring
    have hnpos : (0 : ℝ) < n := by linarith
    nlinarith
  have hhalf2 : (n : ℝ) + 2 < σ ^ c / 2 := by
    have h1 : (n : ℝ) ^ 2 ≤ n ^ c := pow_le_pow_right₀ hn1 (by omega)
    have h2 : (n : ℝ) ^ c < σ ^ c := pow_lt_pow_left₀ hnσ (by positivity) hc0
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
    nlinarith
  have hreal : (A : ℝ) * ((n : ℝ) * 2 ^ (k + 2)) ^ a * s' + n + 2 < S := by
    rw [← hσc]; linarith
  exact_mod_cast hreal

/-- `S^{1/c} > 0` reals and the strict passage from `1/2 + ε` to `1/2 + δ` (`app:sources`, "Full-range amplification interface"). -/
theorem agreement_strict (ε δ N x : ℝ) (hδε : δ < ε) (hN : 0 < N) (hx : (1 / 2 + ε) * N ≤ x) :
    (1 / 2 + δ) * N < x := by nlinarith

/-- **The middle regime is hard** (`app:sources`, "Full-range amplification interface"), given the reconstruction bound: with `k = dyadicExp c S`, the
rounded code of every `f` without circuits of size `S` cannot be `(1/2 + S^{-1/c})`-approximated by circuits of
size `S^{1/c}`. -/
theorem middle_regime_hard (C A a c : ℕ) (hc : 2 * a + 2 ≤ c) (hR : ReconstructionBound C A a)
    (n : ℕ) (hn : 2 * A * 8 ^ a + 4 ≤ n) (S : ℕ) (hS : (n : ℝ) ^ c < S)
    (q : (ZMod 2)[X]) [Fact (Irreducible q)] (hq : q.Monic)
    (ht : q.natDegree = tParam C n (dyadicExp c S (by omega))) (f : BoolFunction n)
    (hf : ¬ HasCircuitOfSize f S) :
    CannotBeApproximated (stvEncode C n (dyadicExp c S (by omega)) hq ht f)
      ((S : ℝ) ^ (-(1 : ℝ) / c)) ((S : ℝ) ^ ((1 : ℝ) / c)) := by
  have hc1 : 1 ≤ c := by omega
  set k := dyadicExp c S hc1
  have hS2 : 2 ≤ S := by
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
    have : (4 : ℝ) ≤ (n : ℝ) ^ c := by
      calc (4 : ℝ) ≤ n := h4
        _ = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ c := pow_le_pow_right₀ (by linarith) hc1
    have : (2 : ℝ) < S := by linarith
    exact_mod_cast this.le
  intro B hB
  by_contra hcon
  push Not at hcon
  have hδε : dyadicAcc k < (S : ℝ) ^ (-(1 : ℝ) / c) := by
    have h1 := dyadicAcc_le c S hc1 hS2
    have h2 := dyadicAcc_pos k
    linarith
  have hagr := agreement_strict _ _ _ _ hδε (by positivity) hcon
  have hrec := hR n k q hq ht f B (by
    have e : (univ.filter fun x => B.eval x = stvEncode C n k hq ht f x) =
        (univ.filter fun w => B.eval w = stvEncode C n k hq ht f w) := rfl
    rw [e] at hagr; exact hagr)
  have hlt := size_inequality A a c hc n hn S k B.size hS (two_pow_pred_lt c S hc1 hS2)
    (one_le_dyadicExp c S hc1 hS2) hB
  exact hf (NearCubicGates.Close.Amplifier.hasCircuitOfSize_mono hrec hlt.le)

end NearCubicGates.Adapters.Amplification
