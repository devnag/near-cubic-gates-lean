import NineInputs

/-!
# W01: the exact-power instances of Williams' dimension `N^{.1}`

Restrict to `N=k^10`, inner dimension `k`. This weakens the source range and avoids interpreting a
fractional matrix dimension. The leaf `RectangularProductLeaf` reads `N^{.1}` as the real power `(N:ℝ)^(1/10)`;
the consumer `Williams14_Corollary4_4` (`Statement.lean:1141`) quantifies over `N = k^10` with inner dimension `k`.
 (`imp:batch`): "multiplies over the integers any two \(0\)-\(1\) matrices of dimensions
\(N\times\ceil{N^{0.1}}\) and \(\ceil{N^{0.1}}\times N\)"; at `N = k^10` every reading (real power, ceiling, floor)
gives `k`.
-/

namespace NearCubicGates.Adapters.Williams

open NearCubicGates.Published.Williams

set_option autoImplicit false

/-- At `N = k^10` the real power `N^{1/10}` is `k`. -/
theorem tenthRoot_pow (k : ℕ) : (k : ℝ) = ((k ^ 10 : ℕ) : ℝ) ^ (1 / 10 : ℝ) := by
  have h : (1 / 10 : ℝ) = ((10 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h, Nat.cast_pow]
  exact (Real.pow_rpow_inv_natCast (Nat.cast_nonneg k) (by norm_num)).symm

/-- The leaf at the exact-power instances: `N = k^10`, inner dimension `k`. -/
theorem leaf_at_powers (h : RectangularProductLeaf) :
    ∃ (M : MultitapeTM) (inputTape outputTape : Fin M.tapes) (C e N₀ : ℕ),
      ∀ (k : ℕ), N₀ ≤ k ^ 10 →
      ∀ (A : Fin (k ^ 10) → Fin k → Bool) (B : Fin k → Fin (k ^ 10) → Bool),
        ∃ (t : ℕ) (c : M.Configuration),
          M.run t (M.initial inputTape (inputWord A B)) = some c ∧ M.step c = none ∧
          (t : ℝ) ≤ (C : ℝ) * ((k ^ 10 : ℕ) : ℝ) ^ 2 * Real.logb 2 ((k ^ 10 : ℕ) : ℝ) ^ e ∧
          c.contents outputTape = fun p => (outputWord (integerProduct A B)).getD p Symbol.blank := by
  obtain ⟨M, i, o, C, e, N₀, hM⟩ := h
  exact ⟨M, i, o, C, e, N₀, fun k hk A B => hM (k ^ 10) k hk (tenthRoot_pow k) A B⟩

end NearCubicGates.Adapters.Williams
