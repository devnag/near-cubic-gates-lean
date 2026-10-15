import Proof.Gates.WorkerArith.TermK
import Proof.Gates.Target

/-!
# WeakWorker (abstract part): the runtime split from the component classes

Paper v2 lines 2403–2407: "`2^q q^{O(1)−μ_q} = o(T_clk(N))`". The worker's fuel is a polynomial part plus the counter
budgets of its calls (`termCost`: `10^13 (t+1)(Z+1)^4(B+1) + (300t + 6000)·bud`). With `Counter.fast`
(`budget · q^{μ(q)} ≤ 2^q` on admitted calls at `q = c.n`) and a call count polynomial in `q`, the hot part times any
fixed power `q^σ` is `O(2^q)`, because `μ(q) = ⌈lg ⌈lg q⌉⌉ → ∞`. Stated over abstract components until the composed
machine's cost shape lands (BRIEF2).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open scoped BigOperators

/-- `μ(q) ≥ K` once `q ≥ 2^(2^K)`. -/
theorem mu_ge (K q : ℕ) (hq : 2 ^ (2 ^ K) ≤ q) : K ≤ NearCubicGates.Target.mu q := by
  unfold NearCubicGates.Target.mu NearCubicGates.Target.lambda
  have h1 : 2 ^ K ≤ Nat.clog 2 q := by
    have := Nat.clog_mono_right 2 hq
    rwa [Nat.clog_pow 2 _ (by norm_num)] at this
  have h2 := Nat.clog_mono_right 2 h1
  rwa [Nat.clog_pow 2 _ (by norm_num)] at h2

/-- **The hot split.** `m N` counter calls, call `i` spending `bud N i ≤ 2^q / q^{μ(q)}`, `m N ≤ C (q+1)^c`,
`q → ∞`: then `(D Σ bud) · q^σ ≤ D C 2^q` eventually. -/
theorem hot_split (q m : ℕ → ℕ) (bud : ℕ → ℕ → ℕ) (D C c σ : ℕ)
    (hfast : ∃ onset, ∀ N, onset ≤ N → ∀ i < m N, bud N i * q N ^ NearCubicGates.Target.mu (q N) ≤ 2 ^ q N)
    (hm : ∀ N, m N ≤ C * (q N + 1) ^ c)
    (hq : ∀ K, ∃ N0, ∀ N, N0 ≤ N → K ≤ q N) :
    ∃ onset, ∀ N, onset ≤ N → (D * ∑ i ∈ Finset.range (m N), bud N i) * q N ^ σ ≤ D * C * 2 ^ q N := by
  obtain ⟨o1, h1⟩ := hfast
  obtain ⟨o2, h2⟩ := hq (2 ^ (2 ^ (σ + 2 * c)) + 2)
  refine ⟨max o1 o2, fun N hN => ?_⟩
  have hqN := h2 N (le_trans (le_max_right _ _) hN)
  set Q := q N with hQ
  have hQ2 : 2 ≤ Q := by have := Nat.one_le_two_pow (n := 2 ^ (σ + 2 * c)); omega
  have hmu : σ + 2 * c ≤ NearCubicGates.Target.mu Q := mu_ge _ Q (by omega)
  set S := ∑ i ∈ Finset.range (m N), bud N i with hS
  -- `S · Q^μ ≤ m · 2^Q`
  have hsum : S * Q ^ NearCubicGates.Target.mu Q ≤ m N * 2 ^ Q := by
    rw [hS, Finset.sum_mul]
    calc ∑ i ∈ Finset.range (m N), bud N i * Q ^ NearCubicGates.Target.mu Q
        ≤ ∑ _i ∈ Finset.range (m N), 2 ^ Q := Finset.sum_le_sum (fun i hi =>
          h1 N (le_trans (le_max_left _ _) hN) i (Finset.mem_range.mp hi))
      _ = m N * 2 ^ Q := by simp
  -- `(Q+1)^c ≤ Q^(2c)`
  have hQc : (Q + 1) ^ c ≤ Q ^ (2 * c) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by nlinarith) c
  have hpos : 0 < Q ^ (2 * c) := by positivity
  -- `S · Q^σ · Q^(2c) ≤ S · Q^μ`
  have hmono : S * Q ^ σ * Q ^ (2 * c) ≤ S * Q ^ NearCubicGates.Target.mu Q := by
    rw [mul_assoc, ← pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hmu)
  have hkey : S * Q ^ σ * Q ^ (2 * c) ≤ C * 2 ^ Q * Q ^ (2 * c) := by
    calc S * Q ^ σ * Q ^ (2 * c) ≤ m N * 2 ^ Q := hmono.trans hsum
      _ ≤ C * (Q + 1) ^ c * 2 ^ Q := Nat.mul_le_mul_right _ (hm N)
      _ ≤ C * Q ^ (2 * c) * 2 ^ Q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hQc)
      _ = C * 2 ^ Q * Q ^ (2 * c) := by ring
  have hcancel : S * Q ^ σ ≤ C * 2 ^ Q := Nat.le_of_mul_le_mul_right hkey hpos
  calc D * S * Q ^ σ = D * (S * Q ^ σ) := by ring
    _ ≤ D * (C * 2 ^ Q) := Nat.mul_le_mul_left _ hcancel
    _ = D * C * 2 ^ Q := by ring

/-- **The split, assembled** from a fuel decomposition (polynomial part + hot part) and a hot bound. -/
theorem split_of (fuel hot q : ℕ → ℕ) (A a B σ : ℕ)
    (hfuel : ∃ onset, ∀ N, onset ≤ N → fuel N + 2 ≤ A * (N + 1) ^ a + hot N)
    (hhot : ∃ onset, ∀ N, onset ≤ N → hot N * q N ^ σ ≤ B * 2 ^ q N) :
    ∃ onset, ∀ N, onset ≤ N → fuel N + 2 ≤ A * (N + 1) ^ a + hot N ∧ hot N * q N ^ σ ≤ B * 2 ^ q N := by
  obtain ⟨o1, h1⟩ := hfuel
  obtain ⟨o2, h2⟩ := hhot
  exact ⟨max o1 o2, fun N hN => ⟨h1 N (le_trans (le_max_left _ _) hN), h2 N (le_trans (le_max_right _ _) hN)⟩⟩

end NearCubicGates.Close.WorkerArith
