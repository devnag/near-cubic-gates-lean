import NineInputs

/-!
# The uniform step cap fits every promised machine eventually (input 7, step F03 arithmetic)

Paper context: `lem:multitape-refuter`, Step 2, and “Uniform setup cost” in the proof of
`cor:framed-refuter`. A useful branch costs at most `c_0 N + a_M + 2 b_M (t_M(N)+1)`, with `c_0`
independent of `M` and `a_M, b_M` allowed to depend on `M`. This is eventually smaller than the uniform
cap `(c_0+2)(T(N)+1)` because `N ≤ T(N)` and `t_M(N) = o(T(N))`. In particular, the coefficient of
the initial data length is uniform in `M`; the same argument covers linear clocks.

`useful_branch_fits_cap` is that inequality with the exact natural-number little-o predicate of the
consumer (`OrdinaryLittleO`, `L/Statement.lean:623`) and the clock-range half `∀ n, n ≤ T n` of
`InClockRange` (`L/Statement.lean:1038`). The order of quantifiers carries the content: `c0` is
fixed before `M`; `a`, `b` and the onset are chosen after `M`. Neither monotonicity of `T` nor
`T(N)/N → ∞` is assumed.

`dependent_setup_fails` records why the order matters when `T(N) = N`.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.RepairSource

set_option autoImplicit false

/-- **The useful branch fits the uniform cap** (proof of `cor:framed-refuter`). For every clock with `N ≤ T(N)`,
every setup coefficient `c0` fixed before the machine, every promised weak machine `M` and every
machine-dependent constants `a`, `b`, the useful branch cost `c0·N + a + 2b(t_M(N)+1)` is strictly
below the cap `(c0+2)(T(N)+1)` from some onset on. Here `t_M = M.runtime`, the declared bound
that `M.halts` makes good on every input and witness. -/
theorem useful_branch_fits_cap (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (c0 : ℕ)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M T) (a b : ℕ) :
    ∃ onset, ∀ N, onset ≤ N →
      c0 * N + a + 2 * b * (M.runtime N + 1) < (c0 + 2) * (T N + 1) := by
  obtain ⟨onset, hon⟩ := hM (2 * b + 1) (by omega)
  refine ⟨max onset (a + 2 * b + 1), fun N hN => ?_⟩
  have h1 : (2 * b + 1) * M.runtime N ≤ T N := hon N (le_of_max_le_left hN)
  have h2 : a + 2 * b + 1 ≤ N := le_of_max_le_right hN
  have h3 : N ≤ T N := hT N
  have h4 : 2 * b * M.runtime N ≤ T N := by
    have : 2 * b * M.runtime N ≤ (2 * b + 1) * M.runtime N :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h5 : c0 * N ≤ c0 * T N := Nat.mul_le_mul_left _ h3
  have h6 : 2 * b * (M.runtime N + 1) = 2 * b * M.runtime N + 2 * b := by ring
  have h7 : (c0 + 2) * (T N + 1) = c0 * T N + c0 + 2 * T N + 2 := by ring
  omega

/-- The same statement with the cap's onset taken uniformly over finitely many verdicts: two useful
simulations (proof of `lem:multitape-refuter`: the rejecting-verdict run and the accepting-verdict run) are covered by
the factor 2 already present in `2·b`. This corollary spells out the two-run sum. -/
theorem two_runs_fit_cap (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (c0 : ℕ)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M T) (a b : ℕ) :
    ∃ onset, ∀ N, onset ≤ N →
      c0 * N + a + b * (M.runtime N + 1) + b * (M.runtime N + 1) < (c0 + 2) * (T N + 1) := by
  obtain ⟨onset, h⟩ := useful_branch_fits_cap T hT c0 M hM a b
  refine ⟨onset, fun N hN => ?_⟩
  have := h N hN
  have e : 2 * b * (M.runtime N + 1) = b * (M.runtime N + 1) + b * (M.runtime N + 1) := by ring
  omega

/-- **Why `c0` must not depend on the machine**. At the linear clock `T(N) = N`, a
setup cost `(c0+3)·N` — a coefficient larger than the cap's — exceeds the cap `(c0+2)(T(N)+1)` at
every length `N ≥ c0+2`, whatever `t_M` is. So the eventual fit of `useful_branch_fits_cap` fails
if the coefficient of `N` in the useful branch is allowed to grow with `M`. -/
theorem dependent_setup_fails (c0 : ℕ) :
    ∀ onset, ∃ N, onset ≤ N ∧ (c0 + 2) * ((fun n : ℕ => n) N + 1) ≤ (c0 + 3) * N := by
  intro onset
  refine ⟨max onset (c0 + 2), le_max_left _ _, ?_⟩
  have h : c0 + 2 ≤ max onset (c0 + 2) := le_max_right _ _
  simp only
  nlinarith

/-- The linear clock is in the consumer's range half `∀ n, n ≤ T n`. -/
theorem linear_clock_in_range : ∀ n : ℕ, n ≤ (fun n : ℕ => n) n := fun _ => le_rfl

end NearCubicGates.Adapters.Refuter
