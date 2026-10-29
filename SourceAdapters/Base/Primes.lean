import NineInputs

/-!
# Field 4 (`primes`) from the prime number theorem as stated by Apostol

Consumer: `NineInputs.primes : NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem`
(`Statement.lean` §26): for every `ε > 0` an onset `≥ 2` beyond which `|π(n) log n / n − 1| < ε` at every
natural `n`.

Paper:
- `sec:windows`, "How many useful primes are available?" (subsection "How many useful primes are available?"): "For an integer \(P\ge3\), let
  \(\cP\) consist of all primes in \((P/2,P]\). Only the order of magnitude of this set is needed."
- proof of `lem:primes`: "By the prime number theorem~\cite[Chapters~4 and~13]{Apostol76}, the
  interval \((P/2,P]\) contains \((1+o(1))P/(2\ln P)\) primes". The dyadic count is derived downstream
  (`Proof/Gates/Counter/Eventual.lean`) from the natural-argument form proved here.
- `app:sources` (app:sources): "Prime number theorem \cite[Chapters~4 and~13]{Apostol76} … Derived".

Steps:
1. `primeCountingReal_natCast`: at a natural argument the real-argument count is `Nat.primeCounting n` (primes
   `≤ n`), not `Nat.primeCounting'` (primes `< n`).
2–3. Compose the real limit with `Nat.cast : ℕ → ℝ` (`tendsto_natCast_atTop_atTop`) and unpack it metrically.
4. Raise the onset to at least `2`; the strict inequality comes from the open ball.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Base

open NearCubicGates.Published.Apostol

/-- Step 1: at a natural argument `n` the real-argument prime count is `Nat.primeCounting n`, the
number of primes `≤ n`. -/
theorem primeCountingReal_natCast (n : ℕ) : primeCountingReal (n : ℝ) = Nat.primeCounting n := by
  unfold primeCountingReal
  have hset : {p : ℕ | p.Prime ∧ (p : ℝ) ≤ (n : ℝ)} = ((Nat.primesLE n : Finset ℕ) : Set ℕ) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primesLE, Nat.cast_le]
    exact and_comm
  rw [hset, Set.ncard_coe_finset, Nat.primesLE_card_eq_primeCounting]

/-- Steps 2–3: the source limit along natural arguments. -/
theorem tendsto_primeCounting_natCast (h : primeNumberTheorem) :
    Filter.Tendsto (fun n : ℕ => (Nat.primeCounting n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 1) := by
  have hcomp := h.comp tendsto_natCast_atTop_atTop
  refine hcomp.congr fun n => ?_
  simp only [Function.comp_apply, primeCountingReal_natCast]

/-- **Field 4.** Apostol's prime number theorem (real-argument limit, p. 74) implies `NineInputs.primes`
(natural arguments, an onset `≥ 2` for each `ε`, strict absolute error). `sec:windows`, "How many useful primes are available?" (`lem:primes` and its
proof). -/
theorem primes_of_primeNumberTheorem (h : primeNumberTheorem) :
    NearCubicGates.PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (tendsto_primeCounting_natCast h) epsilon hepsilon
  refine ⟨max N 2, le_max_right N 2, fun n hn => ?_⟩
  have hd := hN n (le_trans (le_max_left N 2) hn)
  rwa [Real.dist_eq] at hd

end NearCubicGates.Adapters.Base
