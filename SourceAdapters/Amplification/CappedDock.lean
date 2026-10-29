import SourceAdapters.Joins.CappedRun
import Proof.Foundations.OrdinaryMachine

/-!
# Dock of the X8 join (`CappedRun`) for input 8 (A05)

`app:sources`, "Full-range amplification interface": "Fix a time constructor computing `S(n)` from unary `n` within `C(S(n)+1)` steps. For `n ≥ n0`,
run it for only `C(U(n)+1)` simulated steps. A timeout implies `S(n) > U(n)`; a returned value at least `U(n)` also
selects the constant output. Otherwise the returned value determines the cases above."

The time constructor is the program `p` of `TimeConstructible S` (`Statement.lean:1033`). The join's
`CappedWordRun` turns `p` into an ordinary word function on `(cap, 1^n)` writing `frame (cappedResultWord p (cap, 1^n))`
within `C'·(cap + n + 1)` steps. `cappedResult_cases` reads that word exactly as the paper does:

* either the run returned, and the word is `true :: frame (S(n) in binary)` (the constructor's own output: an
  ordinary run is deterministic, `run_moreFuel`);
* or it timed out, the word is `false :: frame []`, and `cap < C·(S(n)+1)`; with `cap = C·(U(n)+1)` this is
  `S(n) > U(n)` (`timeout_gt`).

`cappedConstructor`: from `CappedRun` and `TimeConstructible S`, one word function with linear budget
`C'·(cap + n + 1)` and this reading. With `cap = C(U(n)+1)`, `U(n) = 2^(n+3)`, the budget is `2^{O(n)}`.
**DOCK CappedRun: OK.**
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicGates.Adapters.Joins
open NearCubicWires.Bindings.CLW20Theorem113

/-- **The capped result of a time constructor.** If `p` writes `v` within `B` steps, then the capped result word
at cap `cap` is `true :: frame v`, or it is `false :: frame []` and `cap < B`. -/
theorem cappedResult_cases (p : Program) (w v : List Bool) (B : ℕ)
    (hp : ∃ receipt, run p.machine B (p.inputTapes w) = some receipt ∧ receipt.final.tapes p.outputTape = v)
    (cap : ℕ) :
    cappedResultWord p (cap, w) = true :: frame v ∨ (cappedResultWord p (cap, w) = false :: frame [] ∧ cap < B) := by
  obtain ⟨receipt, hrun, hout⟩ := hp
  unfold cappedResultWord
  simp only
  cases hc : run p.machine cap (p.inputTapes w) with
  | none =>
      right
      refine ⟨rfl, ?_⟩
      by_contra hle
      push Not at hle
      have := run_moreFuel p.machine B (cap - B) _ receipt hrun
      rw [Nat.add_sub_of_le hle, hc] at this
      cases this
  | some r =>
      left
      have h1 := run_moreFuel p.machine cap B _ r hc
      have h2 := run_moreFuel p.machine B cap _ receipt hrun
      rw [Nat.add_comm] at h2
      rw [h1] at h2
      cases h2
      show true :: frame (receipt.final.tapes p.outputTape) = true :: frame v
      rw [hout]

/-- A timeout at cap `C·(U+1)` of a constructor running within `C·(S+1)` steps means `S > U`. -/
theorem timeout_gt (C U S : ℕ) (h : C * (U + 1) < C * (S + 1)) : U < S := by
  have := lt_of_mul_lt_mul_left h
  omega

/-- **The capped time constructor** (`app:sources`, "Full-range amplification interface"): one ordinary word function on `(cap, 1^n)` with budget
`C'·(cap + n + 1)` whose framed result is the constructor's value `S(n)` in binary, or a timeout implying
`cap < C·(S(n)+1)`. -/
theorem cappedConstructor (hX8 : CappedRun) {S : ℕ → ℕ} (hS : TimeConstructible S) :
    ∃ (C C' : ℕ) (p : Program), 0 < C ∧ 1 ≤ C' ∧
      Nonempty (WordFunction CappedRequest cappedRequestWord (fun r => frame (cappedResultWord p r))
        (fun r => C' * (r.1 + r.2.length + 1))) ∧
      ∀ n cap : ℕ, cappedResultWord p (cap, List.replicate n true) = true :: frame (S n).bits ∨
        (cappedResultWord p (cap, List.replicate n true) = false :: frame [] ∧ cap < C * (S n + 1)) := by
  obtain ⟨C, hC, ⟨F⟩⟩ := hS
  obtain ⟨C', hC', hW⟩ := hX8.2 F.program
  refine ⟨C, C', F.program, hC, hC', hW, fun n cap => ?_⟩
  exact cappedResult_cases F.program _ _ _ (F.realizes n) cap

end NearCubicGates.Adapters.Amplification
