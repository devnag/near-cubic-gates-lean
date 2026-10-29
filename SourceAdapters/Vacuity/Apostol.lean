import SourceAdapters.Base.Primes

/-!
# Vacuity and convention checks for the Apostol prime number theorem leaf

The leaf has no hypotheses, so it needs no satisfiability example. These checks pin the model
`primeCountingReal` ("the number of primes not exceeding x"):

* `primeCountingReal_two`: the endpoint is included (`π(2) = 1`), so the count is not the strict one.
* `primeCountingReal_lt_two`: no prime is counted below `2` (`π(3/2) = 0`), including non-natural arguments.
* `primeCountingReal_seven_ne_strict`: `π(7) = 4`, while Mathlib's strict count `Nat.primeCounting' 7 = 3`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.Apostol

open NearCubicGates.Published.Apostol

theorem primeCountingReal_lt_two : primeCountingReal (3 / 2) = 0 := by
  unfold primeCountingReal
  have hempty : {p : ℕ | p.Prime ∧ (p : ℝ) ≤ 3 / 2} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hle
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  rw [hempty, Set.ncard_empty]

theorem primeCountingReal_two : primeCountingReal 2 = 1 := by
  have h := NearCubicGates.Adapters.Base.primeCountingReal_natCast 2
  push_cast at h
  rw [h]
  decide

theorem primeCountingReal_seven_ne_strict :
    primeCountingReal 7 = 4 ∧ Nat.primeCounting' 7 = 3 := by
  have h := NearCubicGates.Adapters.Base.primeCountingReal_natCast 7
  push_cast at h
  rw [h]
  constructor <;> decide

end NearCubicGates.Adapters.Vacuity.Apostol
