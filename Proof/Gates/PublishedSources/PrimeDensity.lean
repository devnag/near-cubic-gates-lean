import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import StatementSupport

/-! This module only imports: its definitions are part of the trusted statement, `Statement.lean`. -/

/-!
# Input 4: the prime number theorem

This file only defines the proposition: the prime number theorem is assumed as an input, not proved here.

Source: Tom M. Apostol, Introduction to Analytic Number Theory (1976),
Chapter 4, pp. 74--105, and Chapter 13, pp. 278--303.
https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_5
https://link.springer.com/chapter/10.1007/978-1-4757-5579-4_14

The Chapter 4 publisher abstract states the limit
  pi(x) log(x) / x -> 1.
The definition below restricts that published limit to natural arguments
and spells out the epsilon/onset quantifiers. `Nat.primeCounting n` counts
primes at most n, and `Real.log` is the natural logarithm.

Dyadic-count bounds, the prime list, largest-candidate selection, the lift
exponent, public guards, windows, word bounds, and ordinary execution remain
local adapter obligations. No such obligation appears as a source premise.
-/

set_option autoImplicit false

namespace NearCubicGates.PublishedSources.PrimeDensity

end NearCubicGates.PublishedSources.PrimeDensity
