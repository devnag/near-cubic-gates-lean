import Proof.Foundations.SourceInterfaces
import StatementSupport

/-!
# Binding: RS62 Theorem 4, eq. (3.14) → `PrimeThetaBoundContract`

Source PDF: `RS62_Rosser_Schoenfeld_Approximate_Formulas_Prime_Functions.pdf`
(its text layer is garbled; every quotation below was checked against the rendered page image).

* PDF page 1 (printed p.64), §2 Introduction:
  "Counting 2 as the first prime, we denote by π(x), ϑ(x), and ψ(x), respectively, the number
  of primes ≦ x, the logarithm of the product of all primes ≦ x, and the logarithm of the least
  common multiple of all positive integers ≦ x; if x < 2, we take π(x) = ϑ(x) = ψ(x) = 0. …
  Throughout, n shall denote a positive integer, p a prime, and x a real number."
* PDF page 3 (printed p.66): "(2.15) li(x) = Ei(log x)", with "(2.16)
  Ei(y) = lim_{ε→0+} {∫_{−∞}^{−ε} e^t dt/t + ∫_ε^y e^t dt/t}" and "(2.17)
  ∫_2^x dy/log y = li(x) − li(2)". (2.17) differentiates correctly only when `e^{log x} = x`,
  so `log` is the NATURAL logarithm: `Real.log`.
* PDF page 7 (printed p.70): "THEOREM 4. We have (3.14) x(1 − 1/(2 log x)) < ϑ(x) for
  563 ≦ x,".

Transcription choices: `x` is real (as the paper says); "the product of all primes ≤ x" is the
`finprod` over the set `{p : ℕ | p.Prime ∧ (p : ℝ) ≤ x}` (no floor appears in the literal); the
paper's convention "if x < 2, we take ϑ(x) = 0" is a consequence, proved as
`theta_eq_zero_of_lt_two` (empty product, `log 1 = 0`).

Self-contained: the step from (3.14) to the two-clause import is `rs62_prime_contract_iff`
below, which states (3.14) with the import's `chebyshevTheta`. This module adds `rs62_theta_eq` (the literal
`ϑ` IS `chebyshevTheta`, for every real `x`) and composes. It imports only
`Proof.Foundations.SourceInterfaces`.
-/

namespace NearCubicWires.Bindings.RS62

open NearCubicWires NearCubicWires.SourceInterfaces
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-- The set of primes `≤ x` is the import's finite range `range (⌊x⌋₊ + 1)` filtered by
primality, for EVERY real `x`. -/
theorem primes_le_eq (x : ℝ) :
    {p : ℕ | p.Prime ∧ (p : ℝ) ≤ x} =
      (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime : Finset ℕ) : Set ℕ) := by
  ext p
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hp, hle⟩
    exact ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hle, hp⟩
  · rintro ⟨hle, hp⟩
    exact ⟨hp, (Nat.le_floor_iff' hp.ne_zero).mp hle⟩

/-- The literal `ϑ` equals the import's `chebyshevTheta`, for every real `x`. -/
theorem rs62_theta_eq (x : ℝ) : theta x = chebyshevTheta x := by
  unfold theta chebyshevTheta
  rw [primes_le_eq, finprod_mem_coe_finset, Real.log_prod]
  intro p hp
  exact Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero

/-- RS62's convention "if x < 2, we take ϑ(x) = 0" holds for the literal definition. -/
theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : theta x = 0 := by
  rw [rs62_theta_eq]
  unfold chebyshevTheta
  refine Finset.sum_eq_zero fun p hp => ?_
  exfalso
  obtain ⟨hr, hprime⟩ := Finset.mem_filter.mp hp
  have hfl : ⌊x⌋₊ < 2 := (Nat.floor_lt' (by norm_num)).mpr (by exact_mod_cast hx)
  have h2 := hprime.two_le
  have hlt := Finset.mem_range.mp hr
  omega

/-- `log x > 1` on `x ≥ 563`. -/
theorem one_lt_log_of_563_le {x : ℝ} (hx : 563 ≤ x) : 1 < Real.log x := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The imported prime contract says exactly (3.14) stated with `chebyshevTheta`: its `x / 3`
clause is an elementary consequence on the same domain. -/
theorem rs62_prime_contract_iff :
    PrimeThetaBoundContract ↔
      ∀ x : ℝ, 563 ≤ x → x * (1 - 1 / (2 * Real.log x)) < chebyshevTheta x := by
  constructor
  · intro h x hx
    exact (h x hx).1
  · intro h x hx
    refine ⟨h x hx, ?_⟩
    have hlog := one_lt_log_of_563_le hx
    have htwo : (2 : ℝ) ≤ 2 * Real.log x := by linarith
    have hinv : 1 / (2 * Real.log x) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) htwo
    have hxpos : 0 < x := by linarith
    have hmain : x / 3 ≤ x * (1 - 1 / (2 * Real.log x)) := by
      have hfac : (1 : ℝ) / 3 ≤ 1 - 1 / (2 * Real.log x) := by linarith
      calc x / 3 = x * (1 / 3) := by ring
        _ ≤ x * (1 - 1 / (2 * Real.log x)) := mul_le_mul_of_nonneg_left hfac hxpos.le
    exact hmain.trans (h x hx).le

/-- **Adapter.** The literal RS62 (3.14) implies the imported `PrimeThetaBoundContract`
(its extra `x / 3 ≤ ϑ(x)` clause is an elementary consequence on `x ≥ 563`). -/
theorem rs62_to_import : RS62_Theorem4_eq314 → PrimeThetaBoundContract := by
  intro h
  refine rs62_prime_contract_iff.mpr ?_
  intro x hx
  rw [← rs62_theta_eq]
  exact h x hx

/-- The converse also holds: the import says no more than (3.14). -/
theorem import_to_rs62 : PrimeThetaBoundContract → RS62_Theorem4_eq314 := by
  intro h x hx
  rw [rs62_theta_eq]
  exact rs62_prime_contract_iff.mp h x hx

end NearCubicWires.Bindings.RS62
