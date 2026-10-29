import Proof.Gates.Counter.Params
import Proof.Gates.PublishedSources.PrimeDensity
import Proof.Gates.QuantitativePairWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational

/-!
# Counter module 6/9 — lem:asymptotics, part 1, with lem:primes from the prime number theorem
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates

/-! ## Log domination -/

theorem polynomial_le_binary (K d : ℕ) :
    ∃ onset : ℕ, 1 ≤ onset ∧ ∀ q : ℕ, onset ≤ q → K * q ^ d ≤ 2 ^ q := by
  have logPositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let epsilon : ℝ := (Real.log 2) ^ d / (K + 1)
  have epsilonPositive : 0 < epsilon := by dsimp [epsilon]; positivity
  obtain ⟨a, bound⟩ := Filter.eventually_atTop.mp
    ((Real.isLittleO_pow_exp_atTop (n := d)).def epsilonPositive)
  refine ⟨max 1 ⌈a / Real.log 2⌉₊, le_max_left _ _, ?_⟩
  intro q large
  have ceilBound : ⌈a / Real.log 2⌉₊ ≤ q := (le_max_right _ _).trans large
  have realBound : a / Real.log 2 ≤ (q : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ceilBound)
  have argument : a ≤ (q : ℝ) * Real.log 2 := (div_le_iff₀ logPositive).mp realBound
  have estimate := bound ((q : ℝ) * Real.log 2) argument
  have expIdentity : Real.exp ((q : ℝ) * Real.log 2) = (2 : ℝ) ^ q := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((q : ℝ) * Real.log 2) ^ d),
    expIdentity, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ q)] at estimate
  have denominatorPositive : (0 : ℝ) < K + 1 := by positivity
  have scalePositive : 0 < (Real.log 2) ^ d := pow_pos logPositive _
  have paid : ((K : ℝ) + 1) * (q : ℝ) ^ d ≤ (2 : ℝ) ^ q := by
    have multiply := (le_div_iff₀ denominatorPositive).mp
      (show ((q : ℝ) * Real.log 2) ^ d ≤
        ((Real.log 2) ^ d * (2 : ℝ) ^ q) / ((K : ℝ) + 1) by
          simpa only [epsilon, div_mul_eq_mul_div] using estimate)
    have cancel : (Real.log 2) ^ d * (((K : ℝ) + 1) * (q : ℝ) ^ d) ≤
        (Real.log 2) ^ d * (2 : ℝ) ^ q := by
      simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using multiply
    exact (mul_le_mul_iff_right₀ scalePositive).mp (by
      simpa only [mul_comm] using cancel)
  have actual : (K : ℝ) * (q : ℝ) ^ d ≤ (2 : ℝ) ^ q := by
    have nonnegative : (0 : ℝ) ≤ (q : ℝ) ^ d := by positivity
    nlinarith
  exact_mod_cast actual

theorem polynomial_lambda_binary (K d : ℕ) :
    ∃ onset : ℕ, 65536 ≤ onset ∧ ∀ n : ℕ, onset ≤ n →
      16 ≤ Target.lambda n ∧ K * (Target.lambda n) ^ d ≤
        2 ^ (Target.lambda n / 4) := by
  obtain ⟨a, positive, bound⟩ := polynomial_le_binary (K * 8 ^ d) d
  let b := max 4 a
  refine ⟨2 ^ (4 * b), ?_, ?_⟩
  · have large : 16 ≤ 4 * b := by dsimp [b]; omega
    have powers := Nat.pow_le_pow_right (by decide : 0 < 2) large
    norm_num at powers
    exact powers
  intro n large
  have logBound : 4 * b ≤ Target.lambda n := by
    have monotone := Nat.clog_mono_right 2 large
    simpa only [Nat.clog_pow, show 1 < 2 by decide, if_pos, Target.lambda] using monotone
  have quotient : a ≤ Target.lambda n / 4 := by dsimp [b] at logBound; omega
  have logLarge : 16 ≤ Target.lambda n := by dsimp [b] at logBound; omega
  have remainder := Nat.mod_lt (Target.lambda n) (by decide : 0 < 4)
  have division := Nat.mod_add_div (Target.lambda n) 4
  have comparison : Target.lambda n ≤ 8 * (Target.lambda n / 4) := by omega
  refine ⟨logLarge, ?_⟩
  calc
    K * (Target.lambda n) ^ d ≤ K * (8 * (Target.lambda n / 4)) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left comparison _)
    _ = (K * 8 ^ d) * (Target.lambda n / 4) ^ d := by ring
    _ ≤ _ := bound _ quotient

/-! ## Prime density in dyadic intervals (lem:primes) -/

theorem dyadic_card_add (P : ℕ) :
    Nat.primeCounting P = Nat.primeCounting (P / 2) + (dyadicPrimes P).card := by
  have split : Nat.primesLE P = Nat.primesLE (P / 2) ∪ dyadicPrimes P := by
    ext p
    by_cases prime : Nat.Prime p
    · simp only [Nat.mem_primesLE, Finset.mem_union, dyadicPrimes,
        Finset.mem_filter, Finset.mem_range, prime, and_true, true_and]
      omega
    · simp [Nat.mem_primesLE, dyadicPrimes, prime]
  have disjoint : Disjoint (Nat.primesLE (P / 2)) (dyadicPrimes P) := by
    apply Finset.disjoint_left.mpr
    intro p half dyadic
    have bound := (Nat.mem_primesLE.mp half).1
    have larger := (Finset.mem_filter.mp dyadic).2.2
    omega
  rw [← Nat.primesLE_card_eq_primeCounting, split, Finset.card_union_of_disjoint disjoint,
    Nat.primesLE_card_eq_primeCounting]

theorem dyadic_density
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (P : ℝ) / 8 ≤ (dyadicPrimes P).card * Real.log (P : ℝ) := by
  obtain ⟨a, aPositive, approximation⟩ := source (1 / 16) (by norm_num)
  refine ⟨max 256 (2 * a), le_max_left _ _, ?_⟩
  intro P large
  have PBound : 256 ≤ P := (le_max_left _ _).trans large
  have halfBound : a ≤ P / 2 := by have := (le_max_right _ _).trans large; omega
  have wholeBound : a ≤ P := by omega
  have positiveP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have positiveHalf : (0 : ℝ) < ((P / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P / 2)
  have logPositive : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have quarter : (P : ℝ) / 4 ≤ ((P / 2 : ℕ) : ℝ) := by
    have natural : P ≤ 4 * (P / 2) := by omega
    have real : (P : ℝ) ≤ 4 * ((P / 2 : ℕ) : ℝ) := by exact_mod_cast natural
    linarith
  have half : ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    have natural := Nat.div_mul_le_self P 2
    have real : ((P / 2 : ℕ) : ℝ) * 2 ≤ (P : ℝ) := by exact_mod_cast natural
    linarith
  have logLarge : 8 * Real.log 2 ≤ Real.log (P : ℝ) := by
    have realBound : (256 : ℝ) ≤ P := by exact_mod_cast PBound
    have logarithm := Real.log_le_log (by norm_num : (0 : ℝ) < 256) realBound
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow] at logarithm
    norm_num at logarithm
    exact logarithm
  have logHalf : 3 / 4 * Real.log (P : ℝ) ≤ Real.log ((P / 2 : ℕ) : ℝ) := by
    have monotone := Real.log_le_log (by positivity : (0 : ℝ) < (P : ℝ) / 4) quarter
    rw [Real.log_div (ne_of_gt positiveP) (by norm_num : (4 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at monotone
    norm_num at monotone
    linarith
  obtain ⟨lower, _⟩ := abs_lt.mp (approximation P wholeBound)
  obtain ⟨_, upper⟩ := abs_lt.mp (approximation (P / 2) halfBound)
  have lowerCount : 15 / 16 * (P : ℝ) < Nat.primeCounting P * Real.log (P : ℝ) := by
    apply (lt_div_iff₀ positiveP).mp
    linarith
  have upperCount : (Nat.primeCounting (P / 2) : ℝ) * Real.log ((P / 2 : ℕ) : ℝ) <
      17 / 16 * ((P / 2 : ℕ) : ℝ) := by
    have bound : (Nat.primeCounting (P / 2) : ℝ) * Real.log ((P / 2 : ℕ) : ℝ) /
        ((P / 2 : ℕ) : ℝ) < 17 / 16 := by linarith
    have bound' := (div_lt_iff₀ positiveHalf).mp bound
    exact bound'
  have upperHalf : (Nat.primeCounting (P / 2) : ℝ) * (3 / 4 * Real.log (P : ℝ)) <
      17 / 32 * (P : ℝ) := by
    have monotone := mul_le_mul_of_nonneg_left logHalf
      (by positivity : (0 : ℝ) ≤ Nat.primeCounting (P / 2))
    nlinarith
  have count : (Nat.primeCounting P : ℝ) = (Nat.primeCounting (P / 2) : ℝ) +
      ((dyadicPrimes P).card : ℝ) := by exact_mod_cast dyadic_card_add P
  have countLog : (Nat.primeCounting P : ℝ) * Real.log (P : ℝ) =
      (Nat.primeCounting (P / 2) : ℝ) * Real.log (P : ℝ) +
      ((dyadicPrimes P).card : ℝ) * Real.log (P : ℝ) := by rw [count]; ring
  nlinarith

theorem dyadic_weight_lower (P : ℕ) (large : 4 ≤ P) :
    P * (dyadicPrimes P).card ≤ 4 * (ScalarWindow.window (dyadicPrimes P) - 1) := by
  have pointwise : ∀ p ∈ dyadicPrimes P, P ≤ 4 * (p - 1) := by
    intro p member
    have dyadic := (Finset.mem_filter.mp member).2.2
    omega
  have sum := Finset.sum_le_sum pointwise
  simpa [ScalarWindow.window, Finset.mul_sum, Nat.mul_comm] using sum

theorem dyadic_window_density
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (P : ℝ) ^ 2 / 32 ≤ (ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) * Real.log (P : ℝ) := by
  obtain ⟨onset, bound, density⟩ := dyadic_density source
  refine ⟨onset, bound, ?_⟩
  intro P large
  have PBound : 256 ≤ P := bound.trans large
  have logPositive : 0 < Real.log (P : ℝ) := Real.log_pos
    (by exact_mod_cast (by omega : 1 < P))
  have weight : (P : ℝ) * ((dyadicPrimes P).card : ℝ) ≤
      4 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) := by
    exact_mod_cast dyadic_weight_lower P (by omega)
  have multiply := mul_le_mul_of_nonneg_right weight logPositive.le
  have lower := mul_le_mul_of_nonneg_left (density P large)
    (by positivity : (0 : ℝ) ≤ P)
  nlinarith

theorem dyadic_nonempty
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P → (dyadicPrimes P).Nonempty := by
  obtain ⟨onset, bound, density⟩ := dyadic_density source
  refine ⟨onset, bound, ?_⟩
  intro P large
  apply Finset.card_pos.mp
  by_contra empty
  have zero : (dyadicPrimes P).card = 0 := by omega
  have positiveP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have lower := density P large
  rw [zero] at lower
  norm_num at lower
  linarith

theorem log_le_lambda (P n : ℕ) (positive : 0 < P) (small : P ≤ n) :
    Real.log (P : ℝ) ≤ (Target.lambda n : ℝ) := by
  have power : P ≤ 2 ^ Target.lambda n :=
    small.trans (Nat.le_pow_clog (by decide : 1 < 2) n)
  have positiveReal : (0 : ℝ) < P := by exact_mod_cast positive
  have powerReal : (P : ℝ) ≤ (2 : ℝ) ^ Target.lambda n := by exact_mod_cast power
  have logarithm := Real.log_le_log positiveReal powerReal
  rw [Real.log_pow] at logarithm
  have binaryLog : Real.log 2 ≤ 1 := by
    have bound := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at bound
    exact bound
  have scale := mul_le_mul_of_nonneg_left binaryLog
    (by positivity : (0 : ℝ) ≤ Target.lambda n)
  simpa only [mul_one] using logarithm.trans scale

theorem dyadic_window_growth
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P n : ℕ, onset ≤ P → P ≤ n →
      P ^ 2 ≤ 32 * (ScalarWindow.window (dyadicPrimes P) - 1) * Target.lambda n := by
  obtain ⟨onset, positive, density⟩ := dyadic_window_density source
  refine ⟨onset, positive, ?_⟩
  intro P n large small
  have logarithm := log_le_lambda P n (by omega) small
  have lower := density P large
  have scale := mul_le_mul_of_nonneg_left logarithm
    (by positivity : (0 : ℝ) ≤ (ScalarWindow.window (dyadicPrimes P) - 1 : ℕ))
  have realBound : (P : ℝ) ^ 2 ≤
      32 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) * (Target.lambda n : ℝ) := by linarith
  exact_mod_cast realBound

theorem dyadic_window_linear
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      P ≤ 32 * (ScalarWindow.window (dyadicPrimes P) - 1) := by
  obtain ⟨onset, positive, density⟩ := dyadic_window_density source
  refine ⟨onset, positive, ?_⟩
  intro P large
  have positiveP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have logarithm : Real.log (P : ℝ) ≤ P := by
    have := Real.log_le_sub_one_of_pos positiveP
    linarith
  have scale := mul_le_mul_of_nonneg_left logarithm
    (by positivity : (0 : ℝ) ≤ (ScalarWindow.window (dyadicPrimes P) - 1 : ℕ))
  have lower := density P large
  have realBound : (P : ℝ) ≤ 32 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast realBound

/-! ## The two-score window `L₂` (lem:window-size) -/

theorem pairSide_greatest (D' L : ℕ) (hL : Admissible D' L) (hLD : L ≤ D') : L ≤ pairSide D' := by
  have hle := Nat.le_findGreatest hLD hL
  unfold pairSide
  split_ifs with h
  · omega
  · exact hle

theorem pairSide_le_window (D' : ℕ) : pairSide D' ≤ D' ∨ pairSide D' = 1 := by
  unfold pairSide
  split_ifs with h
  · right; rfl
  · left; exact Nat.findGreatest_le D'

theorem pairSide_growth : ∃ onset : ℕ, 4 ≤ onset ∧ ∀ D' : ℕ, onset ^ 4 ≤ D' →
    2 ≤ pairSide D' ∧ D' ^ 3 ≤ (16 ^ 3 * 48 ^ 4) * pairSide D' ^ 4 := by
  obtain ⟨a, positive, admissible⟩ := QuantitativePairWindow.side_is_admissible
  refine ⟨a, positive, ?_⟩
  intro D room
  let q := QuantitativePairWindow.fourthRoot D
  let L := QuantitativePairWindow.side D
  have large : 4 ^ 4 ≤ D := (Nat.pow_le_pow_left positive _).trans room
  obtain ⟨two, criterion⟩ := admissible D room
  have rootPositive : 0 < q := by
    have four := QuantitativePairWindow.fourthRoot_large large
    change 4 ≤ q at four
    omega
  have sideBound : L ≤ D := by
    calc
      _ ≤ q ^ 3 := Nat.div_le_self _ _
      _ ≤ q ^ 4 := Nat.pow_le_pow_right rootPositive (by decide)
      _ ≤ D := (QuantitativePairWindow.fourthRoot_bounds D).1
  have selected : L ≤ pairSide D := pairSide_greatest D L ⟨two, criterion⟩ sideBound
  refine ⟨two.trans selected, ?_⟩
  have concrete := (QuantitativePairWindow.side_three_quarters D large).2
  exact concrete.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left selected _))

theorem dyadic_pair_growth
    (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P n : ℕ, onset ≤ P → P ≤ n →
      2 ≤ pairSide (ScalarWindow.window (dyadicPrimes P)) ∧
      P ^ 6 ≤ (32 ^ 3 * (16 ^ 3 * 48 ^ 4)) * (Target.lambda n) ^ 3 *
        (pairSide (ScalarWindow.window (dyadicPrimes P))) ^ 4 := by
  obtain ⟨a, aBound, scalar⟩ := dyadic_window_growth source
  obtain ⟨b, bBound, linear⟩ := dyadic_window_linear source
  obtain ⟨c, cBound, pair⟩ := pairSide_growth
  refine ⟨max (max a b) (32 * c ^ 4 + 256), ?_, ?_⟩
  · exact (by omega : 256 ≤ 32 * c ^ 4 + 256).trans (le_max_right _ _)
  intro P n large small
  have scalarBound := scalar P n ((le_max_left _ _).trans ((le_max_left _ _).trans large)) small
  have linearBound := linear P ((le_max_right _ _).trans ((le_max_left _ _).trans large))
  have PBound := (le_max_right _ _).trans large
  have windowLarge : c ^ 4 ≤ ScalarWindow.window (dyadicPrimes P) := by omega
  obtain ⟨side, growth⟩ := pair _ windowLarge
  refine ⟨side, ?_⟩
  calc
    P ^ 6 = (P ^ 2) ^ 3 := by ring
    _ ≤ (32 * (ScalarWindow.window (dyadicPrimes P) - 1) * Target.lambda n) ^ 3 :=
      Nat.pow_le_pow_left scalarBound _
    _ ≤ (32 * ScalarWindow.window (dyadicPrimes P) * Target.lambda n) ^ 3 := by gcongr; omega
    _ = 32 ^ 3 * (Target.lambda n) ^ 3 * ScalarWindow.window (dyadicPrimes P) ^ 3 := by ring
    _ ≤ 32 ^ 3 * (Target.lambda n) ^ 3 *
        ((16 ^ 3 * 48 ^ 4) * pairSide (ScalarWindow.window (dyadicPrimes P)) ^ 4) :=
      Nat.mul_le_mul_left _ growth
    _ = _ := by ring

end NearCubicGates.Close.Counter

set_option autoImplicit false

namespace NearCubicGates.Close.Counter

open scoped BigOperators
open NearCubicGates

/-- The public admission of a header (`sec:algorithm`): `n ≥ 4`, `W ≤ 2n⁴`, `n^{−B₁} ≤ β ≤ 1/16`. -/
def HeaderOK (B1 : ℕ) (hd : Header) : Prop :=
  4 ≤ hd.n ∧ hd.W ≤ 2 * hd.n ^ 4 ∧ 1 ≤ hd.beta * (hd.n : ℚ) ^ B1 ∧ hd.beta ≤ 1 / 16

theorem HeaderOK.beta_pos {B1 : ℕ} {hd : Header} (h : HeaderOK B1 hd) : 0 < hd.beta := by
  have hn : (0 : ℚ) < (hd.n : ℚ) ^ B1 := by have := h.1; positivity
  by_contra hneg
  have : hd.beta * (hd.n : ℚ) ^ B1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hn.le
  linarith [h.2.2.1]

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (le_of_lt Nat.lt_two_pow_self)

/-! ## The degree budget with the constant 100 -/

theorem outer_le_succ (n k : ℕ) : outer n k ≤ n + 1 := by
  have remainder := Nat.mod_lt (n - k) (by decide : 0 < 2)
  unfold outer
  omega

theorem outer_ge (n k : ℕ) : n - k ≤ outer n k := by
  unfold outer; omega

theorem Ubase_ge_two (n m : ℕ) (hn : 0 < n) : 2 ≤ Ubase n m := by
  unfold Ubase G0
  have h1 : 1 ≤ 2 * (2 * n ^ 4) * mT n m := Nat.one_le_iff_ne_zero.mpr (by unfold mT; positivity)
  omega

theorem degreePass_le (n k m D : ℕ) (hn : 0 < n) (passed : DegreePass n k m D) : D ≤ m := by
  have base := Ubase_ge_two n m hn
  have powerBound : 2 ^ (100 * D) ≤ 2 ^ m := by
    calc
      2 ^ (100 * D) ≤ Ubase n m ^ (100 * D) := Nat.pow_le_pow_left base _
      _ = 1 * Ubase n m ^ (100 * D) := by simp
      _ ≤ 2 ^ (100 * (k + 2)) * Ubase n m ^ (100 * D) :=
        Nat.mul_le_mul_right _ (by
          have positivePower : 0 < 2 ^ (100 * (k + 2)) := by positivity
          omega)
      _ ≤ 2 ^ m := passed
  have exponentBound : 100 * D ≤ m :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp powerBound
  omega

theorem greatestDegree_spec (n k m : ℕ) (hn : 0 < n) (zeroPass : DegreePass n k m 0) :
    DegreePass n k m (greatestDegree n k m) ∧ ∀ D, DegreePass n k m D → D ≤ greatestDegree n k m := by
  unfold greatestDegree
  refine ⟨Nat.findGreatest_spec (Nat.zero_le _) zeroPass, ?_⟩
  intro D passed
  exact Nat.le_findGreatest (degreePass_le n k m D hn passed) passed

theorem Ubase_polynomial (n m : ℕ) (large : 4 ≤ n) (hm : m ≤ n + 1) : Ubase n m ≤ n ^ 12 := by
  have mBound : m ≤ 2 * n := hm.trans (by omega)
  have nLog : Nat.clog 2 (n + 1) ≤ 2 * n := (clog_le_self _).trans (by omega)
  have mLog : Nat.clog 2 (m + 1) ≤ 3 * n := (clog_le_self _).trans (by omega)
  have hB0 : 4 * n * Nat.clog 2 (n + 1) ≤ 8 * n ^ 2 := by
    have := Nat.mul_le_mul_left (4 * n) nLog
    nlinarith
  have hBb : Bb n m ≤ 12 * n ^ 2 := by
    unfold Bb B0
    nlinarith
  have half : (m + 1) / 2 ≤ 2 * n := (by omega : (m + 1) / 2 ≤ m).trans mBound
  have exact : mT n m ≤ 49 * n ^ 4 := by
    unfold mT
    have product : Bb n m * m * ((m + 1) / 2) ≤ 12 * n ^ 2 * (2 * n) * (2 * n) :=
      Nat.mul_le_mul (Nat.mul_le_mul hBb mBound) half
    have positive : 1 ≤ n ^ 4 := Nat.succ_le_iff.mpr (pow_pos (by omega) _)
    nlinarith
  have nFourth : 197 ≤ n ^ 4 := by
    have := Nat.pow_le_pow_left large 4
    norm_num at this
    omega
  have eighth : 1 ≤ n ^ 8 := Nat.succ_le_iff.mpr (pow_pos (by omega) _)
  calc
    Ubase n m = 1 + 2 * (2 * n ^ 4) * mT n m := rfl
    _ ≤ 1 + 4 * n ^ 4 * (49 * n ^ 4) := by nlinarith
    _ ≤ 197 * n ^ 8 := by nlinarith
    _ ≤ n ^ 4 * n ^ 8 := Nat.mul_le_mul_right _ nFourth
    _ = n ^ 12 := by ring

theorem degreePass_of_exponents (n k m D : ℕ) (large : 4 ≤ n) (hm : m ≤ n + 1)
    (budget : 100 * (k + 2) + 1200 * Target.lambda n * D ≤ m) : DegreePass n k m D := by
  have envelopeBound : Ubase n m ≤ 2 ^ (12 * Target.lambda n) := by
    calc
      _ ≤ n ^ 12 := Ubase_polynomial n m large hm
      _ ≤ (2 ^ Target.lambda n) ^ 12 :=
        Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) n) _
      _ = _ := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  unfold DegreePass
  calc
    _ ≤ 2 ^ (100 * (k + 2)) * (2 ^ (12 * Target.lambda n)) ^ (100 * D) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left envelopeBound _)
    _ = 2 ^ (100 * (k + 2) + 1200 * Target.lambda n * D) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) budget

theorem greatestDegree_lower (n k : ℕ) (large : 4 ≤ n) (smallInner : 400 * (k + 2) ≤ n) :
    DegreePass n k (outer n k) 0 ∧ n / (4800 * Target.lambda n) ≤ greatestDegree n k (outer n k) := by
  have work := Nat.div_mul_le_self n (4800 * Target.lambda n)
  have outerBound := outer_ge n k
  have hm := outer_le_succ n k
  have scalar : 1200 * Target.lambda n * (n / (4800 * Target.lambda n)) * 4 ≤ n := by
    convert work using 1; ring
  have passed : DegreePass n k (outer n k) (n / (4800 * Target.lambda n)) :=
    degreePass_of_exponents n k _ _ large hm (by omega)
  have zero : DegreePass n k (outer n k) 0 := degreePass_of_exponents n k _ 0 large hm (by omega)
  exact ⟨zero, (greatestDegree_spec n k _ (by omega) zero).2 _ passed⟩

/-! ## Lift exponents -/

theorem lift_cap (k P : ℕ) (large : 3 ≤ P) : 2 ^ (k + 1 + 2 * (k + 1)) ≤ P ^ (2 * (k + 1)) := by
  calc
    _ = (2 ^ 3) ^ (k + 1) := by rw [← Nat.pow_mul]; congr 1; omega
    _ ≤ (P ^ 2) ^ (k + 1) := Nat.pow_le_pow_left (by norm_num; nlinarith) _
    _ = P ^ (2 * (k + 1)) := (Nat.pow_mul _ _ _).symm

theorem liftExp_exists (k P : ℕ) (large : 3 ≤ P) : ∃ e, liftExp k P = some e :=
  leastUpTo_isSome _ _ (2 * (k + 1)) le_rfl ⟨by omega, lift_cap k P large⟩

theorem liftExp_le_of_pass (k P e trial : ℕ) (he : liftExp k P = some e) (positive : 1 ≤ trial)
    (passed : 2 ^ (k + 1 + trial) ≤ P ^ trial) : e ≤ trial := by
  by_contra failure
  exact (leastUpTo_spec _ _ _ he).2.2 trial (by omega) ⟨positive, passed⟩

theorem lift_trial (cT n P : ℕ) (logLarge : 16 ≤ Target.lambda n)
    (binary : 2 ^ (Target.lambda n / 4) ≤ P) :
    2 ^ (inner cT n + 1 + 8 * (3 * Target.mu n + cT + 2)) ≤ P ^ (8 * (3 * Target.mu n + cT + 2)) := by
  let C := 3 * Target.mu n + cT + 2
  have positive : 2 ≤ C := by dsimp [C]; omega
  have remainder := Nat.mod_lt (Target.lambda n) (by decide : 0 < 4)
  have division := Nat.mod_add_div (Target.lambda n) 4
  have budget : inner cT n + 1 + 8 * C ≤ (Target.lambda n / 4) * (8 * C) := by
    change (2 * (Target.mu n + 1) + cT + Target.mu n) * Target.lambda n + 1 + 8 * C ≤ _
    have factor : 3 * Target.mu n + cT + 2 = C := rfl
    nlinarith
  calc
    _ ≤ 2 ^ ((Target.lambda n / 4) * (8 * C)) := Nat.pow_le_pow_right (by decide : 0 < 2) budget
    _ = (2 ^ (Target.lambda n / 4)) ^ (8 * C) := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left binary _

/-! ## The prime scale -/

def primeCoefficient (cT : ℕ) : ℕ := 460800 * (cT + 5)

theorem inner_eq (cT n : ℕ) : inner cT n = (3 * Target.mu n + cT + 2) * Target.lambda n := by
  unfold inner Jmax; ring

theorem prime_growth_at (cT n : ℕ) (large : 65536 ≤ n) (logLarge : 16 ≤ Target.lambda n)
    (polynomial : primeCoefficient cT * (Target.lambda n) ^ 3 ≤ 2 ^ (Target.lambda n / 4)) :
    inner cT n < n ∧ 400 * (inner cT n + 2) ≤ n ∧ DegreePass n (inner cT n) (outer n (inner cT n)) 0 ∧
      2 ^ (Target.lambda n / 4) ≤
        Nat.findGreatest (PrimeCandidate n (inner cT n) (Jmax n) (greatestDegree n (inner cT n) (outer n (inner cT n))))
          (min n (greatestDegree n (inner cT n) (outer n (inner cT n)) + 1)) ∧
      n ≤ primeCoefficient cT * Target.lambda n * (Target.mu n) ^ 2 *
        Nat.findGreatest (PrimeCandidate n (inner cT n) (Jmax n)
          (greatestDegree n (inner cT n) (outer n (inner cT n))))
          (min n (greatestDegree n (inner cT n) (outer n (inner cT n)) + 1)) ∧
      PrimeCandidate n (inner cT n) (Jmax n) (greatestDegree n (inner cT n) (outer n (inner cT n)))
        (Nat.findGreatest (PrimeCandidate n (inner cT n) (Jmax n)
          (greatestDegree n (inner cT n) (outer n (inner cT n))))
          (min n (greatestDegree n (inner cT n) (outer n (inner cT n)) + 1))) := by
  let L := Target.lambda n
  let M := Target.mu n
  let k := inner cT n
  let C := 3 * M + cT + 2
  let E := 8 * C
  let B := (2 * E - 1) * (2 * (M + 1) + 2)
  let D0 := n / (4800 * L)
  let P0 := 1 + D0 / B
  have LBound : 16 ≤ L := logLarge
  have LPositive : 0 < L := by omega
  have MPositive : 0 < M := Nat.clog_pos (by decide : 1 < 2) (by omega)
  have Mle : M ≤ L := clog_le_self _
  have CPositive : 2 ≤ C := by dsimp [C]; omega
  have CBound : C ≤ (cT + 5) * M := by dsimp [C]; nlinarith only [MPositive]
  have CBoundL : C ≤ (cT + 5) * L := CBound.trans (Nat.mul_le_mul_left _ Mle)
  have innerEq : k = C * L := inner_eq cT n
  have innerBound : k + 2 ≤ (cT + 7) * L ^ 2 := by
    have multiply := Nat.mul_le_mul_right L CBoundL
    have two : 2 ≤ 2 * L ^ 2 := by nlinarith only [LBound]
    rw [innerEq]
    nlinarith only [multiply, two]
  have coefficient : 400 * (cT + 7) ≤ primeCoefficient cT := by
    dsimp [primeCoefficient]
    omega
  have smallWork : 400 * (k + 2) ≤ 2 ^ (L / 4) := by
    calc
      _ ≤ 400 * ((cT + 7) * L ^ 2) := Nat.mul_le_mul_left _ innerBound
      _ ≤ primeCoefficient cT * L ^ 2 := by
        simpa only [mul_assoc] using Nat.mul_le_mul_right (L ^ 2) coefficient
      _ ≤ primeCoefficient cT * L ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right LPositive (by decide : 2 ≤ 3))
      _ ≤ _ := polynomial
  have lowerBinary : 2 ^ (L - 1) < n := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega)
  have quarter : L / 4 ≤ L - 1 := by omega
  have binarySmall : 2 ^ (L / 4) < n :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) quarter).trans_lt lowerBinary
  have smallInner : 400 * (k + 2) ≤ n := smallWork.trans binarySmall.le
  have innerSmall : k < n := by omega
  obtain ⟨zeroPass, Dfit⟩ := greatestDegree_lower n k (by omega) smallInner
  have EPositive : 0 < E := by dsimp [E]; omega
  have BPositive : 0 < B := by
    have leftPositive : 0 < 2 * E - 1 := by omega
    exact Nat.mul_pos leftPositive (by omega)
  have BBound : B ≤ 96 * (cT + 5) * M ^ 2 := by
    have first : 2 * E - 1 ≤ 16 * C := by dsimp [E]; omega
    have second : 2 * (M + 1) + 2 ≤ 6 * M := by omega
    calc
      _ ≤ (16 * C) * (6 * M) := Nat.mul_le_mul first second
      _ ≤ (16 * ((cT + 5) * M)) * (6 * M) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ CBound)
      _ = _ := by ring
  have paidB : 4800 * L * B ≤ 2 ^ (L / 4) := by
    calc
      _ ≤ 4800 * L * (96 * (cT + 5) * M ^ 2) := Nat.mul_le_mul_left _ BBound
      _ ≤ 4800 * L * (96 * (cT + 5) * L ^ 2) := by gcongr
      _ = primeCoefficient cT * L ^ 3 := by dsimp [primeCoefficient]; ring
      _ ≤ _ := polynomial
  have doubled : 2 * (L / 4) ≤ L - 1 := by omega
  have room : B * 2 ^ (L / 4) ≤ D0 := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 4800 * L)).mpr
    calc
      _ = (4800 * L * B) * 2 ^ (L / 4) := by ring
      _ ≤ 2 ^ (L / 4) * 2 ^ (L / 4) := Nat.mul_le_mul_right _ paidB
      _ = 2 ^ (2 * (L / 4)) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide : 0 < 2) doubled
      _ ≤ _ := lowerBinary.le
  have PBinary : 2 ^ (L / 4) ≤ P0 :=
    ((Nat.le_div_iff_mul_le BPositive).mpr (by simpa only [mul_comm] using room)).trans
      (by dsimp [P0]; omega)
  have PPositive : 3 ≤ P0 := by
    have logarithm : 2 ≤ L / 4 := by omega
    have powers := Nat.pow_le_pow_right (by decide : 0 < 2) logarithm
    norm_num at powers
    omega
  have PSmallD : P0 ≤ D0 + 1 := by dsimp [P0]; have := Nat.div_le_self D0 B; omega
  have Dsmall : D0 * (4800 * L) ≤ n := Nat.div_mul_le_self _ _
  have PSmallN : P0 ≤ n := by
    have scaled : 2 * D0 ≤ n := by
      simpa only [mul_comm] using (Nat.mul_le_mul_left D0 (by omega : 2 ≤ 4800 * L)).trans Dsmall
    omega
  have trialPass : 2 ^ (k + 1 + E) ≤ P0 ^ E := lift_trial cT n P0 logLarge PBinary
  obtain ⟨e0, lift⟩ := liftExp_exists k P0 PPositive
  have liftBound : e0 ≤ E := liftExp_le_of_pass _ _ _ _ lift (by dsimp [E]; omega) trialPass
  have budget : B * (P0 - 1) ≤ D0 := by
    simpa only [P0, Nat.add_sub_cancel_left, Nat.mul_comm] using Nat.div_mul_le_self D0 B
  have candidate : PrimeCandidate n k (Jmax n) (greatestDegree n k (outer n k)) P0 := by
    refine ⟨PPositive, le_min PSmallN (PSmallD.trans (Nat.add_le_add_right Dfit 1)), e0, lift, ?_⟩
    have factor : 2 * e0 - 1 ≤ 2 * E - 1 := by omega
    have hJ : Jmax n = M + 1 := rfl
    rw [hJ]
    exact ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ factor)).trans budget).trans Dfit
  have greater : P0 ≤ Nat.findGreatest (PrimeCandidate n k (Jmax n) (greatestDegree n k (outer n k)))
      (min n (greatestDegree n k (outer n k) + 1)) := Nat.le_findGreatest candidate.2.1 candidate
  have remainder := Nat.mod_lt n (by positivity : 0 < 4800 * L)
  have division := Nat.mod_add_div n (4800 * L)
  have numerator : n ≤ 4800 * L * (D0 + 1) := by
    dsimp only [D0]
    nlinarith only [remainder, division]
  have Bremainder := Nat.mod_lt D0 BPositive
  have Bdivision := Nat.mod_add_div D0 B
  have quotientBound : D0 + 1 ≤ B * P0 := by
    dsimp only [P0]
    nlinarith only [Bremainder, Bdivision]
  have price : n ≤ primeCoefficient cT * L * M ^ 2 * P0 := by
    calc
      _ ≤ 4800 * L * (D0 + 1) := numerator
      _ ≤ 4800 * L * (B * P0) := Nat.mul_le_mul_left _ quotientBound
      _ ≤ 4800 * L * ((96 * (cT + 5) * M ^ 2) * P0) := by gcongr
      _ = _ := by dsimp [primeCoefficient]; ring
  exact ⟨innerSmall, smallInner, zeroPass, PBinary.trans greater, price.trans (Nat.mul_le_mul_left _ greater),
    Nat.findGreatest_spec candidate.2.1 candidate⟩

/-! ## The concentration parameter -/

theorem beta_ge_inv_den (β : ℚ) (hβ : 0 < β) : 1 / (β.den : ℚ) ≤ β := by
  have hnum : 1 ≤ β.num := Rat.num_pos.mpr hβ
  have hden : (0 : ℚ) < β.den := by exact_mod_cast β.den_pos
  rw [div_le_iff₀ hden]
  calc (1 : ℚ) ≤ (β.num : ℚ) := by exact_mod_cast hnum
    _ = β * β.den := (Rat.mul_den_eq_num β).symm

theorem leastT_exists (k J : ℕ) (β : ℚ) (hβ : 0 < β) : ∃ T, leastT k J β = some T := by
  apply leastUpTo_isSome _ _ (TBound k J β) le_rfl
  unfold TPass TBound
  have hden : (0 : ℚ) < β.den := by exact_mod_cast β.den_pos
  have hlog : 4 * J * β.den < 2 ^ (Nat.log 2 (4 * J * β.den) + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hcast : ((4 * J * β.den : ℕ) : ℚ) ≤ (2 : ℚ) ^ (Nat.log 2 (4 * J * β.den) + 1) := by
    exact_mod_cast hlog.le
  have hb := beta_ge_inv_den β hβ
  have hpow : (2 : ℚ) ^ (k + Nat.log 2 (4 * J * β.den) + 1) =
      2 ^ k * 2 ^ (Nat.log 2 (4 * J * β.den) + 1) := by rw [← pow_add]; congr 1
  rw [hpow]
  push_cast at hcast ⊢
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  calc (4 : ℚ) * J * 2 ^ k = 2 ^ k * ((4 * J * β.den) * (1 / β.den)) := by field_simp
    _ ≤ 2 ^ k * (2 ^ (Nat.log 2 (4 * J * β.den) + 1) * β) := by
      gcongr
    _ = _ := by ring

theorem leastT_pos (k J T : ℕ) (β : ℚ) (hJ : 1 ≤ J) (hβ : β ≤ 1 / 16) (hT : leastT k J β = some T) :
    0 < T := by
  have hpass := (leastUpTo_spec _ _ _ hT).1
  by_contra h0
  have hT0 : T = 0 := by omega
  rw [hT0] at hpass
  unfold TPass at hpass
  have h1 : (1 : ℚ) ≤ ((4 * J * 2 ^ k : ℕ) : ℚ) := by
    have : 1 ≤ 4 * J * 2 ^ k := Nat.succ_le_iff.mpr (by positivity)
    exact_mod_cast this
  simp only [pow_zero, one_mul] at hpass
  linarith

theorem leastT_upper (B1 k J T n : ℕ) (β : ℚ) (hn : 4 ≤ n) (hβ : 1 ≤ β * (n : ℚ) ^ B1)
    (stageBound : 4 * J ≤ n ^ 2) (hT : leastT k J β = some T) :
    T ≤ k + (B1 + 2) * Target.lambda n := by
  have nPositive : 0 < n := by omega
  have powerPositive : (0 : ℚ) < (n : ℚ) ^ B1 := by positivity
  have binary : n ≤ 2 ^ Target.lambda n := Nat.le_pow_clog (by decide : 1 < 2) n
  have exponent : 4 * J * n ^ B1 ≤ 2 ^ ((B1 + 2) * Target.lambda n) := by
    calc
      _ ≤ n ^ 2 * n ^ B1 := Nat.mul_le_mul_right _ stageBound
      _ = n ^ (B1 + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ (2 ^ Target.lambda n) ^ (B1 + 2) := Nat.pow_le_pow_left binary _
      _ = _ := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have natural : (4 * J * 2 ^ k) * n ^ B1 ≤ 2 ^ (k + (B1 + 2) * Target.lambda n) := by
    calc
      _ = 2 ^ k * (4 * J * n ^ B1) := by ring
      _ ≤ 2 ^ k * 2 ^ ((B1 + 2) * Target.lambda n) := Nat.mul_le_mul_left _ exponent
      _ = _ := by rw [pow_add]
  by_contra hlt
  have hfail := (leastUpTo_spec _ _ _ hT).2.2 (k + (B1 + 2) * Target.lambda n) (by omega)
  apply hfail
  unfold TPass
  have hβ' : 1 / (n : ℚ) ^ B1 ≤ β := by
    rw [div_le_iff₀ powerPositive]; exact hβ
  calc
    ((4 * J * 2 ^ k : ℕ) : ℚ) ≤ (2 : ℚ) ^ (k + (B1 + 2) * Target.lambda n) / (n : ℚ) ^ B1 := by
      apply (le_div_iff₀ powerPositive).mpr
      exact_mod_cast natural
    _ ≤ (2 : ℚ) ^ (k + (B1 + 2) * Target.lambda n) * β := by
      simpa only [← mul_div_assoc, mul_one] using
        mul_le_mul_of_nonneg_left hβ' (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ (k + (B1 + 2) * Target.lambda n))

def tCoefficient (B1 cT : ℕ) : ℕ := B1 + cT + 7

theorem leastT_log_bound (B1 cT T n : ℕ) (β : ℚ) (hβ : 1 ≤ β * (n : ℚ) ^ B1) (large : 65536 ≤ n)
    (hT : leastT (inner cT n) (Jmax n) β = some T) :
    T ≤ tCoefficient B1 cT * Target.mu n * Target.lambda n := by
  have logTwo : 1 < Target.lambda n := by
    have monotone := Nat.clog_mono_right 2 large
    norm_num [Nat.clog_pow, Target.lambda] at monotone
    change 1 < Nat.clog 2 n
    omega
  have muPositive : 0 < Target.mu n := Nat.clog_pos (by decide : 1 < 2) logTwo
  have muBound : Target.mu n ≤ n := (clog_le_self (Target.lambda n)).trans (clog_le_self n)
  have stages : 4 * Jmax n ≤ n ^ 2 := by unfold Jmax; nlinarith only [large, muBound]
  have bound := leastT_upper B1 (inner cT n) (Jmax n) T n β (by omega) hβ stages hT
  have coefficient : 3 * Target.mu n + cT + B1 + 4 ≤ tCoefficient B1 cT * Target.mu n := by
    dsimp [tCoefficient]
    nlinarith only [muPositive]
  calc
    T ≤ inner cT n + (B1 + 2) * Target.lambda n := bound
    _ = (3 * Target.mu n + cT + B1 + 4) * Target.lambda n := by rw [inner_eq]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ coefficient

/-! ## Heights and the chain -/

theorem height_bounds (P : ℕ) : P / 4 ≤ Nat.sqrt (2 * (P / 4) ^ 2) ∧ Nat.sqrt (2 * (P / 4) ^ 2) ≤ P := by
  have lower : P / 4 ≤ Nat.sqrt (2 * (P / 4) ^ 2) :=
    Nat.le_sqrt'.mpr (by nlinarith [Nat.zero_le ((P / 4) ^ 2)])
  have quarter := Nat.div_mul_le_self P 4
  have square := Nat.sqrt_le' (2 * (P / 4) ^ 2)
  have magnitude : 16 * (P / 4) ^ 2 ≤ P ^ 2 := by
    have power := Nat.pow_le_pow_left quarter 2
    nlinarith only [power]
  have upper : Nat.sqrt (2 * (P / 4) ^ 2) ≤ P := by nlinarith only [magnitude, square]
  exact ⟨lower, upper⟩

theorem natCeil_cast (q : ℚ) : ⌈(q : ℝ)⌉₊ = ⌈q⌉₊ := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast (Nat.le_ceil q)
  · apply Nat.ceil_le.mpr
    have real : (q : ℝ) ≤ ((⌈(q : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact_mod_cast real

theorem ellBar_cast (ell0 : ℚ) (h T : ℕ) :
    (ellBar ell0 h T : ℝ) = PublicSamplingRates.liveCap T h ell0 := by
  simp only [ellBar, PublicSamplingRates.liveCap, Rat.cast_max, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat]

theorem piStar_cast (ell0 : ℚ) (h T : ℕ) :
    (piStar ell0 h T : ℝ) = PublicSamplingRates.targetRate T h ell0 := by
  simp only [piStar, PublicSamplingRates.targetRate, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat, ellBar_cast]

theorem firstDen_cast (ell0 : ℚ) (h T : ℕ) :
    firstDen ell0 h T = PublicSamplingRates.denominator T h ell0 := by
  unfold firstDen PublicSamplingRates.denominator
  rw [← natCeil_cast]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, ellBar_cast]

theorem firstRatio_cast (ell0 : ℚ) (h T : ℕ) :
    (firstRatio ell0 h T : ℝ) = PublicSamplingRates.initialRatio T h ell0 := by
  simp only [firstRatio, PublicSamplingRates.initialRatio, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, firstDen_cast, piStar_cast]

theorem firstRatio_pos' (ell0 : ℚ) (h T : ℕ) (positive : 0 < T) (guard : 64 * T ≤ h) :
    0 < firstRatio ell0 h T := by
  have positiveReal : (0 : ℝ) < T := by exact_mod_cast positive
  have guardReal : 64 * (T : ℝ) ≤ h := by exact_mod_cast guard
  have initialReal := (PublicSamplingRates.initial_bounds T h ell0 positiveReal guardReal).2.2.1
  exact (Rat.cast_lt (K := ℝ)).mp (by simpa only [Rat.cast_zero, firstRatio_cast] using initialReal)

/-- The chain of lem:chain stops within `J_max` stages (lem:chain (iii); proof of `lem:asymptotics`). -/
theorem stopIndex_exists (T h n : ℕ) (ell0 : ℚ) (positive : 0 < T) (guard : 64 * T ≤ h) (size : h ≤ n * T) :
    ∃ Jl, stopIndex (firstRatio ell0 h T) n = some Jl := by
  have positiveReal : (0 : ℝ) < T := by exact_mod_cast positive
  have guardReal : 64 * (T : ℝ) ≤ h := by exact_mod_cast guard
  have sizeReal : (h : ℝ) / T ≤ n := by
    apply (div_le_iff₀ positiveReal).mpr
    exact_mod_cast size
  obtain ⟨j, stages, stopped, _⟩ := PublicSamplingRates.chain_length_guard T h ell0 positiveReal guardReal n sizeReal
  have inside : j ≤ Jmax n - 1 := by
    change j + 1 ≤ Target.mu n + 1 at stages
    unfold Jmax
    omega
  have initialPositive := firstRatio_pos' ell0 h T positive guard
  have passed : (1 : ℚ) / 256 ≤ RationalRateChain.ratio (firstRatio ell0 h T) j := by
    apply (Rat.cast_le (K := ℝ)).mp
    simp only [RationalRateChain.ratio_cast _ initialPositive, firstRatio_cast]
    norm_num
    exact stopped
  exact leastUpTo_isSome _ _ j inside passed

theorem degree_large (cT n : ℕ) (large : 65536 ≤ n) (logLarge : 16 ≤ Target.lambda n)
    (polynomial : primeCoefficient cT * (Target.lambda n) ^ 3 ≤ 2 ^ (Target.lambda n / 4)) :
    2 * inner cT n ≤ greatestDegree n (inner cT n) (outer n (inner cT n)) := by
  let L := Target.lambda n
  have positive : 0 < L := by omega
  have Mle : Target.mu n ≤ L := clog_le_self _
  have coefficient : 3 * Target.mu n + cT + 2 ≤ (cT + 5) * L := by
    nlinarith only [Mle, positive]
  have work : 2 * inner cT n * (4800 * L) ≤ primeCoefficient cT * L ^ 3 := by
    rw [inner_eq]
    have multiply := Nat.mul_le_mul_right (9600 * L ^ 2) coefficient
    dsimp only [primeCoefficient]
    nlinarith only [multiply, Nat.zero_le ((cT + 5) * L ^ 3)]
  have lower : 2 ^ (L - 1) < n := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega)
  have binary : 2 ^ (L / 4) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have room : 2 * inner cT n ≤ n / (4800 * L) :=
    (Nat.le_div_iff_mul_le (by positivity)).mpr (work.trans (polynomial.trans (binary.trans lower.le)))
  have innerRoom : 400 * (inner cT n + 2) ≤ n := by
    have coefficientRoom : 400 * (inner cT n + 2) ≤ primeCoefficient cT * L ^ 3 := by
      have innerBound : inner cT n ≤ (cT + 5) * L ^ 2 := by
        rw [inner_eq]
        have multiply := Nat.mul_le_mul_right L coefficient
        nlinarith only [multiply]
      have squarePositive : 1 ≤ L ^ 2 := Nat.succ_le_iff.mpr (pow_pos positive _)
      have cubeBound : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right positive (by decide)
      dsimp only [primeCoefficient]
      nlinarith only [innerBound, squarePositive, cubeBound]
    exact coefficientRoom.trans (polynomial.trans (binary.trans lower.le))
  exact room.trans (greatestDegree_lower n (inner cT n) (by omega) innerRoom).2

/-! ## Eventual selection (lem:asymptotics: "All preliminary checks pass for large n") -/

/-- The data a successful selection is built from, for large `n` (shared with the window estimate). -/
theorem eventual_data (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) (B1 cT : ℕ) :
    ∃ onset : ℕ, 65536 ≤ onset ∧ ∀ hd : Header, HeaderOK B1 hd → onset ≤ hd.n →
      ∃ p, selectParams cT hd = some p ∧ 2 ^ (Target.lambda hd.n / 4) ≤ p.P ∧
        hd.n ≤ primeCoefficient cT * Target.lambda hd.n * (Target.mu hd.n) ^ 2 * p.P ∧
        p.T ≤ tCoefficient B1 cT * Target.mu hd.n * Target.lambda hd.n ∧ 16 ≤ Target.lambda hd.n := by
  obtain ⟨b, bBound, primes⟩ := dyadic_nonempty source
  obtain ⟨c, cBound, primeWork⟩ := polynomial_lambda_binary (primeCoefficient cT) 3
  obtain ⟨d, _, tWork⟩ := polynomial_lambda_binary (512 * tCoefficient B1 cT) 2
  let onset := max c (max d (2 ^ (4 * b)))
  refine ⟨onset, cBound.trans (le_max_left _ _), ?_⟩
  intro hd hok large
  have cLarge : c ≤ hd.n := (le_max_left _ _).trans large
  have dLarge : d ≤ hd.n := (le_max_left _ _).trans ((le_max_right _ _).trans large)
  have sourceLarge : 2 ^ (4 * b) ≤ hd.n := (le_max_right _ _).trans ((le_max_right _ _).trans large)
  have nLarge : 65536 ≤ hd.n := cBound.trans cLarge
  obtain ⟨logLarge, polynomial⟩ := primeWork hd.n cLarge
  obtain ⟨innerSmall, _, zeroPass, PBinary, price, candidate⟩ :=
    prime_growth_at cT hd.n nLarge logLarge polynomial
  set k := inner cT hd.n with hk
  set Dmax := greatestDegree hd.n k (outer hd.n k) with hDmax
  set P := Nat.findGreatest (PrimeCandidate hd.n k (Jmax hd.n) Dmax) (min hd.n (Dmax + 1)) with hP
  have hβ := hok.beta_pos
  obtain ⟨T, hT⟩ := leastT_exists k (Jmax hd.n) hd.beta hβ
  have TPositive : 0 < T := leastT_pos k (Jmax hd.n) T hd.beta (by unfold Jmax; omega) hok.2.2.2 hT
  have TBound := leastT_log_bound B1 cT T hd.n hd.beta hok.2.2.1 nLarge hT
  have muBound : Target.mu hd.n ≤ Target.lambda hd.n := clog_le_self _
  have TSquare : T ≤ tCoefficient B1 cT * (Target.lambda hd.n) ^ 2 := by
    have multiply := Nat.mul_le_mul_right (Target.lambda hd.n)
      (Nat.mul_le_mul_left (tCoefficient B1 cT) muBound)
    exact TBound.trans (by simpa only [pow_two, mul_assoc] using multiply)
  have paidT : 512 * T ≤ P := by
    calc
      _ ≤ 512 * (tCoefficient B1 cT * (Target.lambda hd.n) ^ 2) := Nat.mul_le_mul_left _ TSquare
      _ = (512 * tCoefficient B1 cT) * (Target.lambda hd.n) ^ 2 := by ring
      _ ≤ 2 ^ (Target.lambda hd.n / 4) := (tWork hd.n dLarge).2
      _ ≤ _ := PBinary
  have PLarge : 100 ≤ P := by omega
  have height := height_bounds P
  have width : 64 * T ≤ Nat.sqrt (2 * (P / 4) ^ 2) := by
    have divided : 64 * T ≤ P / 4 := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr (by omega)
    exact divided.trans height.1
  have PSmall : P ≤ hd.n := candidate.2.1.trans (Nat.min_le_left _ _)
  have size : Nat.sqrt (2 * (P / 4) ^ 2) ≤ hd.n * T :=
    height.2.trans (PSmall.trans (by nlinarith only [TPositive]))
  have logSource : 4 * b ≤ Target.lambda hd.n := by
    have monotone := Nat.clog_mono_right 2 sourceLarge
    simpa only [Nat.clog_pow, show 1 < 2 by decide, if_pos, Target.lambda] using monotone
  have PRequired : b ≤ P := by
    have scale : b ≤ Target.lambda hd.n / 4 := by omega
    exact (Nat.lt_two_pow_self.le).trans ((Nat.pow_le_pow_right (by decide : 0 < 2) scale).trans PBinary)
  have nonempty := primes P PRequired
  have degree := degree_large cT hd.n nLarge logLarge polynomial
  obtain ⟨e, he, _⟩ := candidate.2.2
  obtain ⟨Jl, hJ⟩ := stopIndex_exists T (Nat.sqrt (2 * (P / 4) ^ 2)) hd.n
    (((hd.W * k : ℕ) : ℚ) / (hd.beta * (Nat.sqrt (hd.n - k + 1) : ℚ))) TPositive width size
  have hsome : ∃ q, selectParams cT hd = some q := by
    unfold selectParams
    simp only
    rw [if_pos ⟨innerSmall, hβ⟩]
    simp only [← hk, hT]
    rw [if_pos zeroPass]
    simp only [← hDmax, ← hP, he]
    rw [if_pos ⟨by omega, nonempty, PLarge, width, degree⟩]
    simp only [hJ, Option.some.injEq, exists_eq']
  obtain ⟨q, hq⟩ := hsome
  have hs := selectParams_spec cT hd q hq
  have hqP : q.P = P := by rw [hs.P_eq, hs.Dmax_eq, hs.m_eq, hs.k_eq]
  have hqT : q.T ≤ T := by
    by_contra hlt
    exact hs.T_least T (by omega) (by rw [hs.k_eq]; exact (leastUpTo_spec _ _ _ hT).1)
  refine ⟨q, hq, ?_, ?_, ?_, logLarge⟩
  · rw [hqP]; exact PBinary
  · rw [hqP]; exact price
  · exact hqT.trans TBound

/-- lem:asymptotics: all preliminary checks pass for large `n`, uniformly over admitted headers. -/
theorem eventual_selection (source : PublishedSources.PrimeDensity.ApostolPrimeNumberTheorem) (B1 cT : ℕ) :
    ∃ onset : ℕ, ∀ hd : Header, HeaderOK B1 hd → onset ≤ hd.n → ∃ p, selectParams cT hd = some p := by
  obtain ⟨onset, _, h⟩ := eventual_data source B1 cT
  exact ⟨onset, fun hd hok hn => by
    obtain ⟨p, hp, _⟩ := h hd hok hn
    exact ⟨p, hp⟩⟩

end NearCubicGates.Close.Counter
