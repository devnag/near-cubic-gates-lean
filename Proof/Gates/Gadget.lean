import Std

/-!
# The ten-clause Boolean gadget

This module checks the actual ten clauses of the Garey--Johnson--Stockmeyer
gadget, the quadratic penalty, its honest helper, the weighted stability
lemma, and the pair-XOR identity. All variables in these results are Boolean.
The proofs are kernel-checked finite case analyses; they do not use an axiom,
unfinished-proof placeholders, or compiled decision procedures.

The last two results isolate the linear-arithmetic certificate behind the
paper's restricted symmetric optimality observation. They use integer-scaled
coefficients and weights. They do not assert a representation theorem for
arbitrary real quadratic polynomials.
-/

namespace NearCubicGates.Gadget

/-- A Boolean value interpreted as the integer zero or one. -/
def bit : Bool → Int
  | false => 0
  | true => 1

/-- The truth value of the original three-literal clause. -/
def originalClause (x₁ x₂ x₃ : Bool) : Bool := x₁ || x₂ || x₃

/-- The helper chosen by the honest proof table. -/
def honestHelper (x₁ x₂ x₃ : Bool) : Bool := x₁ && x₂ && x₃

def inputWeight (x₁ x₂ x₃ : Bool) : Int := bit x₁ + bit x₂ + bit x₃

/-- The number of satisfied constraints among the actual ten constraints. -/
def satisfaction (x₁ x₂ x₃ y : Bool) : Int :=
  bit x₁ + bit x₂ + bit x₃ +
  bit ((!x₁) || (!x₂)) +
  bit ((!x₂) || (!x₃)) +
  bit ((!x₃) || (!x₁)) +
  bit y +
  bit (x₁ || (!y)) +
  bit (x₂ || (!y)) +
  bit (x₃ || (!y))

/-- Equation (gadget-penalty), interpreted over the integers. -/
def penalty (x₁ x₂ x₃ y : Bool) : Int :=
  1 - (bit x₁ + bit x₂ + bit x₃) +
  (bit x₁ * bit x₂ + bit x₁ * bit x₃ + bit x₂ * bit x₃) +
  2 * bit y - bit y * (bit x₁ + bit x₂ + bit x₃)

/-- A Boolean Hamming distance, with values zero and one. -/
def distance (a b : Bool) : Int := if a = b then 0 else 1

theorem distance_eq_absolute_difference (a b : Bool) :
    distance a b = Int.ofNat (Int.natAbs (bit a - bit b)) := by
  cases a <;> cases b <;> decide

/-- The paper's five-unit weighted error budget for one gadget. -/
def weightedError (x₁ x₂ x₃ x₁' x₂' x₃' y' : Bool) : Int :=
  distance x₁ x₁' + distance x₂ x₂' + distance x₃ x₃' +
  2 * distance (honestHelper x₁ x₂ x₃) y'

/-- The displayed penalty is exactly seven minus the actual clause score. -/
theorem penalty_eq_seven_sub_satisfaction (x₁ x₂ x₃ y : Bool) :
    penalty x₁ x₂ x₃ y = 7 - satisfaction x₁ x₂ x₃ y := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

/-- Twice the displayed score formula `6 + k - choose(k,2) + y * (k-2)`.
The factor two avoids introducing integer division into the statement. -/
theorem satisfaction_formula (x₁ x₂ x₃ y : Bool) :
    2 * satisfaction x₁ x₂ x₃ y =
      12 + 2 * inputWeight x₁ x₂ x₃ -
        inputWeight x₁ x₂ x₃ * (inputWeight x₁ x₂ x₃ - 1) +
        2 * bit y * (inputWeight x₁ x₂ x₃ - 2) := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

theorem penalty_table_helper_zero (x₁ x₂ x₃ : Bool) :
    penalty x₁ x₂ x₃ false =
      if inputWeight x₁ x₂ x₃ = 0 ∨ inputWeight x₁ x₂ x₃ = 3 then 1 else 0 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> decide

theorem penalty_table_helper_one (x₁ x₂ x₃ : Bool) :
    penalty x₁ x₂ x₃ true =
      if inputWeight x₁ x₂ x₃ = 0 then 3 else
      if inputWeight x₁ x₂ x₃ = 1 then 1 else 0 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> decide

/-- The polynomial counts all ten clauses and never exceeds score seven. -/
theorem satisfaction_le_seven (x₁ x₂ x₃ y : Bool) :
    satisfaction x₁ x₂ x₃ y ≤ 7 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

theorem penalty_nonnegative (x₁ x₂ x₃ y : Bool) :
    0 ≤ penalty x₁ x₂ x₃ y := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

theorem penalty_le_three (x₁ x₂ x₃ y : Bool) :
    penalty x₁ x₂ x₃ y ≤ 3 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

/-- The row for the all-zero triple is independent of clause literals. -/
theorem false_penalty_table (y : Bool) :
    penalty false false false y = if y then 3 else 1 := by
  cases y <;> decide

theorem false_clause_penalty (x₁ x₂ x₃ y : Bool) :
    originalClause x₁ x₂ x₃ = false → 1 ≤ penalty x₁ x₂ x₃ y := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

theorem false_clause_satisfaction (x₁ x₂ x₃ y : Bool) :
    originalClause x₁ x₂ x₃ = false → satisfaction x₁ x₂ x₃ y ≤ 6 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

/-- Each false original clause pays at least one unit of penalty; each true
clause pays a nonnegative amount, for every choice of the helper. -/
theorem false_indicator_le_penalty (x₁ x₂ x₃ y : Bool) :
    (if originalClause x₁ x₂ x₃ then (0 : Int) else 1) ≤ penalty x₁ x₂ x₃ y := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

theorem honest_penalty_zero (x₁ x₂ x₃ : Bool) :
    originalClause x₁ x₂ x₃ = true →
      penalty x₁ x₂ x₃ (honestHelper x₁ x₂ x₃) = 0 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> decide

theorem honest_satisfaction_seven (x₁ x₂ x₃ : Bool) :
    originalClause x₁ x₂ x₃ = true →
      satisfaction x₁ x₂ x₃ (honestHelper x₁ x₂ x₃) = 7 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> decide

/-- Lemma `gadget-stability`, for every true honest triple and every replacement. -/
theorem weighted_stability (x₁ x₂ x₃ x₁' x₂' x₃' y' : Bool) :
    originalClause x₁ x₂ x₃ = true →
      penalty x₁' x₂' x₃' y' ≤ weightedError x₁ x₂ x₃ x₁' x₂' x₃' y' := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;>
    cases x₁' <;> cases x₂' <;> cases x₃' <;> cases y' <;> decide

theorem weighted_error_nonnegative (x₁ x₂ x₃ x₁' x₂' x₃' y' : Bool) :
    0 ≤ weightedError x₁ x₂ x₃ x₁' x₂' x₃' y' := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;>
    cases x₁' <;> cases x₂' <;> cases x₃' <;> cases y' <;> decide

theorem weighted_error_le_five (x₁ x₂ x₃ x₁' x₂' x₃' y' : Bool) :
    weightedError x₁ x₂ x₃ x₁' x₂' x₃' y' ≤ 5 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;>
    cases x₁' <;> cases x₂' <;> cases x₃' <;> cases y' <;> decide

/-- The elementary Boolean XOR identity, without division or rounding. -/
theorem twice_product (a b : Bool) :
    2 * (bit a * bit b) = bit a + bit b - bit (Bool.xor a b) := by
  cases a <;> cases b <;> decide

/-- Equation `gadget-pair-identity`, multiplied by two for exact integer syntax.
There is one helper, three input, three input-pair, and three input-helper terms. -/
theorem pair_xor_identity (x₁ x₂ x₃ y : Bool) :
    2 * penalty x₁ x₂ x₃ y =
      2 + bit y - (bit x₁ + bit x₂ + bit x₃) -
        (bit (Bool.xor x₁ x₂) + bit (Bool.xor x₁ x₃) + bit (Bool.xor x₂ x₃)) +
        (bit (Bool.xor x₁ y) + bit (Bool.xor x₂ y) + bit (Bool.xor x₃ y)) := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> cases y <;> decide

/-- A single honest gadget and its possibly corrupted proof coordinates. -/
structure ErrorSample where
  x₁ : Bool
  x₂ : Bool
  x₃ : Bool
  x₁' : Bool
  x₂' : Bool
  x₃' : Bool
  y' : Bool

def ErrorSample.isTrue (s : ErrorSample) : Prop :=
  originalClause s.x₁ s.x₂ s.x₃ = true

def ErrorSample.penalty (s : ErrorSample) : Int :=
  Gadget.penalty s.x₁' s.x₂' s.x₃' s.y'

def ErrorSample.error (s : ErrorSample) : Int :=
  weightedError s.x₁ s.x₂ s.x₃ s.x₁' s.x₂' s.x₃' s.y'

/-- Total penalty over a finite collection of gadget/input pairs. -/
def totalPenalty : List ErrorSample → Int
  | [] => 0
  | s :: ss => s.penalty + totalPenalty ss

def totalError : List ErrorSample → Int
  | [] => 0
  | s :: ss => s.error + totalError ss

/-- Pointwise stability also holds after summing over all clauses and inputs. -/
theorem aggregate_weighted_stability (samples : List ErrorSample)
    (honest : ∀ s ∈ samples, s.isTrue) :
    totalPenalty samples ≤ totalError samples := by
  induction samples with
  | nil => simp [totalPenalty, totalError]
  | cons s ss ih =>
      have hs : s.isTrue := honest s (by simp)
      have hss : ∀ t ∈ ss, t.isTrue := by
        intro t ht
        exact honest t (by simp [ht])
      have hlocal : s.penalty ≤ s.error :=
        weighted_stability s.x₁ s.x₂ s.x₃ s.x₁' s.x₂' s.x₃' s.y' hs
      have hrest := ih hss
      simp only [totalPenalty, totalError]
      omega

/-- The two coefficient identities in the restricted symmetric argument. -/
theorem symmetric_coefficient_identities
    (a₀₁ a₁₁ a₀₃ a₁₃ a₂ : Int)
    (zeroAtOne : a₀₁ + a₁₁ = 0)
    (zeroAtThree : a₀₃ + 3 * a₁₃ + 3 * a₂ = 0) :
    a₂ = a₀₁ + (a₀₁ + 2 * a₁₁ + a₂) ∧
      a₀₃ = 3 * a₂ + 3 * (a₀₃ + 2 * a₁₃ + a₂) := by
  omega

/-- An integer-scaled certificate for the restricted symmetric weight bound.

`d` is the common scale, so `3 * wx + H ≥ 5 * d` says total weight is at
least five in the original units. The hypotheses record only the two honest
helpers, the two nonnegative values at input weight two, the rejection gap,
and the two comparisons supplied by weighted stability.
-/
theorem symmetric_scaled_weight_bound
    (a₀₁ a₁₁ a₀₃ a₁₃ a₂ wx H d : Int)
    (zeroAtOne : a₀₁ + a₁₁ = 0)
    (zeroAtThree : a₀₃ + 3 * a₁₃ + 3 * a₂ = 0)
    (falseGap : d ≤ a₀₁)
    (nonnegativeAtTwo₁ : 0 ≤ a₀₁ + 2 * a₁₁ + a₂)
    (nonnegativeAtTwo₃ : 0 ≤ a₀₃ + 2 * a₁₃ + a₂)
    (sameHelperStability : a₀₁ ≤ wx)
    (differentHelperStability : a₀₃ ≤ wx + H) :
    5 * d ≤ 3 * wx + H := by
  omega

end NearCubicGates.Gadget
