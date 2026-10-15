import Proof.Circuits.ValidatorModeWidthClosure
import Proof.Circuits.ValidatorNodePreparationLedger

/-!
# The oracle stage's result width

`ValidatorLeafPremiseSweep` §4 names `hresult` — the width of
`recoveryOracleValidationResult` — as the width-side twin of the Boolean circuit
validator's fuel charge.  It is not a twin at all: the circuit validator is a
*fail-closed acceptance gate*, so its output is either the closed sentinel `0`
or the single pairing `Nat.pair 1 (booleanCircuitNodeCount inputLength raw)` —
and the node count is exactly the quantity `ValidatorCircuitStageWidths` §2
already capped, at `16` times the code's width, on the way to the comparison
stage's ledger.

So the whole obligation is one four-way case split over the gate's guards and
one pairing step.  No decoded magnitude is read, and nothing below the gate is
needed: the output ledger is strictly cheaper than the fuel ledger it was paired
with.
-/

namespace NearCubicWires.ValidatorOracleResultWidth

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination

/-! ## §1 The acceptance gate's only nonzero value -/

/-- The Boolean circuit validator accepts with the node count or not at all. -/
theorem booleanCircuitValidationOutput_le (inputLength raw : ℕ) :
    booleanCircuitValidationOutput inputLength raw ≤
      Nat.pair 1 (booleanCircuitNodeCount inputLength raw) := by
  simp only [booleanCircuitValidationOutput]
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split
      · exact Nat.zero_le _
      · split
        · exact Nat.zero_le _
        · exact le_rfl

/-- **The circuit validator's output ledger.**  Twice the node count's width,
and `ValidatorCircuitStageWidths` §2 caps that at sixteen times the code's. -/
theorem natBitLength_booleanCircuitValidationOutput_le (inputLength raw : ℕ) :
    natBitLength (booleanCircuitValidationOutput inputLength raw) ≤
      32 * natBitLength raw + 2 := by
  have hgate :=
    natBitLength_mono (booleanCircuitValidationOutput_le inputLength raw)
  have hpair := pairCodeBits_le 1 (booleanCircuitNodeCount inputLength raw)
  have hone : natBitLength 1 = 1 := natBitLength_one
  have hpositive :=
    one_le_natBitLength (booleanCircuitNodeCount inputLength raw)
  have hcount := natBitLength_booleanCircuitNodeCount_le inputLength raw
  have hmax :
      max (natBitLength 1) (natBitLength (booleanCircuitNodeCount inputLength raw)) =
        natBitLength (booleanCircuitNodeCount inputLength raw) := by
    rw [hone]
    exact Nat.max_eq_right hpositive
  rw [hmax] at hpair
  omega

theorem polyBounded_booleanCircuitValidationOutput
    {inputLength raw measure coefficient degree : ℕ}
    (hraw : PolyBounded (natBitLength raw) measure coefficient degree) :
    PolyBounded (natBitLength (booleanCircuitValidationOutput inputLength raw))
      measure (32 * coefficient + 2) degree :=
  ((hraw.const_mul 32).add (polyBounded_const 2 measure degree)).mono
    (natBitLength_booleanCircuitValidationOutput_le inputLength raw)

/-! ## §2 At the handoff's oracle projection -/

/-- The oracle code is one of the handoff's projections. -/
theorem handoffOracleCode_le (handoff : ℕ) :
    handoffOracleCode handoff ≤ handoff := by
  simp only [handoffOracleCode]
  exact (Nat.unpair_left_le _).trans
    ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

/-- **`hresult`, discharged.**  The handoff's own width pays for it. -/
theorem polyBounded_recoveryOracleValidationResult
    {handoff measure coefficient degree : ℕ}
    (hhandoff : PolyBounded (natBitLength handoff) measure coefficient degree) :
    PolyBounded (natBitLength (recoveryOracleValidationResult handoff)) measure
      (32 * coefficient + 2) degree := by
  have hcode :
      PolyBounded (natBitLength (handoffOracleCode handoff)) measure coefficient
        degree :=
    hhandoff.mono (natBitLength_mono (handoffOracleCode_le handoff))
  rw [recoveryOracleValidationResult]
  exact polyBounded_booleanCircuitValidationOutput hcode

end NearCubicWires.ValidatorOracleResultWidth
