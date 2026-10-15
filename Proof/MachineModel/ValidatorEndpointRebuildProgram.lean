import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorRebuildWidthLedger

/-!
# The recovery-witness validator endpoint, rebuilt on the repaired circuit route

`ValidatorCircuitRebuildLedger` §5 replaces the validator's native contextual
call by `recoveryOracleCallRebuildProgram`, whose charge
`recoveryOracleCallRebuildBits` carries no geometric floor.  The frozen
endpoint `CanonicalRecoveryValidatorProgram.recoveryWitnessValidatorProgram`
cannot consume that repair: it *links* `recoveryOracleCallProgram`
definitionally, so its own charge `recoveryWitnessValidatorBits` still contains
`booleanCircuitValidationBits`, and `ValidatorTraversalWidthLedger` refutes
every polynomial bound on that name.

This module rebuilds the endpoint's linking on the repaired call.  Four links
change — the oracle validation stage, the oracle prefix, the legal-sum prefix
and the endpoint itself — and **every output contract is unchanged**, because
`run_recoveryOracleCallRebuildProgram` returns exactly `recoveryOracleCallOutput
handoff`, the value the frozen call returns.  Consequently the frozen
identification `recoveryWitnessValidatorProgramOutput_eq` and the frozen
acceptance ledger transfer verbatim: the Gap-1 endpoints are re-derived at the
rebuilt program with no new semantic content.

* §1 the oracle validation stage, rebuilt.

* §2 the structural prefix with the rebuilt oracle validation.

* §3 the legal-sum prefix over the rebuilt oracle prefix.

* §4 the endpoint, and the two Gap-1 endpoints at it.

* §5 the seam: what the rebuilt endpoint's charge still contains.
-/

namespace NearCubicWires.ValidatorEndpointRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.VerifiedLinker

/-! ## §1 The oracle validation stage, rebuilt -/

/-- **The nested-oracle validation stage, over the rebuilt call.**  Three of
the four stages are the frozen ones; only the contextual call changes. -/
def recoveryOracleValidationRebuildProgram : NPOracleProgram :=
  linkPrograms recoveryOracleCallLoweringProgram <|
    linkPrograms recoveryOracleCallRebuildProgram <|
      linkPrograms recoveryOracleBoundLoweringProgram
        recoveryBoundedContextCheckProgram

@[simp] theorem recoveryOracleValidationRebuildProgram_oracleFree :
    OracleFree recoveryOracleValidationRebuildProgram :=
  oracleFree_linkPrograms recoveryOracleCallLoweringProgram_oracleFree <|
    oracleFree_linkPrograms recoveryOracleCallRebuildProgram_oracleFree <|
      oracleFree_linkPrograms recoveryOracleBoundLoweringProgram_oracleFree
        recoveryBoundedContextCheckProgram_oracleFree

def recoveryOracleValidationRebuildTailFuel (handoff : ℕ) : ℕ :=
  linkFuel recoveryBoundedContextCheckProgram recoveryOracleBoundLoweringFuel <|
    recoveryBoundedContextCheckFuel (recoveryOracleBoundValue handoff)
      (recoveryOracleBoundCap handoff)

def recoveryOracleValidationRebuildCallTailFuel (handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryOracleBoundLoweringProgram
      recoveryBoundedContextCheckProgram)
    (recoveryOracleCallRebuildFuel handoff)
    (recoveryOracleValidationRebuildTailFuel handoff)

def recoveryOracleValidationRebuildFuel (handoff : ℕ) : ℕ :=
  linkFuel
    (linkPrograms recoveryOracleCallRebuildProgram <|
      linkPrograms recoveryOracleBoundLoweringProgram
        recoveryBoundedContextCheckProgram)
    recoveryOracleCallLoweringFuel
    (recoveryOracleValidationRebuildCallTailFuel handoff)

/-- **The rebuilt oracle validation charge.**  Exactly
`recoveryOracleValidationBits` with the call entry replaced. -/
def recoveryOracleValidationRebuildBits (inputLength handoff : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryOracleCallLoweringBits handoff) <|
      max (recoveryOracleCallRebuildBits inputLength handoff) <|
        max (recoveryOracleBoundLoweringBits handoff)
          (recoveryBoundedContextCheckBits inputLength
            (recoveryOracleBoundValue handoff)
            (recoveryOracleBoundCap handoff)
            (recoveryOracleBoundContext handoff))

/-- **The rebuilt oracle validation stage returns the published verdict.**
Output contract unchanged from `run_recoveryOracleValidationProgram`. -/
theorem run_recoveryOracleValidationRebuildProgram (inputLength handoff : ℕ) :
    runNPOracleProgram recoveryOracleValidationRebuildProgram
        (recoveryOracleValidationRebuildBits inputLength handoff)
        (recoveryOracleValidationRebuildFuel handoff)
        (initialNPOracleState inputLength handoff) =
      some (recoveryOracleValidationOutput handoff) := by
  let maximumBits := recoveryOracleValidationRebuildBits inputLength handoff
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hloweringBits :
      recoveryOracleCallLoweringBits handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      recoveryOracleCallRebuildBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hboundLoweringBits :
      recoveryOracleBoundLoweringBits handoff ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hboundBits :
      recoveryBoundedContextCheckBits inputLength
          (recoveryOracleBoundValue handoff)
          (recoveryOracleBoundCap handoff)
          (recoveryOracleBoundContext handoff) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlowering :=
    run_bits_mono (run_recoveryOracleCallLoweringProgram inputLength handoff)
      hloweringBits
  have hcall :=
    run_bits_mono (run_recoveryOracleCallRebuildProgram inputLength handoff)
      hcallBits
  have hboundLowering :=
    run_bits_mono (run_recoveryOracleBoundLoweringProgram inputLength handoff)
      hboundLoweringBits
  have hbound :
      runNPOracleProgram recoveryBoundedContextCheckProgram maximumBits
          (recoveryBoundedContextCheckFuel (recoveryOracleBoundValue handoff)
            (recoveryOracleBoundCap handoff))
          (initialNPOracleState inputLength
            (recoveryOracleBoundInput handoff)) =
        some (recoveryOracleValidationOutput handoff) := by
    rw [recoveryOracleBoundInput_eq_boundedContextInput]
    exact run_bits_mono
      (run_recoveryBoundedContextCheckProgram inputLength
        (recoveryOracleBoundValue handoff) (recoveryOracleBoundCap handoff)
        (recoveryOracleBoundContext handoff))
      hboundBits
  have hboundTail := run_linkPrograms hpositive hlength hboundLowering hbound
  have hcallTail := run_linkPrograms hpositive hlength hcall hboundTail
  have hrun := run_linkPrograms hpositive hlength hlowering hcallTail
  simpa only [recoveryOracleValidationRebuildProgram,
    recoveryOracleValidationRebuildFuel,
    recoveryOracleValidationRebuildCallTailFuel,
    recoveryOracleValidationRebuildTailFuel] using hrun

/-! ## §2 The structural prefix with the rebuilt oracle validation -/

/-- **The structural prefix with mandatory rebuilt oracle validation.** -/
def recoveryValidatorOraclePrefixRebuildProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorStructuralPrefixProgram
    recoveryOracleValidationRebuildProgram

@[simp] theorem recoveryValidatorOraclePrefixRebuildProgram_oracleFree :
    OracleFree recoveryValidatorOraclePrefixRebuildProgram :=
  oracleFree_linkPrograms recoveryValidatorStructuralPrefixProgram_oracleFree
    recoveryOracleValidationRebuildProgram_oracleFree

def recoveryValidatorOraclePrefixRebuildFuel
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryOracleValidationRebuildProgram
    recoveryValidatorStructuralPrefixFuel <|
      recoveryOracleValidationRebuildFuel
        (recoveryValidatorStructuralPrefixOutput limits raw)

def recoveryValidatorOraclePrefixRebuildBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorStructuralPrefixBits inputLength limits raw)
      (recoveryOracleValidationRebuildBits inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw))

/-- **The rebuilt oracle prefix returns the published handoff.**  Output
contract unchanged from `run_recoveryValidatorOraclePrefixProgram`. -/
theorem run_recoveryValidatorOraclePrefixRebuildProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorOraclePrefixRebuildProgram
        (recoveryValidatorOraclePrefixRebuildBits inputLength limits raw)
        (recoveryValidatorOraclePrefixRebuildFuel limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorOraclePrefixOutput limits raw) := by
  let maximumBits :=
    recoveryValidatorOraclePrefixRebuildBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hprefixBits :
      recoveryValidatorStructuralPrefixBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have horacleBits :
      recoveryOracleValidationRebuildBits inputLength
          (recoveryValidatorStructuralPrefixOutput limits raw) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefix :=
    run_bits_mono
      (run_recoveryValidatorStructuralPrefixProgram inputLength limits raw)
      hprefixBits
  have horacle :=
    run_bits_mono
      (run_recoveryOracleValidationRebuildProgram inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw))
      horacleBits
  have hrun := run_linkPrograms hpositive hlength hprefix horacle
  simpa only [recoveryValidatorOraclePrefixRebuildProgram,
    recoveryValidatorOraclePrefixRebuildFuel,
    recoveryValidatorOraclePrefixOutput] using hrun

/-! ## §3 The legal-sum prefix over the rebuilt oracle prefix

The legal-sum envelope is *not* rebuilt here: its ten stages are linked at the
handoff value `recoveryValidatorOraclePrefixOutput limits raw`, which the
rebuilt prefix returns unchanged, so the frozen envelope runner reuses
verbatim. -/

/-- **The staged legal-sum prefix, over the rebuilt oracle prefix.** -/
def recoveryValidatorLegalSumPrefixRebuildProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorOraclePrefixRebuildProgram
    recoveryLegalSumEnvelopeProgram

@[simp] theorem recoveryValidatorLegalSumPrefixRebuildProgram_oracleFree :
    OracleFree recoveryValidatorLegalSumPrefixRebuildProgram :=
  oracleFree_linkPrograms
    recoveryValidatorOraclePrefixRebuildProgram_oracleFree
    recoveryLegalSumEnvelopeProgram_oracleFree

def recoveryValidatorLegalSumPrefixRebuildFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryLegalSumEnvelopeProgram
    (recoveryValidatorOraclePrefixRebuildFuel limits raw) <|
      recoveryLegalSumEnvelopeFuel inputLength
        (recoveryValidatorOraclePrefixOutput limits raw)

def recoveryValidatorLegalSumPrefixRebuildBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorOraclePrefixRebuildBits inputLength limits raw)
      (recoveryLegalSumEnvelopeBits inputLength
        (recoveryValidatorOraclePrefixOutput limits raw))

/-- **The rebuilt legal-sum prefix returns the published handoff.**  Output
contract unchanged from `run_recoveryValidatorLegalSumPrefixProgram`. -/
theorem run_recoveryValidatorLegalSumPrefixRebuildProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryValidatorLegalSumPrefixRebuildProgram
        (recoveryValidatorLegalSumPrefixRebuildBits inputLength limits raw)
        (recoveryValidatorLegalSumPrefixRebuildFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) := by
  let handoff := recoveryValidatorOraclePrefixOutput limits raw
  let maximumBits :=
    recoveryValidatorLegalSumPrefixRebuildBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have horacleBits :
      recoveryValidatorOraclePrefixRebuildBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsumBits :
      recoveryLegalSumEnvelopeBits inputLength handoff ≤ maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have horacle :=
    run_bits_mono
      (run_recoveryValidatorOraclePrefixRebuildProgram inputLength limits raw)
      horacleBits
  have hsum :=
    run_bits_mono (run_recoveryLegalSumEnvelopeProgram inputLength handoff)
      hsumBits
  have hrun := run_linkPrograms hpositive hlength horacle hsum
  simpa only [recoveryValidatorLegalSumPrefixRebuildProgram,
    recoveryValidatorLegalSumPrefixRebuildFuel,
    recoveryValidatorLegalSumPrefixOutput] using hrun

/-! ## §4 The endpoint, and the two Gap-1 endpoints at it -/

/-- **The single public register program for the rebuilt recovery-witness
validator**: the rebuilt staged canonical validation followed by the frozen
mode/raw repackaging. -/
def recoveryWitnessValidatorRebuildProgram : NPOracleProgram :=
  linkPrograms recoveryValidatorLegalSumPrefixRebuildProgram
    recoveryValidatorModeRawProgram

@[simp] theorem recoveryWitnessValidatorRebuildProgram_oracleFree :
    OracleFree recoveryWitnessValidatorRebuildProgram :=
  oracleFree_linkPrograms
    recoveryValidatorLegalSumPrefixRebuildProgram_oracleFree
    recoveryValidatorModeRawProgram_oracleFree

def recoveryWitnessValidatorRebuildFuel
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryValidatorModeRawProgram
    (recoveryValidatorLegalSumPrefixRebuildFuel inputLength limits raw)
    recoveryValidatorModeRawFuel

/-- **The rebuilt endpoint's charge.**  Exactly `recoveryWitnessValidatorBits`
with the prefix entry replaced. -/
def recoveryWitnessValidatorRebuildBits
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max (recoveryValidatorLegalSumPrefixRebuildBits inputLength limits raw)
      (recoveryValidatorModeRawBits inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))

/-- **The rebuilt endpoint returns the published executable output.**  Output
contract unchanged from `run_recoveryWitnessValidatorProgram`. -/
theorem run_recoveryWitnessValidatorRebuildProgram
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryWitnessValidatorRebuildProgram
        (recoveryWitnessValidatorRebuildBits inputLength limits raw)
        (recoveryWitnessValidatorRebuildFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryWitnessValidatorProgramOutput inputLength limits raw) := by
  let maximumBits := recoveryWitnessValidatorRebuildBits inputLength limits raw
  have hlength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlength
  have hprefixBits :
      recoveryValidatorLegalSumPrefixRebuildBits inputLength limits raw ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmodeBits :
      recoveryValidatorModeRawBits inputLength
          (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hprefix :=
    run_bits_mono
      (run_recoveryValidatorLegalSumPrefixRebuildProgram inputLength limits raw)
      hprefixBits
  have hmode :=
    run_bits_mono
      (run_recoveryValidatorModeRawProgram inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw))
      hmodeBits
  have hrun := run_linkPrograms hpositive hlength hprefix hmode
  simpa only [recoveryWitnessValidatorRebuildProgram,
    recoveryWitnessValidatorRebuildFuel,
    recoveryWitnessValidatorProgramOutput] using hrun

/-- **Gap-1 exact-shape run theorem, at the rebuilt endpoint.**  The rebuilt
register program returns the pure validator's own output at every input; the
frozen unconditional identification is reused verbatim, because the rebuilt
program computes the same output function. -/
theorem run_recoveryWitnessValidatorRebuildProgram_eq_validatorOutput
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    runNPOracleProgram recoveryWitnessValidatorRebuildProgram
        (recoveryWitnessValidatorRebuildBits inputLength limits raw)
        (recoveryWitnessValidatorRebuildFuel inputLength limits raw)
        (initialNPOracleState inputLength
          (recoveryWitnessValidatorInput limits raw)) =
      some (recoveryWitnessValidatorOutput limits raw) := by
  rw [run_recoveryWitnessValidatorRebuildProgram inputLength limits raw,
    recoveryWitnessValidatorProgramOutput_eq inputLength limits raw]

/-- **Gap-1 acceptance ledger, at the rebuilt endpoint.**  The rebuilt program
accepts exactly the decodable witnesses whose resource checks hold. -/
theorem recoveryWitnessValidatorRebuildProgram_accepts_with_resources_iff
    (inputLength : ℕ) (limits : RecoveryWitnessLimits) (raw : ℕ) :
    recoveryWitnessValidatorProgramOutput inputLength limits raw ≠ 0 ↔
      ∃ witness : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits raw = some witness ∧
          RecoveryWitnessResourceChecks witness :=
  recoveryWitnessValidatorProgram_accepts_with_resources_iff inputLength limits
    raw

/-! ## §5 The seam

`recoveryWitnessValidatorRebuildBits` is a four-way maximum:

* `natBitLength inputLength`;

* `recoveryValidatorStructuralPrefixBits` — the frozen handoff projection cone;

* `recoveryOracleCallRebuildBits` — **the repaired call**, whose domination is
  `ValidatorCircuitRebuildLedger.hcall_rebuild_at_computableLimits`;

* `recoveryOracleCallLoweringBits`, `recoveryOracleBoundLoweringBits`,
  `recoveryBoundedContextCheckBits`, `recoveryValidatorModeRawBits` — frozen
  scalar trace ledgers;

* `recoveryLegalSumEnvelopeBits` — the frozen legal-sum envelope, carried
  unchanged.

The envelope is the only summand this module does not repair.  Its ten stages
link `balancedValidationSummaryProgram` at six call sites and
`canonicalNatValidationProgram` at one, so six of the ten still carry the
geometric charges the rebuild programs exist to remove; the width premise
`henvelopeBits` and the fuel premise `henvelopeFuel` are therefore carried
named, exactly as `ValidatorThreeLeafClosure` §4 carries them. -/

/-- **The rebuilt endpoint's charge, reduced to its five summands.**  The
reduction is definitional unfolding: every entry is named, and the only one
that is not a frozen scalar ledger is the repaired call. -/
theorem recoveryWitnessValidatorRebuildBits_le
    {inputLength : ℕ} {limits : RecoveryWitnessLimits} {raw bound : ℕ}
    (hlength : natBitLength inputLength ≤ bound)
    (hprefix :
      recoveryValidatorStructuralPrefixBits inputLength limits raw ≤ bound)
    (hlowering :
      recoveryOracleCallLoweringBits
        (recoveryValidatorStructuralPrefixOutput limits raw) ≤ bound)
    (hcall :
      recoveryOracleCallRebuildBits inputLength
        (recoveryValidatorStructuralPrefixOutput limits raw) ≤ bound)
    (hboundLowering :
      recoveryOracleBoundLoweringBits
        (recoveryValidatorStructuralPrefixOutput limits raw) ≤ bound)
    (hcheck :
      recoveryBoundedContextCheckBits inputLength
        (recoveryOracleBoundValue
          (recoveryValidatorStructuralPrefixOutput limits raw))
        (recoveryOracleBoundCap
          (recoveryValidatorStructuralPrefixOutput limits raw))
        (recoveryOracleBoundContext
          (recoveryValidatorStructuralPrefixOutput limits raw)) ≤ bound)
    (henvelope :
      recoveryLegalSumEnvelopeBits inputLength
        (recoveryValidatorOraclePrefixOutput limits raw) ≤ bound)
    (hmode :
      recoveryValidatorModeRawBits inputLength
        (recoveryValidatorLegalSumPrefixOutput inputLength limits raw) ≤
          bound) :
    recoveryWitnessValidatorRebuildBits inputLength limits raw ≤ bound := by
  simp only [recoveryWitnessValidatorRebuildBits,
    recoveryValidatorLegalSumPrefixRebuildBits,
    recoveryValidatorOraclePrefixRebuildBits,
    recoveryOracleValidationRebuildBits]
  omega

end NearCubicWires.ValidatorEndpointRebuildProgram
