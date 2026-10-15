import Proof.MachineModel.CanonicalRecoveryValidatorProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# The limits front end of the recovery verifier

The internal validator ABI of `CanonicalRecoveryValidatorProgram` is
`pair(encoded schedule-derived limits, untrusted witness)`, and its comment
names the remaining obligation exactly: *the final public wrapper must build or
freeze the left component from register-one input arity; the nondeterministic
branch supplies only `raw`.*  This module is that wrapper.

The wrapper is a two-stage stream that is completely independent of *how* the
limits code is produced:

```
raw
  → recoveryLimitsDuplicateProgram            pair(raw, raw)
  → preserveRightProgram limitsCodeProgram    pair(limitsCode, raw)
```

`preserveRightProgram` forwards the public input length unchanged, so the
supplied `limitsCodeProgram` sees exactly `initialNPOracleState inputLength raw`
and may read the public arity from register one.  Consequently the whole
front-end obligation of `ExecutableRecoveryMachine.hlimitsFrontEnd` collapses
to the single premise

```
runNPOracleProgram limitsCodeProgram bits fuel
    (initialNPOracleState request.length (encodeBitInput request.witness)) =
  some (encodeRecoveryWitnessLimits (limitsOf request.inputArity))
```

which is `run_recoveryLimitsFrontEndProgram_request` below.  §4 discharges that
premise unconditionally for every *frozen* policy, i.e. whenever `limitsOf` is
constant: the frozen numeral is a `.set` immediate, so no arithmetic on the
public arity is performed at all.

## What a limits-code program can and cannot compute

`NPOracleProgram` is a finite list of instructions whose immediates are
naturals, and `run_bits_mono` makes a successful output independent of the
width budget.  A limits-code program therefore realizes a family
`inputLength ↦ encodeRecoveryWitnessLimits (limitsOf inputLength)` only when
that family is computable from the finitely many naturals frozen into the
stream.  §4 is the boundary case where the family is constant; a genuinely
length-indexed family must be presented the same way, as a program plus its run
theorem.  Nothing in this module assumes more.
-/

namespace NearCubicWires.RecoveryLimitsFrontEndProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 Duplicating the untrusted witness code

The nondeterministic branch supplies `raw` in register zero and nothing else.
Duplicating it is what lets the count-preserving adapter overwrite one copy
with the limits code while retaining the other. -/

/-- `raw ↦ pair(raw, raw)`. -/
def recoveryLimitsDuplicateProgram : NPOracleProgram :=
  [ .pair 0 0 0 1
  , .halt 0
  ]

@[simp] theorem recoveryLimitsDuplicateProgram_oracleFree :
    OracleFree recoveryLimitsDuplicateProgram := by
  rfl

def recoveryLimitsDuplicateBits (raw : ℕ) : ℕ :=
  natBitLength (Nat.pair raw raw)

def recoveryLimitsDuplicateFuel : ℕ := 2

theorem run_recoveryLimitsDuplicateProgram (inputLength raw : ℕ) :
    runNPOracleProgram recoveryLimitsDuplicateProgram
        (recoveryLimitsDuplicateBits raw) recoveryLimitsDuplicateFuel
        (initialNPOracleState inputLength raw) =
      some (Nat.pair raw raw) := by
  have hbits :
      natBitLength (Nat.pair raw raw) ≤ recoveryLimitsDuplicateBits raw :=
    le_rfl
  rw [show recoveryLimitsDuplicateFuel = 1 + 1 by rfl]
  rw [run_pair_instruction (value := Nat.pair raw raw)
    (by rfl) rfl (by simp [initialNPOracleState]) hbits]
  exact run_halt_instruction (fuel := 0) (value := Nat.pair raw raw)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-! ## §2 The wrapper -/

/-- **The limits front end.**  `limitsCodeProgram` is any stream producing the
encoded policy from the public input length in register one; the wrapper is
what turns it into the validator's internal ABI without disturbing the guessed
witness code. -/
def recoveryLimitsFrontEndProgram
    (limitsCodeProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms recoveryLimitsDuplicateProgram
    (preserveRightProgram limitsCodeProgram)

theorem recoveryLimitsFrontEndProgram_oracleFree
    {limitsCodeProgram : NPOracleProgram}
    (hlimitsCode : OracleFree limitsCodeProgram) :
    OracleFree (recoveryLimitsFrontEndProgram limitsCodeProgram) :=
  oracleFree_linkPrograms recoveryLimitsDuplicateProgram_oracleFree
    (preserveRightProgram_oracleFree limitsCodeProgram hlimitsCode)

def recoveryLimitsFrontEndBits
    (limitsCodeBits inputLength raw limitsCode : ℕ) : ℕ :=
  max (natBitLength inputLength)
    (max (recoveryLimitsDuplicateBits raw)
      (preserveRightBits limitsCodeBits raw raw limitsCode))

def recoveryLimitsFrontEndFuel
    (limitsCodeProgram : NPOracleProgram) (limitsCodeFuel : ℕ) : ℕ :=
  linkFuel (preserveRightProgram limitsCodeProgram)
    recoveryLimitsDuplicateFuel (preserveRightFuel limitsCodeFuel)

/-- Exact execution of the wrapper.  The single premise is the run theorem of
the limits-code program at the *same* public input length; every plumbing
instruction is accounted for. -/
theorem run_recoveryLimitsFrontEndProgram
    (limitsCodeProgram : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel inputLength raw : ℕ)
    (limits : RecoveryWitnessLimits)
    (hlimitsCode :
      runNPOracleProgram limitsCodeProgram limitsCodeBits limitsCodeFuel
          (initialNPOracleState inputLength raw) =
        some (encodeRecoveryWitnessLimits limits)) :
    runNPOracleProgram (recoveryLimitsFrontEndProgram limitsCodeProgram)
        (recoveryLimitsFrontEndBits limitsCodeBits inputLength raw
          (encodeRecoveryWitnessLimits limits))
        (recoveryLimitsFrontEndFuel limitsCodeProgram limitsCodeFuel)
        (initialNPOracleState inputLength raw) =
      some (recoveryWitnessValidatorInput limits raw) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryLimitsFrontEndBits limitsCodeBits inputLength raw
          (encodeRecoveryWitnessLimits limits) :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤
        recoveryLimitsFrontEndBits limitsCodeBits inputLength raw
          (encodeRecoveryWitnessLimits limits) := by
    refine le_trans ?_ hlength
    unfold natBitLength
    omega
  have hduplicateBits :
      recoveryLimitsDuplicateBits raw ≤
        recoveryLimitsFrontEndBits limitsCodeBits inputLength raw
          (encodeRecoveryWitnessLimits limits) :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits limitsCodeBits raw raw
          (encodeRecoveryWitnessLimits limits) ≤
        recoveryLimitsFrontEndBits limitsCodeBits inputLength raw
          (encodeRecoveryWitnessLimits limits) :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hduplicate :=
    run_bits_mono (run_recoveryLimitsDuplicateProgram inputLength raw)
      hduplicateBits
  have hpreserve :=
    run_bits_mono
      (run_preserveRightProgram limitsCodeProgram inputLength limitsCodeBits
        limitsCodeFuel raw raw (encodeRecoveryWitnessLimits limits)
        hlimitsCode)
      hpreserveBits
  exact run_linkPrograms hpositive hlength hduplicate hpreserve

/-! ## §3 The machine premise shape

`WeakVerifierRequest.length` is definitionally `WeakVerifierRequest.inputArity`,
so the public arity the machine indexes its policy by is exactly the register
the wrapper forwards. -/

def recoveryLimitsFrontEndRequestBits
    (limitsCodeBits : WeakVerifierRequest → ℕ)
    (limitsOf : ℕ → RecoveryWitnessLimits) (request : WeakVerifierRequest) :
    ℕ :=
  recoveryLimitsFrontEndBits (limitsCodeBits request)
    (WeakVerifierRequest.length request) (encodeBitInput request.witness)
    (encodeRecoveryWitnessLimits (limitsOf request.inputArity))

def recoveryLimitsFrontEndRequestFuel
    (limitsCodeProgram : NPOracleProgram)
    (limitsCodeFuel : WeakVerifierRequest → ℕ)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryLimitsFrontEndFuel limitsCodeProgram (limitsCodeFuel request)

/-- **`hlimitsFrontEnd` from one limits-code program.**  This is literally the
premise binder of `ExecutableRecoveryMachine.executableRecoveryMachine`, with
the front end, its width and its fuel supplied as named eta-reduced
functions. -/
theorem run_recoveryLimitsFrontEndProgram_request
    (limitsCodeProgram : NPOracleProgram)
    (limitsCodeBits limitsCodeFuel : WeakVerifierRequest → ℕ)
    (limitsOf : ℕ → RecoveryWitnessLimits)
    (hlimitsCode : ∀ request : WeakVerifierRequest,
      runNPOracleProgram limitsCodeProgram (limitsCodeBits request)
          (limitsCodeFuel request)
          (initialNPOracleState (WeakVerifierRequest.length request)
            (encodeBitInput request.witness)) =
        some (encodeRecoveryWitnessLimits (limitsOf request.inputArity)))
    (request : WeakVerifierRequest) :
    runNPOracleProgram (recoveryLimitsFrontEndProgram limitsCodeProgram)
        (recoveryLimitsFrontEndRequestBits limitsCodeBits limitsOf request)
        (recoveryLimitsFrontEndRequestFuel limitsCodeProgram limitsCodeFuel
          request)
        (initialNPOracleState (WeakVerifierRequest.length request)
          (encodeBitInput request.witness)) =
      some
        (recoveryWitnessValidatorInput (limitsOf request.inputArity)
          (encodeBitInput request.witness)) :=
  run_recoveryLimitsFrontEndProgram limitsCodeProgram (limitsCodeBits request)
    (limitsCodeFuel request) (WeakVerifierRequest.length request)
    (encodeBitInput request.witness) (limitsOf request.inputArity)
    (hlimitsCode request)

/-! ## §4 The frozen policy

A frozen numeral is a `.set` immediate: the stream performs no arithmetic on
the public arity, so the run theorem holds at every input length and every
guessed code.  This closes `hlimitsFrontEnd` outright for a constant policy
family. -/

/-- `_ ↦ value`, at every public input length. -/
def frozenNatProgram (value : ℕ) : NPOracleProgram :=
  [ .set 0 value 1
  , .halt 0
  ]

@[simp] theorem frozenNatProgram_oracleFree (value : ℕ) :
    OracleFree (frozenNatProgram value) := by
  rfl

def frozenNatBits (value : ℕ) : ℕ := natBitLength value

def frozenNatFuel : ℕ := 2

theorem run_frozenNatProgram (inputLength code value : ℕ) :
    runNPOracleProgram (frozenNatProgram value) (frozenNatBits value)
        frozenNatFuel (initialNPOracleState inputLength code) =
      some value := by
  have hbits : natBitLength value ≤ frozenNatBits value := le_rfl
  rw [show frozenNatFuel = 1 + 1 by rfl]
  rw [run_set_instruction (value := value) (by rfl) rfl hbits]
  exact run_halt_instruction (fuel := 0) (value := value)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hbits

/-- The frozen limits front end: one instruction stream, closed in the policy
it installs. -/
def frozenLimitsFrontEndProgram (limits : RecoveryWitnessLimits) :
    NPOracleProgram :=
  recoveryLimitsFrontEndProgram
    (frozenNatProgram (encodeRecoveryWitnessLimits limits))

theorem frozenLimitsFrontEndProgram_oracleFree
    (limits : RecoveryWitnessLimits) :
    OracleFree (frozenLimitsFrontEndProgram limits) :=
  recoveryLimitsFrontEndProgram_oracleFree
    (frozenNatProgram_oracleFree (encodeRecoveryWitnessLimits limits))

def frozenLimitsFrontEndBits (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryLimitsFrontEndRequestBits
    (fun _ => frozenNatBits (encodeRecoveryWitnessLimits limits))
    (fun _ => limits) request

def frozenLimitsFrontEndFuel (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryLimitsFrontEndRequestFuel
    (frozenNatProgram (encodeRecoveryWitnessLimits limits))
    (fun _ => frozenNatFuel) request

/-- **`hlimitsFrontEnd`, discharged for the frozen policy family.**  No
premise remains. -/
theorem run_frozenLimitsFrontEndProgram (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) :
    runNPOracleProgram (frozenLimitsFrontEndProgram limits)
        (frozenLimitsFrontEndBits limits request)
        (frozenLimitsFrontEndFuel limits request)
        (initialNPOracleState (WeakVerifierRequest.length request)
          (encodeBitInput request.witness)) =
      some
        (recoveryWitnessValidatorInput limits
          (encodeBitInput request.witness)) :=
  run_recoveryLimitsFrontEndProgram_request
    (frozenNatProgram (encodeRecoveryWitnessLimits limits))
    (fun _ => frozenNatBits (encodeRecoveryWitnessLimits limits))
    (fun _ => frozenNatFuel) (fun _ => limits)
    (fun request =>
      run_frozenNatProgram (WeakVerifierRequest.length request)
        (encodeBitInput request.witness)
        (encodeRecoveryWitnessLimits limits))
    request

end NearCubicWires.RecoveryLimitsFrontEndProgram
