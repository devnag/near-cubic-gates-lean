import Proof.MachineModel.CanonicalRecoveryProgram
import Proof.Amplification.RecoveryWitnessScheduleCapacity
import Proof.PCP.VerifierThresholdSeam

/-!
# Case-2 witness completeness for the fixed recovery machine

This module discharges the mathematical content of the Case-2 completeness
obligation `hcaseTwo`, namely `InverseCaseTwoAcceptance` and
`FixedCaseTwoAcceptance` of
[`CaseTwoRecoveryAssembly`](Proof/Amplification/CaseTwoRecoveryAssembly.lean).

The construction is witness-first.  From one legal symmetric or threshold
approximation of the scheduled Case-2 seed it builds the canonical
`CheckedRecoveryWitness` at the schedule-selected `RecoveryWitnessLimits`,
widens it into the sole length-indexed verifier policy without changing a
single serialized bit, places its canonical code into the fixed `n / 16`
nondeterministic witness using the existing schedule-capacity theorem, and
reads that code back exactly.

The semantic approximation distance is deliberately *not* stored in
`CheckedRecoveryWitness`; the verifier must execute that check itself.  This
module therefore keeps the distance alive as a separate proposition,
`RecoveryWitnessApproximates`, proved for the constructed witness from the
pointwise value theorems of `RecoveryWitnessNormalization`.  Nothing here
recovers the distance from a proof field of the witness.

## The single remaining machine hypothesis

Everything above is unconditional.  The only fact that cannot be proved before
the concrete machine exists is the behaviour of its verifier program on the
accepting witness.  It is isolated in exactly one definition,
`RecoveryVerifierAcceptsApproximation`:

```lean
∀ bits : BitInput (machine.witnessBits inputLength),
  recoveryWitnessValidatorOutput limits (encodeBitInput bits) ≠ 0 →
  (∀ witness : CheckedRecoveryWitness limits,
    decodeRecoveryWitness limits (encodeBitInput bits) = some witness →
    RecoveryWitnessApproximates seed delta witness) →
  machine.verifier.execute (machine.verifierRequest input bits) ≠ 0
```

Both premises are discharged here for the constructed witness: the guessed raw
code is accepted by the *pure* full-validator specification
`recoveryWitnessValidatorOutput` of `CanonicalRecoveryProgram`, see
`recoveryWitnessValidatorOutput_ne_zero_of_readback`, and every witness that
specification can return passes the semantic approximation check.  The
conclusion is one run of the verifier program on the corresponding
`WeakVerifierRequest`; no local checker, callback, evaluator, or fuel argument
occurs.  When the concrete machine lands, the hypothesis is discharged by
substitution from the verifier's run theorem.

`not_recoveryWitnessApproximates_of_checked` at the end of this module is the
regression guard for the failure mode the handoff calls out: a fully checked
canonical witness carries no distance evidence, so completeness cannot be
obtained from a supplied `CheckedRecoveryWitness`.
-/

namespace NearCubicWires.CaseTwoWitnessCompleteness

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessNormalization
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessScheduleCapacity
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## Semantic value of one serialized legal sum

The value depends only on the serialized description, never on the resource
policy it was checked against.  Keeping the limits out of this definition is
what lets the same real-valued function be recognized before and after a
policy widening. -/

/-- Real value of a serialized `SYM ∘ THR` sum at the arity it carries. -/
noncomputable def symmetricLegalSumValue
    (sum : LegalCircuitSumDescription NormalizedSymmetricThresholdCircuit)
    (input : BitInput sum.q) : ℝ :=
  sum.terms.foldl
    (fun total term =>
      total + (term.coefficient : ℝ) *
        bitAsReal (term.circuit.eval input)) 0

/-- Real value of a serialized `THR ∘ THR` sum at the arity it carries. -/
noncomputable def thresholdLegalSumValue
    (sum : LegalCircuitSumDescription NormalizedThresholdThresholdCircuit)
    (input : BitInput sum.q) : ℝ :=
  sum.terms.foldl
    (fun total term =>
      total + (term.coefficient : ℝ) *
        bitAsReal (term.circuit.eval input)) 0

/-- Move a Boolean function along an arity identity without casting the
function space itself. -/
def transportedSeed {smaller larger : ℕ} (harity : smaller = larger)
    (seed : BoolFunction larger) : BoolFunction smaller :=
  fun input => seed fun index => input (Fin.cast harity.symm index)

@[simp] theorem transportedSeed_rfl {arity : ℕ} (seed : BoolFunction arity) :
    transportedSeed (rfl : arity = arity) seed = seed := rfl

theorem transportedSeed_trans
    {small middle large : ℕ}
    (hfirst : small = middle) (hsecond : middle = large)
    (seed : BoolFunction large) :
    transportedSeed hfirst (transportedSeed hsecond seed) =
      transportedSeed (hfirst.trans hsecond) seed := rfl

/-- One arity identity used consistently on the seed and on the approximating
value leaves the mean `L¹` distance unchanged. -/
theorem l1DistanceFromBoolean_of_pointwise
    {smaller larger : ℕ} (harity : smaller = larger)
    (seed : BoolFunction larger)
    (value : BitInput smaller → ℝ)
    (approximation : BitInput larger → ℝ)
    (hvalue : ∀ input : BitInput smaller,
      value input = approximation (cast (congrArg BitInput harity) input)) :
    l1DistanceFromBoolean (transportedSeed harity seed) value =
      l1DistanceFromBoolean seed approximation := by
  cases harity
  have hequal : value = approximation := funext hvalue
  rw [hequal, transportedSeed_rfl]

/-! ## The approximation check the verifier must execute -/

/-- The semantic acceptance condition of the fixed verifier.  It is a
proposition *about* a checked witness, never a field stored inside one. -/
def RecoveryWitnessApproximates
    {limits : RecoveryWitnessLimits}
    (seed : BoolFunction limits.sumArity) (delta : ℝ) :
    CheckedRecoveryWitness limits → Prop
  | .symmetric _ _ sum =>
      l1DistanceFromBoolean
          (transportedSeed (sum.arity_eq.trans limits.symmetricArity) seed)
          (symmetricLegalSumValue sum.value) ≤ delta
  | .threshold _ _ sum =>
      l1DistanceFromBoolean
          (transportedSeed (sum.arity_eq.trans limits.thresholdArity) seed)
          (thresholdLegalSumValue sum.value) ≤ delta

theorem recoveryWitnessApproximates_symmetric
    {limits : RecoveryWitnessLimits}
    (seed : BoolFunction limits.sumArity) (delta : ℝ)
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits limits.symmetric) :
    RecoveryWitnessApproximates seed delta
        (CheckedRecoveryWitness.symmetric oracle horacle sum) ↔
      l1DistanceFromBoolean
          (transportedSeed (sum.arity_eq.trans limits.symmetricArity) seed)
          (symmetricLegalSumValue sum.value) ≤ delta := Iff.rfl

theorem recoveryWitnessApproximates_threshold
    {limits : RecoveryWitnessLimits}
    (seed : BoolFunction limits.sumArity) (delta : ℝ)
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits limits.threshold) :
    RecoveryWitnessApproximates seed delta
        (CheckedRecoveryWitness.threshold oracle horacle sum) ↔
      l1DistanceFromBoolean
          (transportedSeed (sum.arity_eq.trans limits.thresholdArity) seed)
          (thresholdLegalSumValue sum.value) ≤ delta := Iff.rfl

/-! ## Canonical witness construction that keeps the distance alive -/

/-- Symmetric-mode approximation certificate, stated so that the resource
policy is an explicit argument.  Leaving it explicit keeps every downstream
instantiation a first-order unification. -/
private theorem approximates_symmetric_of_pointwise
    (limits : RecoveryWitnessLimits)
    (seed : BoolFunction limits.sumArity) (delta : ℝ)
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits limits.symmetric)
    (approximation : BitInput limits.sumArity → ℝ)
    (hvalue : ∀ input : BitInput sum.value.q,
      symmetricLegalSumValue sum.value input =
        approximation
          (cast (congrArg BitInput
            (sum.arity_eq.trans limits.symmetricArity)) input))
    (hdistance : l1DistanceFromBoolean seed approximation ≤ delta) :
    RecoveryWitnessApproximates seed delta
      (CheckedRecoveryWitness.symmetric oracle horacle sum) := by
  rw [recoveryWitnessApproximates_symmetric,
    l1DistanceFromBoolean_of_pointwise _ seed
      (symmetricLegalSumValue sum.value) approximation hvalue]
  exact hdistance

/-- Threshold-mode counterpart of `approximates_symmetric_of_pointwise`. -/
private theorem approximates_threshold_of_pointwise
    (limits : RecoveryWitnessLimits)
    (seed : BoolFunction limits.sumArity) (delta : ℝ)
    (oracle : BooleanCircuit limits.oracleArity)
    (horacle : oracle.size ≤ limits.oracleSizeCap)
    (sum : CheckedLegalCircuitSum
      NormalizedThresholdThresholdCircuit
      NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits limits.threshold)
    (approximation : BitInput limits.sumArity → ℝ)
    (hvalue : ∀ input : BitInput sum.value.q,
      thresholdLegalSumValue sum.value input =
        approximation
          (cast (congrArg BitInput
            (sum.arity_eq.trans limits.thresholdArity)) input))
    (hdistance : l1DistanceFromBoolean seed approximation ≤ delta) :
    RecoveryWitnessApproximates seed delta
      (CheckedRecoveryWitness.threshold oracle horacle sum) := by
  rw [recoveryWitnessApproximates_threshold,
    l1DistanceFromBoolean_of_pointwise _ seed
      (thresholdLegalSumValue sum.value) approximation hvalue]
  exact hdistance

/-- Canonical decoder witness for one published legal approximation, together
with the executed distance property.  The existing schedule bridge selects the
same canonical witness through `Classical.choice` and therefore discards this
property; keeping it is exactly what makes verifier completeness provable
without storing a terminal obligation inside `CheckedRecoveryWitness`. -/
theorem exists_approximatingCheckedRecoveryWitness
    (contracts : PublishedContracts)
    {oracleArity oracleSizeCap sumArity : ℕ}
    (copies symmetricWireCap thresholdWireCap : ℕ)
    (seed : BoolFunction sumArity)
    (oracle : BooleanCircuit oracleArity)
    (oracleSize_le : oracle.size ≤ oracleSizeCap)
    (approximation :
      PublishedLegalApproximation contracts seed copies
        symmetricWireCap thresholdWireCap) :
    ∃ witness : CheckedRecoveryWitness
      (xorRecoveryWitnessLimits (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts)
        copies oracleArity oracleSizeCap sumArity
        symmetricWireCap thresholdWireCap),
      RecoveryWitnessApproximates seed (publishedRecoveryDelta contracts)
        witness := by
  simp only [PublishedLegalApproximation] at approximation
  rcases approximation with approximation | approximation
  · rcases approximation with ⟨sum, hterms, hbits, hmass, hdistance⟩
    obtain ⟨checked, _, hvalue⟩ :=
      symmetricCheckedLegalCircuitSum_of_contracts
        contracts.thresholdNormalization (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts) copies sum hterms hbits hmass
    exact ⟨CheckedRecoveryWitness.symmetric oracle oracleSize_le checked,
      approximates_symmetric_of_pointwise
        (xorRecoveryWitnessLimits (publishedXorWitness contracts)
          (publishedRecoveryDelta contracts)
          copies oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap)
        seed (publishedRecoveryDelta contracts) oracle oracleSize_le checked
        sum.value hvalue hdistance⟩
  · rcases approximation with ⟨sum, hterms, hbits, hmass, hdistance⟩
    obtain ⟨checked, _, hvalue⟩ :=
      thresholdCheckedLegalCircuitSum_of_contracts
        contracts.thresholdNormalization (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts) copies sum hterms hbits hmass
    exact ⟨CheckedRecoveryWitness.threshold oracle oracleSize_le checked,
      approximates_threshold_of_pointwise
        (xorRecoveryWitnessLimits (publishedXorWitness contracts)
          (publishedRecoveryDelta contracts)
          copies oracleArity oracleSizeCap sumArity
          symmetricWireCap thresholdWireCap)
        seed (publishedRecoveryDelta contracts) oracle oracleSize_le checked
        sum.value hvalue hdistance⟩

/-! ## Policy widening preserves the executed check -/

/-- Rechecking a canonical witness under a weaker policy changes neither its
serialized bits nor its semantic value, so the executed approximation check
survives the widening used by the inverse schedule. -/
theorem recoveryWitnessApproximates_widen
    (smaller larger : RecoveryWitnessLimits)
    (hlimits : smaller.Weakens larger)
    (seed : BoolFunction larger.sumArity) (delta : ℝ)
    (witness : CheckedRecoveryWitness smaller)
    (happroximates :
      RecoveryWitnessApproximates
        (transportedSeed hlimits.sumArity_eq seed) delta witness) :
    RecoveryWitnessApproximates seed delta (witness.widen hlimits) := by
  cases witness with
  | symmetric _ _ _ => exact happroximates
  | threshold _ _ _ => exact happroximates

/-! ## The single remaining machine hypothesis -/

/-- Sole verifier-run hypothesis of Case-2 completeness.  Both premises are
proved unconditionally in this module for the constructed witness: the guessed
bit vector is accepted by the *pure* full-validator specification
`recoveryWitnessValidatorOutput`, and every witness that specification can
return passes the semantic approximation check.  The conclusion is exactly one
run of the machine's verifier program on the corresponding
`WeakVerifierRequest`; no local checker, callback, or fuel argument occurs. -/
def RecoveryVerifierAcceptsApproximation
    (machine : ExecutableWeakNondeterministicMachine)
    (limits : RecoveryWitnessLimits) (delta : ℝ)
    {inputLength : ℕ} (input : BitInput inputLength)
    (seed : BoolFunction limits.sumArity) : Prop :=
  ∀ bits : BitInput (machine.witnessBits inputLength),
    recoveryWitnessValidatorOutput limits (encodeBitInput bits) ≠ 0 →
    (∀ witness : CheckedRecoveryWitness limits,
      decodeRecoveryWitness limits (encodeBitInput bits) = some witness →
      RecoveryWitnessApproximates seed delta witness) →
    machine.verifier.execute (machine.verifierRequest input bits) ≠ 0

/-- Installing `recoveryWitnessShape` fixes the machine's nondeterministic
witness width to the executable `n / 16` program. -/
theorem machineWitnessBits_eq
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (inputLength : ℕ) :
    machine.witnessBits inputLength = recoveryWitnessWidth inputLength := by
  unfold ExecutableWeakNondeterministicMachine.witnessBits
  rw [hshape, recoveryWitnessShape_execute, recoveryWitnessWidth_eq]

/-- Exact readback of the canonical witness code from the machine's fixed
nondeterministic witness width.  No padding is serialized as witness data. -/
theorem encodeBitInput_machineWitnessCode
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (limits : RecoveryWitnessLimits) (inputLength : ℕ)
    (witness : CheckedRecoveryWitness limits)
    (hcapacity :
      recoveryWitnessCodeBitBound limits ≤
        recoveryWitnessWidth inputLength) :
    encodeBitInput
        (fun bit : Fin (machine.witnessBits inputLength) =>
          witness.code.testBit bit.val) = witness.code := by
  apply encodeBitInput_testBit
  have hbits :
      natBitLength witness.code ≤ machine.witnessBits inputLength := by
    rw [machineWitnessBits_eq machine hshape]
    exact (CheckedRecoveryWitness.code_bits_le witness).trans hcapacity
  have hcode : witness.code < 2 ^ natBitLength witness.code := by
    unfold natBitLength
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two witness.code
  exact hcode.trans_le (Nat.pow_le_pow_right (by omega) hbits)

/-- The pure full-validator specification accepts exactly the raw code the
machine guesses.  This is the premise the executable validator of the
production verifier must reproduce; no local checker is assumed here. -/
theorem recoveryWitnessValidatorOutput_ne_zero_of_readback
    (limits : RecoveryWitnessLimits) (width : ℕ)
    (witness : CheckedRecoveryWitness limits)
    (bits : BitInput width)
    (hbits : encodeBitInput bits = witness.code) :
    recoveryWitnessValidatorOutput limits (encodeBitInput bits) ≠ 0 := by
  rw [hbits]
  exact recoveryWitnessValidatorOutput_ne_zero_iff.mpr
    ⟨witness, decodeRecoveryWitness_encode witness⟩

/-- A nonzero verifier output is exactly one accepting nondeterministic
branch of the derived semantic machine. -/
private theorem run_eq_true_of_execute_ne_zero
    (machine : ExecutableWeakNondeterministicMachine) (inputLength : ℕ)
    (input : BitInput inputLength)
    (bits : BitInput (machine.witnessBits inputLength))
    (hnonzero :
      machine.verifier.execute (machine.verifierRequest input bits) ≠ 0) :
    machine.run inputLength input bits = true := by
  unfold ExecutableWeakNondeterministicMachine.run
  simpa using hnonzero

/-- Package the accepting nondeterministic branch required by
`WeakNondeterministicMachine.accepts`.  Both premises of the verifier-run
hypothesis are discharged here from the canonical codec and the schedule
capacity theorem. -/
theorem accepts_of_verifierAcceptsApproximation
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (limits : RecoveryWitnessLimits) (delta : ℝ)
    (inputLength : ℕ) (input : BitInput inputLength)
    (seed : BoolFunction limits.sumArity)
    (hverifier :
      RecoveryVerifierAcceptsApproximation machine limits delta input seed)
    (witness : CheckedRecoveryWitness limits)
    (hcapacity :
      recoveryWitnessCodeBitBound limits ≤
        recoveryWitnessWidth inputLength)
    (happroximates : RecoveryWitnessApproximates seed delta witness) :
    machine.toSemantic.accepts input := by
  refine ⟨fun bit => witness.code.testBit bit.val, ?_⟩
  have hbits :
      encodeBitInput
          (fun bit : Fin (machine.witnessBits inputLength) =>
            witness.code.testBit bit.val) = witness.code :=
    encodeBitInput_machineWitnessCode machine hshape limits inputLength
      witness hcapacity
  have hdecode :
      decodeRecoveryWitness limits
          (encodeBitInput
            (fun bit : Fin (machine.witnessBits inputLength) =>
              witness.code.testBit bit.val)) = some witness := by
    rw [hbits]
    exact decodeRecoveryWitness_encode witness
  have hvalidator :
      recoveryWitnessValidatorOutput limits
          (encodeBitInput
            (fun bit : Fin (machine.witnessBits inputLength) =>
              witness.code.testBit bit.val)) ≠ 0 :=
    recoveryWitnessValidatorOutput_ne_zero_iff.mpr ⟨witness, hdecode⟩
  have hcheck :
      ∀ candidate : CheckedRecoveryWitness limits,
        decodeRecoveryWitness limits
            (encodeBitInput
              (fun bit : Fin (machine.witnessBits inputLength) =>
                witness.code.testBit bit.val)) = some candidate →
          RecoveryWitnessApproximates seed delta candidate := by
    intro candidate hcandidate
    rw [hdecode] at hcandidate
    exact Option.some.inj hcandidate ▸ happroximates
  exact run_eq_true_of_execute_ne_zero machine inputLength input _
    (hverifier _ hvalidator hcheck)

/-! ## Inverse-polynomial schedule -/

/-- Schedule-level form of the sole machine hypothesis.  The verifier policy
is the one length-indexed policy recovered from the public input length; no
schedule coordinate enters the request or witness ABI. -/
def InverseCaseTwoVerifierCompleteness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  ∀ (scheduleIndex : ℕ)
    (input : BitInput (sourceLength (inverseSourceIndex scheduleIndex)))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input),
    RecoveryVerifierAcceptsApproximation machine
      (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        (inverseSourceIndex scheduleIndex))
      (publishedRecoveryDelta contracts) input
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)

/-- Canonical inverse-schedule witness in the length-indexed verifier policy,
carrying the executed approximation check. -/
private theorem inverseApproximatingWitness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower scheduleIndex : ℕ)
    {input : BitInput (sourceLength (inverseSourceIndex scheduleIndex))}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (approximation :
      PublishedLegalApproximation contracts
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (inverseCopies outer (publishedPointwisePCPP contracts)
          (inverseRate contracts advantagePower)
          (inverseSourceIndex scheduleIndex))
        (inverseCaseTwoSymmetricSize contracts outer advantagePower
          scheduleIndex)
        (inverseCaseTwoThresholdSize contracts outer advantagePower
          scheduleIndex)) :
    ∃ witness : CheckedRecoveryWitness
      (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
        (inverseSourceIndex scheduleIndex)),
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness := by
  obtain ⟨witness, happroximates⟩ :=
    exists_approximatingCheckedRecoveryWitness contracts
      (inverseCopies outer (publishedPointwisePCPP contracts)
        (inverseRate contracts advantagePower)
        (inverseSourceIndex scheduleIndex))
      (inverseCaseTwoSymmetricSize contracts outer advantagePower
        scheduleIndex)
      (inverseCaseTwoThresholdSize contracts outer advantagePower
        scheduleIndex)
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
      caseTwo.circuit caseTwo.sizeBounded approximation
  exact
    ⟨witness.widen
        (inverseRecoveryWitnessLimits_weakens_sourceLimits contracts outer
          advantagePower scheduleIndex),
      recoveryWitnessApproximates_widen
        (inverseRecoveryWitnessLimits contracts outer advantagePower
          scheduleIndex)
        (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
          (inverseSourceIndex scheduleIndex))
        (inverseRecoveryWitnessLimits_weakens_sourceLimits contracts outer
          advantagePower scheduleIndex)
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness happroximates⟩

/-- Case-2 completeness for the inverse-polynomial schedule, in schedule
coordinates.  The onset is the schedule-capacity onset already proved in
`RecoveryWitnessScheduleCapacity`; no capacity field is assumed. -/
theorem inverseCaseTwoAcceptance_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      InverseCaseTwoVerifierCompleteness contracts outer advantagePower
        machine) :
    ∃ onset, ∀ scheduleIndex, onset ≤ scheduleIndex →
      ∀ (input : BitInput (sourceLength (inverseSourceIndex scheduleIndex)))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts advantagePower))
          (paddedOuterPCP outer) input),
        InverseCaseTwoAcceptance contracts outer advantagePower scheduleIndex
          caseTwo machine := by
  obtain ⟨onset, hcapacity⟩ :=
    inverseRecoveryWitnessSource_eventually_fits_at_schedule contracts outer
      advantagePower
  refine ⟨onset, fun scheduleIndex honset input caseTwo => ?_⟩
  intro approximation
  obtain ⟨witness, happroximates⟩ :=
    inverseApproximatingWitness contracts outer advantagePower scheduleIndex
      caseTwo approximation
  exact accepts_of_verifierAcceptsApproximation machine hshape
    (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
      (inverseSourceIndex scheduleIndex))
    (publishedRecoveryDelta contracts)
    (sourceLength (inverseSourceIndex scheduleIndex)) input
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (hverifier scheduleIndex input caseTwo) witness
    (hcapacity scheduleIndex honset) happroximates

/-- Target-indexed form of inverse Case-2 completeness.  This is the exact
shape consumed by the inverse recovery constructor. -/
theorem inverseCaseTwoAcceptance_eventually_at_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      InverseCaseTwoVerifierCompleteness contracts outer advantagePower
        machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ (input : BitInput
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts outer advantagePower target))))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (inverseRequiredDegree contracts advantagePower))
          (paddedOuterPCP outer) input),
        InverseCaseTwoAcceptance contracts outer advantagePower
          (inverseSelectedSource contracts outer advantagePower target)
          caseTwo machine := by
  obtain ⟨scheduleOnset, hacceptance⟩ :=
    inverseCaseTwoAcceptance_eventually contracts outer advantagePower machine
      hshape hverifier
  let envelope := inverseEnvelope contracts outer advantagePower
  refine
    ⟨max envelope.targetOnset (2 * envelope.coreArity scheduleOnset),
      fun target htarget input caseTwo => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity scheduleOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hschedule :
      scheduleOnset ≤
        inverseSelectedSource contracts outer advantagePower target :=
    (inverseSchedule contracts outer advantagePower).output_source_ge
      target henvelope scheduleOnset hsourceTarget
  exact hacceptance
    (inverseSelectedSource contracts outer advantagePower target) hschedule
    input caseTwo

/-! ## Fixed-rate schedule -/

/-- Fixed-rate form of the sole machine hypothesis. -/
def FixedCaseTwoVerifierCompleteness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) : Prop :=
  ∀ (sourceIndex : ℕ) (input : BitInput (sourceLength sourceIndex))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input),
    RecoveryVerifierAcceptsApproximation machine
      (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex)
      (publishedRecoveryDelta contracts) input
      (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)

/-- Canonical fixed-rate witness carrying the executed approximation check. -/
private theorem fixedApproximatingWitness
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate sourceIndex : ℕ)
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (approximation :
      PublishedLegalApproximation contracts
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (fixedCopies (publishedPointwisePCPP contracts)
          (fixedRate contracts requestedRate))
        (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
        (fixedCaseTwoThresholdSize contracts outer requestedRate
          sourceIndex)) :
    ∃ witness : CheckedRecoveryWitness
      (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex),
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness :=
  exists_approximatingCheckedRecoveryWitness contracts
    (fixedCopies (publishedPointwisePCPP contracts)
      (fixedRate contracts requestedRate))
    (fixedCaseTwoSymmetricSize contracts outer requestedRate sourceIndex)
    (fixedCaseTwoThresholdSize contracts outer requestedRate sourceIndex)
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    caseTwo.circuit caseTwo.sizeBounded approximation

/-- Case-2 completeness for the fixed-rate schedule, in source coordinates. -/
theorem fixedCaseTwoAcceptance_eventually
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      FixedCaseTwoVerifierCompleteness contracts outer requestedRate machine) :
    ∃ onset, ∀ sourceIndex, onset ≤ sourceIndex →
      ∀ (input : BitInput (sourceLength sourceIndex))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP outer) input),
        FixedCaseTwoAcceptance contracts outer requestedRate sourceIndex
          caseTwo machine := by
  obtain ⟨onset, hcapacity⟩ :=
    fixedRecoveryWitness_eventually_fits contracts outer requestedRate
  refine ⟨onset, fun sourceIndex honset input caseTwo => ?_⟩
  intro approximation
  obtain ⟨witness, happroximates⟩ :=
    fixedApproximatingWitness contracts outer requestedRate sourceIndex
      caseTwo approximation
  exact accepts_of_verifierAcceptsApproximation machine hshape
    (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex)
    (publishedRecoveryDelta contracts) (sourceLength sourceIndex) input
    (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
    (hverifier sourceIndex input caseTwo) witness
    (hcapacity sourceIndex honset) happroximates

/-- Target-indexed form of fixed-rate Case-2 completeness. -/
theorem fixedCaseTwoAcceptance_eventually_at_target
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (hverifier :
      FixedCaseTwoVerifierCompleteness contracts outer requestedRate machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ (input : BitInput
          (sourceLength
            (fixedSelectedSource contracts outer requestedRate target)))
        (caseTwo : CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound
            (fixedRequiredDegree contracts requestedRate))
          (paddedOuterPCP outer) input),
        FixedCaseTwoAcceptance contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          caseTwo machine := by
  obtain ⟨sourceOnset, hacceptance⟩ :=
    fixedCaseTwoAcceptance_eventually contracts outer requestedRate machine
      hshape hverifier
  let envelope := fixedEnvelope contracts outer requestedRate
  refine
    ⟨max envelope.targetOnset (2 * envelope.coreArity sourceOnset),
      fun target htarget input caseTwo => ?_⟩
  have henvelope : envelope.targetOnset ≤ target :=
    (le_max_left _ _).trans htarget
  have hsourceTarget :
      2 * envelope.coreArity sourceOnset ≤ target :=
    (le_max_right _ _).trans htarget
  have hsource :
      sourceOnset ≤
        fixedSelectedSource contracts outer requestedRate target :=
    (fixedSchedule contracts outer requestedRate).output_source_ge
      target henvelope sourceOnset hsourceTarget
  exact hacceptance
    (fixedSelectedSource contracts outer requestedRate target) hsource
    input caseTwo

/-! ## Exact `hcaseTwo` shapes at the published refuter word -/

/-- Inverse Case-2 completeness in exactly the binder shape consumed by the
inverse recovery constructor. -/
theorem inverseCaseTwoAcceptance_at_refuterInput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (advantageExponent : ℝ)
    (hverifier :
      InverseCaseTwoVerifierCompleteness contracts outer
        (inverseCoreAdvantagePower advantageExponent) machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer machine advantageExponent target),
        InverseCaseTwoAcceptance contracts outer
          (inverseCoreAdvantagePower advantageExponent)
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target)
          caseTwo machine := by
  obtain ⟨onset, hacceptance⟩ :=
    inverseCaseTwoAcceptance_eventually_at_target contracts outer
      (inverseCoreAdvantagePower advantageExponent) machine hshape hverifier
  exact ⟨onset, fun target htarget caseTwo =>
    hacceptance target htarget _ caseTwo⟩

/-- Fixed-rate Case-2 completeness in exactly the binder shape consumed by the
fixed-advantage recovery constructor. -/
theorem fixedCaseTwoAcceptance_at_refuterInput
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource
      (NearCubicWires.PolynomialClock.pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (requestedRate : ℕ)
    (hverifier :
      FixedCaseTwoVerifierCompleteness contracts outer requestedRate machine) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
        FixedCaseTwoAcceptance contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          caseTwo machine := by
  obtain ⟨onset, hacceptance⟩ :=
    fixedCaseTwoAcceptance_eventually_at_target contracts outer requestedRate
      machine hshape hverifier
  exact ⟨onset, fun target htarget caseTwo =>
    hacceptance target htarget _ caseTwo⟩

/-! ## Alignment with the verifier threshold seam

`VerifierThresholdSeam.§7` refutes the published fixed radius `1 / 4`: the
verifier's completeness direction needs `delta ≤ 3 * zeta`, and the soundness
reserve forces `6 * zeta < 1 / 288`.  `§9` closes the seam at
`repairedRecoveryDelta parameters = parameters.zeta`.  The three theorems below
compile the statement that this module's Case-2 chain — the one that ends in
`inverseCaseTwoAcceptance_at_refuterInput` and
`fixedCaseTwoAcceptance_at_refuterInput` — now runs at exactly that radius, so
the `RecoveryWitnessApproximates seed (publishedRecoveryDelta contracts)`
premise it carries and the `hclose` premise of
`repairedDelta_completeness_seam` are the same hypothesis. -/

/-- The radius of the published Case-2 XOR ledger *is* the radius the verifier's
completeness seam closes at.  Both sides are the validity constant of the
parameter package selected for the scheduled pointwise-PCPP source. -/
theorem publishedRecoveryDelta_eq_seamRadius
    (contracts : PublishedContracts) :
    publishedRecoveryDelta contracts =
      ((VerifierThresholdSeam.repairedRecoveryDelta
        (executableParametersOfSource
          (publishedPointwisePCPP contracts)) : ℚ) : ℝ) :=
  rfl

/-- **Alignment corollary.**  Every witness the Case-2 completeness chain
constructs from a published legal approximation carries its executed distance
check at the seam radius, not at the refuted literal `1 / 4`.  This is
`exists_approximatingCheckedRecoveryWitness` restated with its radius displayed
as the one `repairedDelta_completeness_seam` consumes. -/
theorem exists_approximatingCheckedRecoveryWitness_at_seamRadius
    (contracts : PublishedContracts)
    {oracleArity oracleSizeCap sumArity : ℕ}
    (copies symmetricWireCap thresholdWireCap : ℕ)
    (seed : BoolFunction sumArity)
    (oracle : BooleanCircuit oracleArity)
    (oracleSize_le : oracle.size ≤ oracleSizeCap)
    (approximation :
      PublishedLegalApproximation contracts seed copies
        symmetricWireCap thresholdWireCap) :
    ∃ witness : CheckedRecoveryWitness
      (xorRecoveryWitnessLimits (publishedXorWitness contracts)
        (publishedRecoveryDelta contracts)
        copies oracleArity oracleSizeCap sumArity
        symmetricWireCap thresholdWireCap),
      RecoveryWitnessApproximates seed
        ((VerifierThresholdSeam.repairedRecoveryDelta
          (executableParametersOfSource
            (publishedPointwisePCPP contracts)) : ℚ) : ℝ) witness := by
  obtain ⟨witness, happroximates⟩ :=
    exists_approximatingCheckedRecoveryWitness contracts copies
      symmetricWireCap thresholdWireCap seed oracle oracleSize_le
      approximation
  refine ⟨witness, ?_⟩
  rw [← publishedRecoveryDelta_eq_seamRadius contracts]
  exact happroximates

/-- The seam closes at the schedule's own radius.  Every guessed proof whose
clause-occurrence `ℓ¹` error against the honest table is inside
`publishedRecoveryDelta contracts` — the exact budget the Case-2 witness layer
enforces — forces the fixed verifier's rational comparison.  This is
`VerifierThresholdSeam.repairedDelta_completeness_seam` at the scheduled
source, and it is the step that fails at the retired literal
(`VerifierThresholdSeam.recoveryDelta_not_le_threeZeta`). -/
theorem threshold_le_estimate_of_publishedRecoveryDelta
    (contracts : PublishedContracts)
    {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (estimate : ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hhonest :
      (publishedPointwisePCPP contracts).completeness ≤
        clauseMean pcpp
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)))
    (hclose :
      VerifierThresholdSeam.clauseOccurrenceErrorMean pcpp value
          (fun j => bitAsReal (pcpp.assignment input auxiliary j)) ≤
        publishedRecoveryDelta contracts)
    (haccurate :
      |estimate - clauseMean pcpp value| ≤
        ((executableParametersOfSource
          (publishedPointwisePCPP contracts)).estimationError : ℝ)) :
    ((executableParametersOfSource
        (publishedPointwisePCPP contracts)).threshold : ℝ) ≤ estimate :=
  VerifierThresholdSeam.repairedDelta_completeness_seam pcpp input auxiliary
    (publishedPointwisePCPP contracts) value estimate hnonneg hleOne hhonest
    (by
      rw [← publishedRecoveryDelta_eq_seamRadius contracts]
      exact hclose)
    haccurate

/-! ## Regression: the executed check is not stored evidence

The following closed counterexample is a guard against a completeness proof
that reads the approximation distance out of a supplied
`CheckedRecoveryWitness`.  Every resource check of the policy succeeds while
the semantic check fails, so the distance is genuinely additional information
that the verifier must compute. -/

private def regressionOracle : BooleanCircuit 0 where
  nodes := [.const false]
  output := ⟨0, by simp⟩
  wellFormed := by
    intro index
    simp [BooleanNode.WellFormedAt]

private def regressionLegalSumLimits : LegalSumLimits where
  expectedArity := 0
  termCap := 0
  coefficientBitCap := 0
  coefficientMassCap := 0
  wireCap := 0
  descriptionCap := 0

private def regressionRecoveryWitnessLimits : RecoveryWitnessLimits where
  oracleArity := 0
  oracleSizeCap := 1
  sumArity := 0
  symmetric := regressionLegalSumLimits
  threshold := regressionLegalSumLimits
  symmetricArity := rfl
  thresholdArity := rfl

private def regressionSymmetricSum :
    CheckedLegalCircuitSum NormalizedSymmetricThresholdCircuit
      NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      regressionRecoveryWitnessLimits.symmetric where
  value := ⟨0, []⟩
  arity_eq := rfl
  terms_le := by simp
  coefficient_bits_le := by simp
  mass_le := by
    simp [LegalCircuitSumDescription.coefficientMass,
      regressionRecoveryWitnessLimits, regressionLegalSumLimits]
  wires_le := by simp
  description_le := by simp

private def regressionCheckedRecoveryWitness :
    CheckedRecoveryWitness regressionRecoveryWitnessLimits :=
  .symmetric regressionOracle (by rfl) regressionSymmetricSum

/-- A fully checked canonical witness carries no distance evidence.  The empty
legal sum satisfies every configured resource limit yet is one unit away from
the constant seed, so `RecoveryWitnessApproximates` cannot be derived from
`CheckedRecoveryWitness` alone. -/
theorem not_recoveryWitnessApproximates_of_checked :
    ¬RecoveryWitnessApproximates
      (limits := regressionRecoveryWitnessLimits) (fun _ => true) 0
      regressionCheckedRecoveryWitness := by
  rw [regressionCheckedRecoveryWitness,
    recoveryWitnessApproximates_symmetric]
  simp [l1DistanceFromBoolean, symmetricLegalSumValue, transportedSeed,
    bitAsReal, regressionSymmetricSum]

end NearCubicWires.CaseTwoWitnessCompleteness
