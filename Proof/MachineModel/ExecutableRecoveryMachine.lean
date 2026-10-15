import Proof.Amplification.CanonicalRecoveryRequest
import Proof.MachineModel.CanonicalRecoveryValidatorProgram
import Proof.CaseAnalysis.CaseTwoWitnessCompleteness
import Proof.Foundations.QuotientBudgetCurrency
import Proof.MachineModel.QuotientProgramConversion

namespace NearCubicWires.ExecutableRecoveryMachine

open NearCubicWires
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoWitnessCompleteness
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RecoveryWitnessScheduleCapacity
open NearCubicWires.RecoveryWitnessShape
open NearCubicWires.ScheduledRecovery
open NearCubicWires.VerifiedLinker

/-! ## §1 Packaging one exact run at a polynomial budget

The polynomial counterpart of `exponentialNatProgramOfRun`.  Its inputs are a
fixed instruction stream, a closed coefficient/degree pair, and one exact run
theorem with explicitly charged width and fuel; no fuel argument, callback, or
existentially supplied implementation crosses the boundary. -/

private theorem run_at_polynomialBudget
    {program : NPOracleProgram} {bits fuel budget length code output : ℕ}
    (hbits : bits ≤ budget) (hfuel : fuel ≤ budget)
    (hrun :
      runNPOracleProgram program bits fuel
        (initialNPOracleState length code) = some output) :
    runNPOracleProgram program budget budget
        (initialNPOracleState length code) = some output := by
  have hwide := run_bits_mono hrun hbits
  have hmore := run_fuel_add hwide (budget - fuel)
  rwa [Nat.add_sub_cancel' hfuel] at hmore

/-- The single polynomial-budget runner constructor used by the machine. -/
def polynomialNatProgramOfRun {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (program : NPOracleProgram) (coefficient degree : ℕ)
    (hcoefficient : 0 < coefficient)
    (bits fuel output : Request → ℕ)
    (hbits : ∀ request,
      bits request ≤ polynomialBudget coefficient degree (measure request))
    (hfuel : ∀ request,
      fuel request ≤ polynomialBudget coefficient degree (measure request))
    (hinitial : ∀ request,
      natBitLength (max (inputLength request) (requestCode request)) ≤
        polynomialBudget coefficient degree (measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (inputLength request) (requestCode request)) =
        some (output request)) :
    PolynomialNatProgram Request inputLength requestCode measure where
  program := program
  coefficient := coefficient
  coefficientPositive := hcoefficient
  degree := degree
  initialBitsFit := hinitial
  halts := fun request =>
    ⟨output request,
      run_at_polynomialBudget (hbits request) (hfuel request) (hrun request)⟩

theorem polynomialNatProgramOfRun_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (program : NPOracleProgram) (coefficient degree : ℕ)
    (hcoefficient : 0 < coefficient)
    (bits fuel output : Request → ℕ)
    (hbits : ∀ request,
      bits request ≤ polynomialBudget coefficient degree (measure request))
    (hfuel : ∀ request,
      fuel request ≤ polynomialBudget coefficient degree (measure request))
    (hinitial : ∀ request,
      natBitLength (max (inputLength request) (requestCode request)) ≤
        polynomialBudget coefficient degree (measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (inputLength request) (requestCode request)) =
        some (output request))
    (request : Request) :
    (polynomialNatProgramOfRun (inputLength := inputLength)
      (requestCode := requestCode) (measure := measure)
      program coefficient degree hcoefficient bits fuel output hbits hfuel
      hinitial hrun).execute request = output request := by
  have hwide :=
    run_at_polynomialBudget (program := program) (hbits request)
      (hfuel request) (hrun request)
  simp only [PolynomialNatProgram.execute, PolynomialNatProgram.toBounded,
    BoundedNatProgram.execute, PolynomialNatProgram.budget,
    polynomialNatProgramOfRun, hwide]
  rfl

/-! ## §2 The composed recovery verifier program -/

/-- Length-indexed raw validator: the limits front end followed by the
complete recovery-witness validator endpoint. -/
def recoveryVerifierValidatorProgram
    (limitsFrontEnd : NPOracleProgram) : NPOracleProgram :=
  linkPrograms limitsFrontEnd recoveryWitnessValidatorProgram

theorem recoveryVerifierValidatorProgram_oracleFree
    {limitsFrontEnd : NPOracleProgram} (hfrontEnd : OracleFree limitsFrontEnd) :
    OracleFree (recoveryVerifierValidatorProgram limitsFrontEnd) :=
  oracleFree_linkPrograms hfrontEnd recoveryWitnessValidatorProgram_oracleFree

def recoveryVerifierValidatorBits (frontEndBits inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  max (natBitLength inputLength)
    (max frontEndBits (recoveryWitnessValidatorBits inputLength limits raw))

def recoveryVerifierValidatorFuel (frontEndFuel inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ) : ℕ :=
  linkFuel recoveryWitnessValidatorProgram frontEndFuel
    (recoveryWitnessValidatorFuel inputLength limits raw)

theorem run_recoveryVerifierValidatorProgram
    (limitsFrontEnd : NPOracleProgram)
    (frontEndBits frontEndFuel inputLength : ℕ)
    (limits : RecoveryWitnessLimits) (raw : ℕ)
    (hfrontEnd :
      runNPOracleProgram limitsFrontEnd frontEndBits frontEndFuel
          (initialNPOracleState inputLength raw) =
        some (recoveryWitnessValidatorInput limits raw)) :
    runNPOracleProgram (recoveryVerifierValidatorProgram limitsFrontEnd)
        (recoveryVerifierValidatorBits frontEndBits inputLength limits raw)
        (recoveryVerifierValidatorFuel frontEndFuel inputLength limits raw)
        (initialNPOracleState inputLength raw) =
      some (recoveryWitnessValidatorProgramOutput inputLength limits raw) := by
  have hlength :
      natBitLength inputLength ≤
        recoveryVerifierValidatorBits frontEndBits inputLength limits raw :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryVerifierValidatorBits frontEndBits inputLength limits raw := by
    refine le_trans ?_ hlength
    unfold natBitLength
    omega
  have hfrontEndBits :
      frontEndBits ≤
        recoveryVerifierValidatorBits frontEndBits inputLength limits raw :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hvalidatorBits :
      recoveryWitnessValidatorBits inputLength limits raw ≤
        recoveryVerifierValidatorBits frontEndBits inputLength limits raw :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hfrontEnd hfrontEndBits)
    (run_bits_mono (run_recoveryWitnessValidatorProgram inputLength limits raw)
      hvalidatorBits)

/-- **The fixed recovery verifier instruction stream.**  The request front end
retains the public input across validation; the semantic stage sees the gate
output, which is the zero sentinel on every rejected witness. -/
def recoveryVerifierProgram
    (limitsFrontEnd semanticStage : NPOracleProgram) : NPOracleProgram :=
  linkPrograms
    (recoveryWitnessRequestProgram
      (recoveryVerifierValidatorProgram limitsFrontEnd))
    semanticStage

theorem recoveryVerifierProgram_oracleFree
    {limitsFrontEnd semanticStage : NPOracleProgram}
    (hfrontEnd : OracleFree limitsFrontEnd)
    (hsemantic : OracleFree semanticStage) :
    OracleFree (recoveryVerifierProgram limitsFrontEnd semanticStage) :=
  oracleFree_linkPrograms
    (recoveryWitnessRequestProgram_oracleFree
      (recoveryVerifierValidatorProgram_oracleFree hfrontEnd))
    hsemantic

def recoveryVerifierRequestBits (frontEndBits : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) : ℕ :=
  recoveryWitnessRequestBits
    (recoveryVerifierValidatorBits frontEndBits request.length limits
      (encodeBitInput request.witness))
    (recoveryWitnessValidatorOutput limits (encodeBitInput request.witness))
    request

def recoveryVerifierRequestFuel (limitsFrontEnd : NPOracleProgram)
    (frontEndFuel : ℕ) (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  recoveryWitnessRequestFuel (recoveryVerifierValidatorProgram limitsFrontEnd)
    (recoveryVerifierValidatorFuel frontEndFuel request.length limits
      (encodeBitInput request.witness))
    (recoveryWitnessValidatorOutput limits (encodeBitInput request.witness))

def recoveryVerifierBits (frontEndBits semanticBits : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) : ℕ :=
  max (natBitLength request.length)
    (max (recoveryVerifierRequestBits frontEndBits limits request) semanticBits)

def recoveryVerifierFuel (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndFuel semanticFuel : ℕ) (limits : RecoveryWitnessLimits)
    (request : WeakVerifierRequest) : ℕ :=
  linkFuel semanticStage
    (recoveryVerifierRequestFuel limitsFrontEnd frontEndFuel limits request)
    semanticFuel

/-- Exact execution of the composed verifier stream.  The two premises are the
limits front end's run theorem and the semantic stage's run theorem; the
validator endpoint, its unconditional identification with the pure
specification, and every plumbing stage are discharged from the compiled
components. -/
theorem run_recoveryVerifierProgram
    (limitsFrontEnd semanticStage : NPOracleProgram)
    (frontEndBits frontEndFuel semanticBits semanticFuel : ℕ)
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (semanticValue : ℕ)
    (hfrontEnd :
      runNPOracleProgram limitsFrontEnd frontEndBits frontEndFuel
          (initialNPOracleState request.length
            (encodeBitInput request.witness)) =
        some
          (recoveryWitnessValidatorInput limits
            (encodeBitInput request.witness)))
    (hsemantic :
      runNPOracleProgram semanticStage semanticBits semanticFuel
          (initialNPOracleState request.length
            (recoveryWitnessValidatorRequestOutput limits request)) =
        some semanticValue) :
    runNPOracleProgram (recoveryVerifierProgram limitsFrontEnd semanticStage)
        (recoveryVerifierBits frontEndBits semanticBits limits request)
        (recoveryVerifierFuel limitsFrontEnd semanticStage frontEndFuel
          semanticFuel limits request)
        (initialNPOracleState request.length request.code) =
      some semanticValue := by
  have hlength :
      natBitLength request.length ≤
        recoveryVerifierBits frontEndBits semanticBits limits request :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ recoveryVerifierBits frontEndBits semanticBits limits request := by
    refine le_trans ?_ hlength
    unfold natBitLength
    omega
  have hrequestBits :
      recoveryVerifierRequestBits frontEndBits limits request ≤
        recoveryVerifierBits frontEndBits semanticBits limits request :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsemanticBits :
      semanticBits ≤
        recoveryVerifierBits frontEndBits semanticBits limits request :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hvalidator :
      runNPOracleProgram (recoveryVerifierValidatorProgram limitsFrontEnd)
          (recoveryVerifierValidatorBits frontEndBits request.length limits
            (encodeBitInput request.witness))
          (recoveryVerifierValidatorFuel frontEndFuel request.length limits
            (encodeBitInput request.witness))
          (initialNPOracleState request.length
            (encodeBitInput request.witness)) =
        some
          (recoveryWitnessValidatorOutput limits
            (encodeBitInput request.witness)) := by
    rw [← recoveryWitnessValidatorProgramOutput_eq request.length limits
      (encodeBitInput request.witness)]
    exact run_recoveryVerifierValidatorProgram limitsFrontEnd frontEndBits
      frontEndFuel request.length limits (encodeBitInput request.witness)
      hfrontEnd
  have hrequest :=
    run_recoveryWitnessRequestProgram
      (recoveryVerifierValidatorProgram limitsFrontEnd) request
      (recoveryVerifierValidatorBits frontEndBits request.length limits
        (encodeBitInput request.witness))
      (recoveryVerifierValidatorFuel frontEndFuel request.length limits
        (encodeBitInput request.witness))
      (recoveryWitnessValidatorOutput limits
        (encodeBitInput request.witness))
      hvalidator
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hrequest hrequestBits)
    (run_bits_mono hsemantic hsemanticBits)

/-! ## §3 The degree envelope, the runner, and the machine -/

private theorem recoveryVerifier_initialBitsFit (coefficient : ℕ)
    (hcoefficient : 4 ≤ coefficient) :
    ∀ request : WeakVerifierRequest,
      natBitLength
          (max (WeakVerifierRequest.length request)
            (WeakVerifierRequest.code request)) ≤
        polynomialBudget coefficient recoveryVerifierDegree
          (WeakVerifierRequest.measure request) := by
  intro request
  have hcode : natBitLength request.code ≤ 4 * (request.measure + 1) :=
    weakVerifierRequest_codeBits_le request
  have hlengthLe : request.length ≤ request.measure := by
    simp [WeakVerifierRequest.length, WeakVerifierRequest.measure]
  have hlength : natBitLength request.length ≤ request.measure + 1 :=
    (natBitLength_le_succ request.length).trans (by omega)
  have hmax :
      natBitLength
          (max (WeakVerifierRequest.length request)
            (WeakVerifierRequest.code request)) ≤
        4 * (request.measure + 1) := by
    rcases le_total (WeakVerifierRequest.length request)
      (WeakVerifierRequest.code request) with hle | hle
    · rw [max_eq_right hle]
      exact hcode
    · rw [max_eq_left hle]
      omega
  refine hmax.trans ?_
  have hpow :
      request.measure + 1 ≤
        (request.measure + 1) ^ recoveryVerifierDegree :=
    Nat.le_self_pow (by simp [recoveryVerifierDegree]) _
  exact Nat.mul_le_mul hcoefficient hpow

/-! ## §4 The two semantic obligations

Both are stated for an arbitrary machine whose verifier execution is known,
so `executableRecoveryMachine` instantiates them through
`executableRecoveryMachine_verifier_execute` and
`executableRecoveryMachine_witnessShape`.  The validation half of the
composed verifier is discharged unconditionally in each; only the semantic
stage remains, as a single named premise. -/

/-- The gate the semantic stage reads is nonzero exactly when the pure
full-validator specification accepts the guessed code.  This is the half of
the completeness obligation the composition closes on its own. -/
theorem recoveryWitnessValidatorRequestOutput_ne_zero_iff_pure
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest) :
    recoveryWitnessValidatorRequestOutput limits request ≠ 0 ↔
      recoveryWitnessValidatorOutput limits
        (encodeBitInput request.witness) ≠ 0 :=
  recoveryWitnessValidationGateOutput_ne_zero_iff _ _

/-- Fail-closed regression: a witness the pure specification rejects reaches
the semantic stage as the global zero sentinel, so no semantic stage can turn
an unvalidated code into an accepting branch. -/
theorem recoveryWitnessValidatorRequestOutput_eq_zero_of_reject
    (limits : RecoveryWitnessLimits) (request : WeakVerifierRequest)
    (hreject :
      recoveryWitnessValidatorOutput limits
        (encodeBitInput request.witness) = 0) :
    recoveryWitnessValidatorRequestOutput limits request = 0 := by
  by_contra hnonzero
  exact
    ((recoveryWitnessValidatorRequestOutput_ne_zero_iff_pure limits
      request).1 hnonzero) hreject

/-- **Completeness obligation.**  With the semantic stage's acceptance as the
single premise, the composed verifier accepts every validated approximating
witness, which is exactly `RecoveryVerifierAcceptsApproximation`. -/
theorem recoveryVerifierAcceptsApproximation_of_semanticStage
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (limits : RecoveryWitnessLimits) (delta : ℝ)
    {inputLength : ℕ} (input : BitInput inputLength)
    (seed : BoolFunction limits.sumArity)
    (hsemanticAccepts :
      ∀ bits : BitInput (machine.witnessBits inputLength),
        recoveryWitnessValidatorOutput limits (encodeBitInput bits) ≠ 0 →
        (∀ witness : CheckedRecoveryWitness limits,
          decodeRecoveryWitness limits (encodeBitInput bits) = some witness →
          RecoveryWitnessApproximates seed delta witness) →
        semanticOutput (machine.verifierRequest input bits) ≠ 0) :
    RecoveryVerifierAcceptsApproximation machine limits delta input seed := by
  intro bits hvalidator hcheck
  rw [hexecute]
  exact hsemanticAccepts bits hvalidator hcheck

/-- Every accepting nondeterministic branch of the machine is a nonzero
semantic-stage output.  This is the half of the one-sidedness obligation the
composition closes on its own. -/
theorem semanticOutput_ne_zero_of_run
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    {inputLength : ℕ} (input : BitInput inputLength)
    (witness : BitInput (machine.witnessBits inputLength))
    (haccepts : machine.run inputLength input witness = true) :
    semanticOutput (machine.verifierRequest input witness) ≠ 0 := by
  rw [← hexecute]
  unfold ExecutableWeakNondeterministicMachine.run at haccepts
  simpa using haccepts

/-- The accepting-branch evidence in the shape the verifier's exact rational
comparison produces it: range checks and the validity charge as rational
inequalities, the supplier accuracy ledger, and the final threshold
comparison. -/
noncomputable def acceptingBranchEvidenceOfRationalChecks
    (source : UniformPointwisePCPPSource) {n : ℕ}
    (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size)
    (input : BitInput n) (hreject : ¬circuit.eval input)
    (supportBound :
      ∀ i,
        ((source.factory.forCircuit circuit).systematicSupport i).card ≤
          n / 2)
    (proofValue :
      Fin
        (((source.factory.forCircuit circuit).toSemantic
            supportBound).systematicBits +
          ((source.factory.forCircuit circuit).toSemantic
            supportBound).auxiliaryBits) → ℚ)
    (hnonneg : ∀ j, 0 ≤ proofValue j) (hleOne : ∀ j, proofValue j ≤ 1)
    (hvalidity :
      rationalTotalClausePenaltyCharge
          ((source.factory.forCircuit circuit).toSemantic supportBound) input
          proofValue ≤
        6 * (executableParametersOfSource source).zeta)
    (estimateCode : ℚ)
    (haccurate :
      |(estimateCode : ℝ) -
          clauseMean
            ((source.factory.forCircuit circuit).toSemantic supportBound)
            (fun j => (proofValue j : ℝ))| ≤
        ((executableParametersOfSource source).estimationError : ℝ))
    (hthreshold :
      (executableParametersOfSource source).threshold ≤ estimateCode) :
    AcceptingBranchEvidence (executableParametersOfSource source) :=
  AcceptingBranchEvidence.ofSelectedSource source circuit hsize input hreject
    supportBound
    (ComponentwiseVerifierTrace.ofRationalChecks
      ((source.factory.forCircuit circuit).toSemantic supportBound) input
      (executableParametersOfSource source) proofValue hnonneg hleOne
      hvalidity estimateCode haccurate hthreshold)

/-- **One-sidedness obligation.**  With the semantic stage's accepting-trace
evidence as the single premise, one-sidedness holds for the machine at the
canonically selected verifier constants. -/
theorem eventuallyOneSided_of_semanticStageEvidence {hierarchy : Language}
    (source : UniformPointwisePCPPSource)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (onset : ℕ)
    (hsemanticEvidence :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        hierarchy n input = false →
        ∀ witness : BitInput (machine.witnessBits n),
          semanticOutput (machine.verifierRequest input witness) ≠ 0 →
            Nonempty
              (AcceptingBranchEvidence
                (executableParametersOfSource source))) :
    EventuallyOneSided hierarchy machine := by
  refine eventuallyOneSided_of_selectedSourceEvidence source machine onset ?_
  intro n hn input hno witness haccepts
  exact hsemanticEvidence n hn input hno witness
    (semanticOutput_ne_zero_of_run machine semanticOutput hexecute input
      witness haccepts)

/-! ## §5 The schedule-level assembly corollaries

Both published schedules reduce their Case-2 completeness obligation to the
same single semantic-stage premise; the validator half of the composed
verifier is already discharged in §4. -/

/-- The remaining semantic-stage premise on the inverse-polynomial schedule:
the stage accepts every guessed code that the pure full-validator
specification accepts and whose decoded witness lies inside the published
approximation radius. -/
def InverseSemanticStageAccepts {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ) : Prop :=
  ∀ (scheduleIndex : ℕ)
    (input : BitInput (sourceLength (inverseSourceIndex scheduleIndex)))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (inverseRequiredDegree contracts advantagePower))
      (paddedOuterPCP outer) input)
    (bits : BitInput
      (machine.witnessBits (sourceLength (inverseSourceIndex scheduleIndex)))),
    recoveryWitnessValidatorOutput
        (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
          (inverseSourceIndex scheduleIndex)) (encodeBitInput bits) ≠ 0 →
    (∀ witness : CheckedRecoveryWitness
        (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
          (inverseSourceIndex scheduleIndex)),
      decodeRecoveryWitness
          (inverseRecoveryWitnessSourceLimits contracts outer advantagePower
            (inverseSourceIndex scheduleIndex)) (encodeBitInput bits) =
        some witness →
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness) →
    semanticOutput (machine.verifierRequest input bits) ≠ 0

/-- The same premise on the fixed-rate schedule. -/
def FixedSemanticStageAccepts {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ) : Prop :=
  ∀ (sourceIndex : ℕ) (input : BitInput (sourceLength sourceIndex))
    (caseTwo : CanonicalAcceptingOracle
      (sizeBound := oracleSizeBound
        (fixedRequiredDegree contracts requestedRate))
      (paddedOuterPCP outer) input)
    (bits : BitInput (machine.witnessBits (sourceLength sourceIndex))),
    recoveryWitnessValidatorOutput
        (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex)
        (encodeBitInput bits) ≠ 0 →
    (∀ witness : CheckedRecoveryWitness
        (fixedRecoveryWitnessLimits contracts outer requestedRate sourceIndex),
      decodeRecoveryWitness
          (fixedRecoveryWitnessLimits contracts outer requestedRate
            sourceIndex) (encodeBitInput bits) = some witness →
      RecoveryWitnessApproximates
        (caseTwoSeed (publishedPointwisePCPP contracts) caseTwo)
        (publishedRecoveryDelta contracts) witness) →
    semanticOutput (machine.verifierRequest input bits) ≠ 0

theorem inverseCaseTwoVerifierCompleteness_of_semanticStage {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantagePower : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (hsemantic :
      InverseSemanticStageAccepts contracts outer advantagePower machine
        semanticOutput) :
    InverseCaseTwoVerifierCompleteness contracts outer advantagePower
      machine := by
  intro scheduleIndex input caseTwo
  exact recoveryVerifierAcceptsApproximation_of_semanticStage machine
    semanticOutput hexecute _ _ input _
    (hsemantic scheduleIndex input caseTwo)

theorem fixedCaseTwoVerifierCompleteness_of_semanticStage {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (hsemantic :
      FixedSemanticStageAccepts contracts outer requestedRate machine
        semanticOutput) :
    FixedCaseTwoVerifierCompleteness contracts outer requestedRate machine := by
  intro sourceIndex input caseTwo
  exact recoveryVerifierAcceptsApproximation_of_semanticStage machine
    semanticOutput hexecute _ _ input _ (hsemantic sourceIndex input caseTwo)

/-- **`hcaseTwo`, inverse schedule.**  Exactly the binder shape consumed by
the inverse recovery constructor, modulo the single semantic-stage premise. -/
theorem inverseCaseTwoAcceptance_of_semanticStage {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (advantageExponent : ℝ)
    (hsemantic :
      InverseSemanticStageAccepts contracts outer
        (inverseCoreAdvantagePower advantageExponent) machine
        semanticOutput) :
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
          caseTwo machine :=
  inverseCaseTwoAcceptance_at_refuterInput contracts outer machine hshape
    advantageExponent
    (inverseCaseTwoVerifierCompleteness_of_semanticStage contracts outer
      (inverseCoreAdvantagePower advantageExponent) machine semanticOutput
      hexecute hsemantic)

/-- **`hcaseTwo`, fixed-advantage schedule.** -/
theorem fixedCaseTwoAcceptance_of_semanticStage {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (machine : ExecutableWeakNondeterministicMachine)
    (hshape : machine.witnessShape = recoveryWitnessShape)
    (semanticOutput : WeakVerifierRequest → ℕ)
    (hexecute : ∀ request : WeakVerifierRequest,
      machine.verifier.execute request = semanticOutput request)
    (requestedRate : ℕ)
    (hsemantic :
      FixedSemanticStageAccepts contracts outer requestedRate machine
        semanticOutput) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer machine requestedRate target),
        FixedCaseTwoAcceptance contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          caseTwo machine :=
  fixedCaseTwoAcceptance_at_refuterInput contracts outer machine hshape
    requestedRate
    (fixedCaseTwoVerifierCompleteness_of_semanticStage contracts outer
      requestedRate machine semanticOutput hexecute hsemantic)

/-! ## §6 The concrete machine and its terminal obligations -/

section Assembly

variable (limitsOf : ℕ → RecoveryWitnessLimits)
  (limitsFrontEnd semanticStage : NPOracleProgram)
  (frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput :
    WeakVerifierRequest → ℕ)
  (coefficient : ℕ) (hcoefficient : 4 ≤ coefficient)
  (hlimitsFrontEnd : ∀ request : WeakVerifierRequest,
    runNPOracleProgram limitsFrontEnd (frontEndBits request)
        (frontEndFuel request)
        (initialNPOracleState request.length
          (encodeBitInput request.witness)) =
      some
        (recoveryWitnessValidatorInput (limitsOf request.inputArity)
          (encodeBitInput request.witness)))
  (hsemanticStage : ∀ request : WeakVerifierRequest,
    runNPOracleProgram semanticStage (semanticBits request)
        (semanticFuel request)
        (initialNPOracleState request.length
          (recoveryWitnessValidatorRequestOutput
            (limitsOf request.inputArity) request)) =
      some (semanticOutput request))
  (hbits : ∀ request : WeakVerifierRequest,
    recoveryVerifierBits (frontEndBits request) (semanticBits request)
        (limitsOf request.inputArity) request ≤
      polynomialBudget coefficient recoveryVerifierDegree request.measure)
  (hfuel : ∀ request : WeakVerifierRequest,
    recoveryVerifierFuel limitsFrontEnd semanticStage (frontEndFuel request)
        (semanticFuel request) (limitsOf request.inputArity) request ≤
      polynomialBudget coefficient recoveryVerifierDegree request.measure)
  (hfrontEndFree : OracleFree limitsFrontEnd)
  (hsemanticFree : OracleFree semanticStage)

/-- The fixed recovery verifier as a polynomial runner.  Its degree is the
closed envelope `recoveryVerifierDegree`, never a function of the selected
source. -/
def executableRecoveryVerifier :
    PolynomialNatProgram WeakVerifierRequest WeakVerifierRequest.length
      WeakVerifierRequest.code WeakVerifierRequest.measure :=
  polynomialNatProgramOfRun
    (recoveryVerifierProgram limitsFrontEnd semanticStage) coefficient
    recoveryVerifierDegree (by omega)
    (fun request =>
      recoveryVerifierBits (frontEndBits request) (semanticBits request)
        (limitsOf request.inputArity) request)
    (fun request =>
      recoveryVerifierFuel limitsFrontEnd semanticStage (frontEndFuel request)
        (semanticFuel request) (limitsOf request.inputArity) request)
    semanticOutput hbits hfuel
    (recoveryVerifier_initialBitsFit coefficient hcoefficient)
    (fun request =>
      run_recoveryVerifierProgram limitsFrontEnd semanticStage
        (frontEndBits request) (frontEndFuel request) (semanticBits request)
        (semanticFuel request) (limitsOf request.inputArity) request
        (semanticOutput request) (hlimitsFrontEnd request)
        (hsemanticStage request))

theorem executableRecoveryVerifier_execute (request : WeakVerifierRequest) :
    (executableRecoveryVerifier limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel).execute request =
      semanticOutput request :=
  polynomialNatProgramOfRun_execute _ _ _ _ _ _ _ _ _ _ _ request

/-- **The executable weak nondeterministic recovery machine.**  It installs
the fixed executable witness shape `n / 16` and the composed recovery
verifier; both programs are oracle-free. -/
def executableRecoveryMachine : ExecutableWeakNondeterministicMachine where
  witnessShape := recoveryWitnessShape
  witnessShapeOracleFree := recoveryWitnessShapeProgram_oracleFree
  verifier :=
    (executableRecoveryVerifier limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd
      hsemanticStage hbits hfuel).toQuotient
      honestRecoveryDegree savingExponent
      (by change recoveryVerifierDegree + 2 * savingExponent ≤
            honestRecoveryDegree
          decide)
  verifierOracleFree :=
    recoveryVerifierProgram_oracleFree hfrontEndFree hsemanticFree

/-- The terminal `hwitnessShape` obligation of the published recovery
constructors, by definitional equality. -/
theorem executableRecoveryMachine_witnessShape :
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel hfrontEndFree
        hsemanticFree).witnessShape = recoveryWitnessShape :=
  rfl

theorem executableRecoveryMachine_verifier_degree :
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel hfrontEndFree
        hsemanticFree).verifier.degree = honestRecoveryDegree :=
  rfl

theorem executableRecoveryMachine_verifier_execute
    (request : WeakVerifierRequest) :
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel hfrontEndFree
        hsemanticFree).verifier.execute request = semanticOutput request :=
  (PolynomialNatProgram.toQuotient_execute
      (executableRecoveryVerifier limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel)
      honestRecoveryDegree savingExponent
      (by change recoveryVerifierDegree + 2 * savingExponent ≤
            honestRecoveryDegree
          decide) request).trans
    (executableRecoveryVerifier_execute limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd
      hsemanticStage hbits hfuel request)

theorem executableRecoveryMachine_degree_le_clock :
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel hfrontEndFree hsemanticFree).verifier.degree ≤
      2 ^ (recoveryVerifierDegree + 1) := by
  rw [executableRecoveryMachine_verifier_degree]
  exact Nat.le.refl

theorem executableRecoveryMachine_verifier_logPower :
    1 ≤ (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd
        hsemanticStage hbits hfuel hfrontEndFree
        hsemanticFree).verifier.logPower :=
  Nat.le.refl

/-- **`honeSided` for the constructed machine at the published refuter
source.**  The clock depth is the closed numeral `recoveryVerifierDegree + 1`,
which is definitionally the depth the published closure derives from
`verifier.degree + 1`; no source is consulted to obtain it. -/
theorem executableRecoveryMachine_eventuallyOneSided
    (contracts : PublishedContracts) (onset : ℕ)
    (hsemanticEvidence :
      ∀ n, onset ≤ n → ∀ input : BitInput n,
        (publishedRefuterSource contracts
            (recoveryVerifierDegree + 1)).hierarchyMachine.accepts n input =
          false →
        ∀ witness : BitInput
          ((executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
            frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
            coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
            hfrontEndFree hsemanticFree).witnessBits n),
          semanticOutput
              ((executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
                frontEndBits frontEndFuel semanticBits semanticFuel
                semanticOutput coefficient hcoefficient hlimitsFrontEnd
                hsemanticStage hbits hfuel hfrontEndFree
                hsemanticFree).verifierRequest input witness) ≠ 0 →
            Nonempty
              (AcceptingBranchEvidence
                (executableParametersOfSource
                  (publishedPointwisePCPP contracts)))) :
    EventuallyOneSided
      (publishedRefuterSource contracts
        (recoveryVerifierDegree + 1)).hierarchyMachine.accepts
      (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
        frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
        coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
        hfrontEndFree hsemanticFree) :=
  eventuallyOneSided_of_semanticStageEvidence
    (publishedPointwisePCPP contracts)
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
      hfrontEndFree hsemanticFree)
    semanticOutput
    (executableRecoveryMachine_verifier_execute limitsOf limitsFrontEnd
      semanticStage frontEndBits frontEndFuel semanticBits semanticFuel
      semanticOutput coefficient hcoefficient hlimitsFrontEnd hsemanticStage
      hbits hfuel hfrontEndFree hsemanticFree)
    onset hsemanticEvidence

/-- **`hcaseTwo` for the constructed machine, inverse-polynomial schedule.** -/
theorem executableRecoveryMachine_inverseCaseTwoAcceptance {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ)
    (hsemantic :
      InverseSemanticStageAccepts contracts outer
        (inverseCoreAdvantagePower advantageExponent)
        (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
          frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
          coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
          hfrontEndFree hsemanticFree)
        semanticOutput) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        (paddedOuterPCP outer)
        (inverseRefuterInput contracts outer
          (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
            frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
            coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
            hfrontEndFree hsemanticFree)
          advantageExponent target),
        InverseCaseTwoAcceptance contracts outer
          (inverseCoreAdvantagePower advantageExponent)
          (inverseSelectedSource contracts outer
            (inverseCoreAdvantagePower advantageExponent) target)
          caseTwo
          (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
            frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
            coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
            hfrontEndFree hsemanticFree) :=
  inverseCaseTwoAcceptance_of_semanticStage contracts outer
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
      hfrontEndFree hsemanticFree)
    (executableRecoveryMachine_witnessShape limitsOf limitsFrontEnd
      semanticStage frontEndBits frontEndFuel semanticBits semanticFuel
      semanticOutput coefficient hcoefficient hlimitsFrontEnd hsemanticStage
      hbits hfuel hfrontEndFree hsemanticFree)
    semanticOutput
    (executableRecoveryMachine_verifier_execute limitsOf limitsFrontEnd
      semanticStage frontEndBits frontEndFuel semanticBits semanticFuel
      semanticOutput coefficient hcoefficient hlimitsFrontEnd hsemanticStage
      hbits hfuel hfrontEndFree hsemanticFree)
    advantageExponent hsemantic

/-- **`hcaseTwo` for the constructed machine, fixed-advantage schedule.** -/
theorem executableRecoveryMachine_fixedCaseTwoAcceptance {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate : ℕ)
    (hsemantic :
      FixedSemanticStageAccepts contracts outer requestedRate
        (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
          frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
          coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
          hfrontEndFree hsemanticFree)
        semanticOutput) :
    ∃ onset, ∀ target, onset ≤ target →
      ∀ caseTwo : CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound
          (fixedRequiredDegree contracts requestedRate))
        (paddedOuterPCP outer)
        (fixedRefuterInput contracts outer
          (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
            frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
            coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
            hfrontEndFree hsemanticFree)
          requestedRate target),
        FixedCaseTwoAcceptance contracts outer requestedRate
          (fixedSelectedSource contracts outer requestedRate target)
          caseTwo
          (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
            frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
            coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
            hfrontEndFree hsemanticFree) :=
  fixedCaseTwoAcceptance_of_semanticStage contracts outer
    (executableRecoveryMachine limitsOf limitsFrontEnd semanticStage
      frontEndBits frontEndFuel semanticBits semanticFuel semanticOutput
      coefficient hcoefficient hlimitsFrontEnd hsemanticStage hbits hfuel
      hfrontEndFree hsemanticFree)
    (executableRecoveryMachine_witnessShape limitsOf limitsFrontEnd
      semanticStage frontEndBits frontEndFuel semanticBits semanticFuel
      semanticOutput coefficient hcoefficient hlimitsFrontEnd hsemanticStage
      hbits hfuel hfrontEndFree hsemanticFree)
    semanticOutput
    (executableRecoveryMachine_verifier_execute limitsOf limitsFrontEnd
      semanticStage frontEndBits frontEndFuel semanticBits semanticFuel
      semanticOutput coefficient hcoefficient hlimitsFrontEnd hsemanticStage
      hbits hfuel hfrontEndFree hsemanticFree)
    requestedRate hsemantic

end Assembly

end NearCubicWires.ExecutableRecoveryMachine
