import Proof.Foundations.ExecutableInterfaces

/-!
# Receipt-backed executable hierarchy sources

`TimedDecisionMachine` is retained as a legacy semantic view only.  At the
source boundary, one fixed `ExecutableLanguageProgram` determines both
acceptance and the charged step budget.  The receipt theorem below ties that
budget to the actual interpreter invocation.

The projection-PCP guarantee is deliberately quantified over executable
programs rather than arbitrary pairs of semantic acceptance and step
functions.  Results still project to the existing executable and semantic PCP
views, so internal consumers do not need a second PCP representation.
-/

namespace NearCubicWires.ExecutableProgramTimedSource

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

def programSteps
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) : ℕ :=
  program.runner.budget (program.request input)

/-- The only permitted timed view of an executable hierarchy program. -/
def toTimedDecisionMachine
    (program : ExecutableLanguageProgram) : TimedDecisionMachine where
  accepts := program.language
  steps := programSteps program

@[simp] theorem toTimedDecisionMachine_accepts
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) :
    (toTimedDecisionMachine program).accepts n input = program.language n input :=
  rfl

@[simp] theorem toTimedDecisionMachine_steps
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) :
    (toTimedDecisionMachine program).steps n input =
      program.runner.budget (program.request input) :=
  rfl

/-- The charged steps are the fuel and register-width supplied to the fixed
interpreter in a literal halting receipt; they are not an author-supplied
counter attached to the language. -/
theorem run_at_timedSteps
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) :
    runNPOracleProgram program.runner.program
        ((toTimedDecisionMachine program).steps n input)
        ((toTimedDecisionMachine program).steps n input)
        (initialNPOracleState n
          (LanguageEvaluationRequest.code (program.request input))) =
      some (program.language n input).toNat := by
  rw [toTimedDecisionMachine_steps]
  calc
    runNPOracleProgram program.runner.program
        (program.runner.budget (program.request input))
        (program.runner.budget (program.request input))
        (initialNPOracleState n
          (LanguageEvaluationRequest.code (program.request input))) =
        some (program.runner.execute (program.request input)) := by
      simpa [LanguageEvaluationRequest.length,
        ExecutableLanguageProgram.request] using
          program.runner.run_eq_execute (program.request input)
    _ = some (program.language n input).toNat :=
      congrArg some (program.output_eq_languageBit input)

/-- One executable projection-PCP result for one fixed hierarchy program.
All resource bounds refer to budgets of the exhibited PCP runners. -/
structure ExecutableProgramProjectionPCPResult
    (program : ExecutableLanguageProgram) (timeBound : ℕ → ℕ)
    (runnerDegree queryExponent substitutionExponent : ℕ) where
  pcp : ExecutableProjectionPCP (toTimedDecisionMachine program) timeBound
  proofExponent : ℕ
  substitution : ExecutableProjectionSubstitution pcp
  shapeDegree : pcp.shape.degree ≤ runnerDegree
  queryDegree : pcp.query.degree ≤ runnerDegree
  decisionDegree : pcp.decisionRunner.degree ≤ runnerDegree
  substitutionDegree : substitution.runner.degree ≤ runnerDegree
  queryCountBound : ∀ n, pcp.queryCount n ≤ pcp.shape.budget n
  compactQueryCountBound : ∀ n,
    pcp.queryCount n ≤
      pcp.shape.coefficient * (pcp.nativeWidth n + 1) ^ queryExponent
  decisionLengthBound : ∀ n input randomness,
    (pcp.decision (n := n) input randomness).clauses.length ≤
      pcp.decisionRunner.budget (pcp.decisionRequest input randomness)
  proofSizeBound : ∀ n,
    2 ^ pcp.nativeWidth n ≤
      pcp.shape.coefficient * timeBound n *
        logScale (timeBound n) ^ proofExponent
  substitutionSizeBound : ∀ request,
    (substitution.circuit request).size ≤
      substitution.sizeCoefficient *
        (pcp.nativeWidth request.inputArity + request.oracle.size + 1) ^
          substitutionExponent
  complete : ∀ n input, program.language n input →
    ∃ proof, ∀ randomness, pcp.toSemantic.accepts input proof randomness
  sound : ∀ n input, ¬program.language n input →
    ∀ proof, pcp.toSemantic.acceptanceFraction input proof ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 10

/-- The faithful executable projection-PCP source.  The quantified input is a
program, so its language and runtime cannot be chosen independently. -/
def ExecutableProgramProjectionPCPGuarantee
    (runnerDegree queryExponent substitutionExponent : ℕ) : Prop :=
  ∀ (program : ExecutableLanguageProgram) (timeBound : ℕ → ℕ),
    (∀ n input, programSteps program n input ≤ timeBound n) →
    (∀ n, n ≤ timeBound n) →
    Nonempty
      (ExecutableProgramProjectionPCPResult program timeBound
        runnerDegree queryExponent substitutionExponent)

def ExecutableProgramProjectionPCPContract : Prop :=
  ∃ runnerDegree queryExponent substitutionExponent : ℕ,
    ExecutableProgramProjectionPCPGuarantee
      runnerDegree queryExponent substitutionExponent

/-- Exact corrected type of the published joint PCP field: only the
projection-PCP half changes domain; the independently executable pointwise
PCPP contract is already data-bearing. -/
def ExecutableProgramProjectionPcpAndPcppContract : Prop :=
  ExecutableProgramProjectionPCPContract ∧ ExecutablePointwisePCPPContract

structure UniformExecutableProgramProjectionPCPSource where
  runnerDegree : ℕ
  queryExponent : ℕ
  substitutionExponent : ℕ
  guarantee : ExecutableProgramProjectionPCPGuarantee
    runnerDegree queryExponent substitutionExponent

theorem existsUniformExecutableProgramProjectionPCPSource
    (contract : ExecutableProgramProjectionPCPContract) :
    Nonempty UniformExecutableProgramProjectionPCPSource := by
  rcases contract with
    ⟨runnerDegree, queryExponent, substitutionExponent, guarantee⟩
  exact ⟨⟨runnerDegree, queryExponent, substitutionExponent, guarantee⟩⟩

/-- Compatibility projection to the legacy semantic PCP representation.  This
forgets executable construction data but does not fabricate a timed machine. -/
def ExecutableProgramProjectionPCPResult.toSemantic
    {program : ExecutableLanguageProgram} {timeBound : ℕ → ℕ}
    {runnerDegree queryExponent substitutionExponent : ℕ}
    (result : ExecutableProgramProjectionPCPResult program timeBound
      runnerDegree queryExponent substitutionExponent) :
    ProjectionPCP (toTimedDecisionMachine program) timeBound :=
  result.pcp.toSemantic

/-- A refuter source whose hierarchy is carried by one fixed executable
program.  Every reference to the hierarchy language below is definitionally
the output language of that program. -/
structure ExecutableProgramRefuterSource (bound : ℕ → ℕ) where
  hierarchyProgram : ExecutableLanguageProgram
  hierarchySteps : ∀ n input, programSteps hierarchyProgram n input ≤ bound n
  refuter : ExecutableSATOracleRefuter hierarchyProgram.language bound
  sound : ∀ machine : ExecutableWeakNondeterministicMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine n) ↔
        hierarchyProgram.language n (refuter.output machine n) = false)

def ExecutableProgramRefuterSource.hierarchyMachine
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    TimedDecisionMachine :=
  toTimedDecisionMachine source.hierarchyProgram

/-- Exact compatibility adapter for the large legacy recovery cone.  Its
timed machine is derived from `hierarchyProgram`; no arbitrary step callback
is introduced by this projection. -/
def ExecutableProgramRefuterSource.toLegacy
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    ExecutableRefuterSource bound where
  hierarchyMachine := source.hierarchyMachine
  hierarchySteps := source.hierarchySteps
  refuter := source.refuter
  sound := source.sound

@[simp] theorem ExecutableProgramRefuterSource.toLegacy_hierarchyMachine
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    source.toLegacy.hierarchyMachine =
      toTimedDecisionMachine source.hierarchyProgram :=
  rfl

@[simp] theorem ExecutableProgramRefuterSource.toLegacy_refuter
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    source.toLegacy.refuter = source.refuter :=
  rfl

def ExecutableProgramRefuterContract : Prop :=
  ∀ (bound : ℕ → ℕ), RefuterClockAdmissible bound →
    Nonempty (ExecutableProgramRefuterSource bound)

def ExecutableProgramRefuterAndXorContract : Prop :=
  ExecutableProgramRefuterContract ∧ XorContract

/-- Instantiate the program-indexed PCP source on exactly the executable
hierarchy selected by the refuter source.  This is the corrected internal
replacement for `RefuterClockClosure.hierarchyProjectionPCP`. -/
theorem hierarchyProjectionPCP
    {bound : ℕ → ℕ} (admissible : RefuterClockAdmissible bound)
    (source : ExecutableProgramRefuterSource bound)
    (projection : UniformExecutableProgramProjectionPCPSource) :
    Nonempty
      (ExecutableProgramProjectionPCPResult source.hierarchyProgram bound
        projection.runnerDegree projection.queryExponent
        projection.substitutionExponent) :=
  projection.guarantee source.hierarchyProgram bound
    source.hierarchySteps admissible.atLeastInput

end NearCubicWires.ExecutableProgramTimedSource
