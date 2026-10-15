import Proof.MachineModel.CanonicalTargetBitProgram
import Proof.Amplification.CaseTwoRecoveryAssembly
import Proof.CaseAnalysis.CaseTwoSeedDeterminacy

namespace NearCubicWires.CanonicalTargetLanguageProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoSeedDeterminacy
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UnaryPolynomialSelector
open NearCubicWires.VerifiedLinker

/-! ## 1. Exponential packaging of one exact interpreter run -/

/-- Widen one exact run to the exponential budget charged by
`ExponentialNatProgram`.  Both the register width and the fuel are raised;
neither can change a successful trace. -/
private theorem run_at_exponentialBudget
    {program : NPOracleProgram} {bits fuel budget length code output : ℕ}
    (hbits : bits ≤ budget) (hfuel : fuel ≤ budget)
    (hrun :
      runNPOracleProgram program bits fuel
        (initialNPOracleState length code) = some output) :
    runNPOracleProgram program budget budget
        (initialNPOracleState length code) = some output := by
  have hwide := run_bits_mono hrun hbits
  have hmore :=
    runNPOracleProgram_add_fuel_of_some (extra := budget - fuel) hwide
  rwa [Nat.add_sub_cancel' hfuel] at hmore

/-- The single constructor for an exponential runner.  Its inputs are one
fixed program, one closed exponent, and one exact run theorem with explicitly
charged width and fuel; no fuel argument, callback, or existential
implementation crosses this boundary. -/
def exponentialNatProgramOfRun {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : Request → ℕ)
    (hbits : ∀ request,
      bits request ≤ exponentialBudget exponent (measure request))
    (hfuel : ∀ request,
      fuel request ≤ exponentialBudget exponent (measure request))
    (hinitial : ∀ request,
      natBitLength (max (inputLength request) (requestCode request)) ≤
        exponentialBudget exponent (measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (inputLength request) (requestCode request)) =
        some (output request)) :
    ExponentialNatProgram Request inputLength requestCode measure where
  program := program
  exponent := exponent
  exponentPositive := hexponent
  initialBitsFit := hinitial
  halts := fun request =>
    ⟨output request,
      run_at_exponentialBudget (hbits request) (hfuel request)
        (hrun request)⟩

/-- The packaged runner reports exactly the output certified by the supplied
run theorem. -/
theorem exponentialNatProgramOfRun_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : Request → ℕ)
    (hbits : ∀ request,
      bits request ≤ exponentialBudget exponent (measure request))
    (hfuel : ∀ request,
      fuel request ≤ exponentialBudget exponent (measure request))
    (hinitial : ∀ request,
      natBitLength (max (inputLength request) (requestCode request)) ≤
        exponentialBudget exponent (measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (inputLength request) (requestCode request)) =
        some (output request))
    (request : Request) :
    (exponentialNatProgramOfRun (inputLength := inputLength)
      (requestCode := requestCode) (measure := measure)
      program exponent hexponent bits fuel output hbits hfuel hinitial
      hrun).execute request = output request := by
  have hwide :=
    run_at_exponentialBudget (program := program) (hbits request)
      (hfuel request) (hrun request)
  simp only [ExponentialNatProgram.execute, ExponentialNatProgram.toBounded,
    BoundedNatProgram.execute, ExponentialNatProgram.budget,
    exponentialNatProgramOfRun, hwide]
  rfl

/-- The single constructor for the terminal `program` binder of the published
recovery closure.  A caller supplies the fixed instruction stream, the closed
exponential envelope, one exact run theorem, and the proof that the certified
output is already canonical Boolean. -/
def executableLanguageProgramOfRun
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1) :
    ExecutableLanguageProgram where
  runner :=
    exponentialNatProgramOfRun
      (inputLength := LanguageEvaluationRequest.length)
      (requestCode := LanguageEvaluationRequest.code)
      (measure := LanguageEvaluationRequest.measure)
      program exponent hexponent bits fuel output hbits hfuel hinitial hrun
  booleanOutput := by
    intro request
    rw [exponentialNatProgramOfRun_execute program exponent hexponent
      bits fuel output hbits hfuel hinitial hrun request]
    exact hboolean request

theorem executableLanguageProgramOfRun_execute
    (program : NPOracleProgram) (exponent : ℕ) (hexponent : 0 < exponent)
    (bits fuel output : LanguageEvaluationRequest → ℕ)
    (hbits : ∀ request,
      bits request ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hfuel : ∀ request,
      fuel request ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hinitial : ∀ request,
      natBitLength
          (max (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) ≤
        exponentialBudget exponent
          (LanguageEvaluationRequest.measure request))
    (hrun : ∀ request,
      runNPOracleProgram program (bits request) (fuel request)
          (initialNPOracleState (LanguageEvaluationRequest.length request)
            (LanguageEvaluationRequest.code request)) =
        some (output request))
    (hboolean : ∀ request, output request ≤ 1)
    (request : LanguageEvaluationRequest) :
    (executableLanguageProgramOfRun program exponent hexponent bits fuel
        output hbits hfuel hinitial hrun hboolean).runner.execute request =
      output request :=
  exponentialNatProgramOfRun_execute program exponent hexponent bits fuel
    output hbits hfuel hinitial hrun request

/-! ## 2. The published refuter reads only the machine description -/

/-- The published refuter is a fixed program whose only machine-dependent
input register is `ExecutableWeakNondeterministicMachine.description`. -/
theorem refuterOutput_eq_of_description
    {hierarchy : Language} {bound : ℕ → ℕ}
    (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (left right : ExecutableWeakNondeterministicMachine)
    (hdescription : left.description = right.description) (n : ℕ) :
    refuter.output left n = refuter.output right n := by
  unfold ExecutableSATOracleRefuter.output
    ExecutableSATOracleRefuter.outputCode
    ExecutableSATOracleRefuter.request
  rw [hdescription]

/-- Consequently the inverse-schedule refuter word, the sole machine-dependent
datum inside `inverseCanonicalTargetFunction`, is a function of the machine
description alone. -/
theorem inverseRefuterInput_eq_of_description
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (left right : ExecutableWeakNondeterministicMachine)
    (hdescription : left.description = right.description)
    (advantageExponent : ℝ) (target : ℕ) :
    inverseRefuterInput contracts outer left advantageExponent target =
      inverseRefuterInput contracts outer right advantageExponent target := by
  unfold inverseRefuterInput
  exact refuterOutput_eq_of_description source.refuter left right
    hdescription _

/-- Fixed-schedule counterpart of `inverseRefuterInput_eq_of_description`. -/
theorem fixedRefuterInput_eq_of_description
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (left right : ExecutableWeakNondeterministicMachine)
    (hdescription : left.description = right.description)
    (requestedRate target : ℕ) :
    fixedRefuterInput contracts outer left requestedRate target =
      fixedRefuterInput contracts outer right requestedRate target := by
  unfold fixedRefuterInput
  exact refuterOutput_eq_of_description source.refuter left right
    hdescription _

/-! ## 3. The Case-1/Case-2 split is one SAT query -/

/-- The genuine outer split is decided by the fixed SAT opcode applied to the
canonical bounded-oracle recovery code.  No circuit, oracle, or branch witness
is supplied from outside: both directions are theorems about the same encoded
formula. -/
theorem encodedSat_iff_nonempty_canonicalAcceptingOracle
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n) :
    encodedSat
        (boundedOracleRecoveryCode pcp input
          (sizeBound (pcp.nativeWidth n))) = true ↔
      Nonempty
        (CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input) := by
  rw [encodedSat_boundedOracleRecoveryCode_eq_true_iff]
  constructor
  · rintro ⟨_description, circuit, hsize, _hdescription, haccepts⟩
    exact existsCanonicalAcceptingOracle pcp input
      ⟨circuit, hsize, haccepts⟩
  · rintro ⟨canonical⟩
    exact
      ⟨canonicalDescriptionInput canonical.circuit canonical.sizeBounded,
        canonical.circuit, canonical.sizeBounded, rfl, canonical.accepts⟩

/-- Scheduled instance of the same discriminator.  This is the exact Boolean
the executable language has to compute before choosing a branch. -/
theorem scheduledCaseTwo_iff_encodedSat
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (requiredDegree sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) :
    encodedSat
        (boundedOracleRecoveryCode (paddedOuterPCP outer) input
          (oracleSizeBound requiredDegree
            (scheduledWidth outer sourceIndex))) = true ↔
      Nonempty
        (CanonicalAcceptingOracle
          (sizeBound := oracleSizeBound requiredDegree)
          (paddedOuterPCP outer) input) :=
  encodedSat_iff_nonempty_canonicalAcceptingOracle
    (sizeBound := oracleSizeBound requiredDegree) (paddedOuterPCP outer) input

/-! ## 4. The Case-2 seed comes from the published factory -/

/-- The published source's systematic-support bound at one circuit.  The
bound is a proposition, so it is extracted from the contract without any
choice at all. -/
theorem factorySupportBound (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size) :
    ∀ i,
      ((pcppSource.factory.forCircuit circuit).systematicSupport i).card ≤
        n / 2 :=
  Exists.elim (pcppSource.guarantee circuit hsize) fun bound _ => bound

/-- The concrete honest PCPP table of the published factory.  Every datum is
the factory's own; the remaining fields are the contract's propositions at the
support bound above.  `caseTwoTable` may therefore be replaced by this table
inside the scheduled Case-2 seed. -/
noncomputable def factoryHonestTable
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size) :
    SourceHonestPCPPTable pcppSource circuit where
  table :=
    { completeness := pcppSource.completeness
      soundness := pcppSource.soundness
      gap := pcppSource.gap
      coefficient := pcppSource.coefficient
      degree := pcppSource.degree
      runnerDegree := pcppSource.runnerDegree
      coefficientPositive := pcppSource.coefficientPositive
      executable := pcppSource.factory.forCircuit circuit
      supportBound := factorySupportBound pcppSource circuit hsize
      shapeDegree := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.1
      supportDegree := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.1
      clauseDegree := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.1
      honestDegree := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.1
      descriptionBound := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.1
      clauseCountBound := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.2.1
      constructionBound := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.2.2.1
      honestComplete := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.2.2.2.1
      rejectSound := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.2.2.2.2.1
      honestStepsBound := by
        rcases pcppSource.guarantee circuit hsize with ⟨_, hrest⟩
        exact hrest.2.2.2.2.2.2.2.2.2 }
  executable_eq := rfl
  coefficient_eq := rfl
  degree_eq := rfl

/-- The concrete table's semantic view is literally the factory's. -/
@[simp] theorem factoryHonestTable_semantic
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size) :
    (factoryHonestTable pcppSource circuit hsize).table.semantic =
      (pcppSource.factory.forCircuit circuit).toSemantic
        (factorySupportBound pcppSource circuit hsize) :=
  rfl

/-- The circuit the Case-2 branch substitutes into the published PCPP source.
Naming it keeps the seed statements below on one line. -/
def caseTwoSubstitutedCircuit
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    BooleanCircuit (outer.pcp.nativeWidth (sourceLength sourceIndex)) :=
  outer.pcppCircuit input
    (restrictPaddedOracle caseTwo.circuit
      (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex)))

theorem caseTwoSubstitutedCircuit_arity_le_size
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    outer.pcp.nativeWidth (sourceLength sourceIndex) ≤
      (caseTwoSubstitutedCircuit caseTwo).size :=
  outer.pcppCircuit_arity_le_size input
    (restrictPaddedOracle caseTwo.circuit
      (nativeWidth_le_widthEnvelope outer (sourceLength sourceIndex)))

/-- The concrete Case-2 honest table: the published factory instantiated once
on the substituted circuit of the recovered oracle. -/
noncomputable def caseTwoFactoryTable
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    SourceHonestPCPPTable pcppSource (caseTwoSubstitutedCircuit caseTwo) :=
  factoryHonestTable pcppSource (caseTwoSubstitutedCircuit caseTwo)
    (caseTwoSubstitutedCircuit_arity_le_size caseTwo)

/-- The scheduled Case-2 table selected with choice and the concrete factory
table share one semantic PCPP. -/
theorem caseTwoTable_semantic_eq_factory
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    (caseTwoTable pcppSource caseTwo).table.semantic =
      (pcppSource.factory.forCircuit
          (caseTwoSubstitutedCircuit caseTwo)).toSemantic
        (factorySupportBound pcppSource (caseTwoSubstitutedCircuit caseTwo)
          (caseTwoSubstitutedCircuit_arity_le_size caseTwo)) :=
  sourceHonestPCPPTable_semantic_eq pcppSource
    (caseTwoTable pcppSource caseTwo) (caseTwoFactoryTable pcppSource caseTwo)

/-- The scheduled Case-2 seed is the seed of the concrete factory table.  This
removes the last choice on data from the Case-2 branch of the canonical target
function: only the recovered oracle circuit remains to be computed. -/
theorem caseTwoSeed_eq_factorySeed
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input) :
    caseTwoSeed pcppSource caseTwo =
      seedOfTable pcppSource caseTwo
        (caseTwoFactoryTable pcppSource caseTwo) :=
  caseTwoSeed_eq_seedOfTable pcppSource caseTwo _

/-! ### From the seed function to one seed bit -/

/-- The scheduled seed arity in the padded envelope coordinates actually used
by the honest occurrence table. -/
theorem seedArity_eq_envelope
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (requiredDegree sourceIndex : ℕ) :
    seedArity outer pcppSource requiredDegree sourceIndex =
      widthEnvelope outer (sourceLength sourceIndex) +
        clauseBitsEnvelope outer pcppSource (oracleSizeBound requiredDegree)
          (sourceLength sourceIndex) + 1 := by
  rw [seedArity, scheduledWidth, scheduledClauseBits_eq_envelope]

private theorem boolFunction_apply_of_heq {left right : ℕ}
    (harity : left = right)
    {source : BoolFunction left} {image : BoolFunction right}
    (hfunction : HEq source image) (point : BitInput left) :
    source point = image fun index => point (Fin.cast harity.symm index) := by
  subst harity
  rw [eq_of_heq hfunction]
  simp

/-- The scheduled arity identification inside `seedOfTable` is a pure
reindexing: no clause, occurrence, or table datum is changed. -/
theorem seedOfTable_heq_paddedFunction
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (table : SourceHonestPCPPTable pcppSource
      (caseTwoSubstitutedCircuit caseTwo)) :
    HEq (seedOfTable pcppSource caseTwo table)
      (table.paddedFunction outer pcppSource (oracleSizeBound requiredDegree)
        input caseTwo.circuit caseTwo.sizeBounded) := by
  unfold seedOfTable
  rw [eq_mpr_eq_cast]
  exact cast_heq _ _

/-- One Case-2 seed bit is exactly one padded honest-occurrence value of the
published factory's PCPP on the substituted circuit.  This is the last purely
mathematical step before an executable occurrence evaluator: everything to its
right is a factory runner call. -/
theorem caseTwoSeed_apply
    (pcppSource : UniformPointwisePCPPSource)
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    {outer : HierarchyOuterPCP source}
    {requiredDegree sourceIndex : ℕ}
    {input : BitInput (sourceLength sourceIndex)}
    (caseTwo :
      CanonicalAcceptingOracle
        (sizeBound := oracleSizeBound requiredDegree)
        (paddedOuterPCP outer) input)
    (point :
      BitInput (seedArity outer pcppSource requiredDegree sourceIndex)) :
    caseTwoSeed pcppSource caseTwo point =
      (caseTwoFactoryTable pcppSource caseTwo).paddedFunction outer pcppSource
        (oracleSizeBound requiredDegree) input caseTwo.circuit
        caseTwo.sizeBounded
        (fun index =>
          point
            (Fin.cast
              (seedArity_eq_envelope outer pcppSource requiredDegree
                sourceIndex).symm index)) := by
  rw [caseTwoSeed_eq_factorySeed pcppSource caseTwo]
  exact boolFunction_apply_of_heq
    (seedArity_eq_envelope outer pcppSource requiredDegree sourceIndex)
    (seedOfTable_heq_paddedFunction pcppSource caseTwo
      (caseTwoFactoryTable pcppSource caseTwo)) point

/-! ## 5. Both branches of the fixed dispatcher compute the branch core -/

private theorem bne_zero_eq_decide (value : ℕ) :
    (value != 0) = decide (value ≠ 0) := by
  cases value <;> rfl

/-- The published amplifier's Boolean output at one padded public input is
literally the evaluator call performed by `paddedAmplifierEvaluationProgram`.
Isolating this small equality keeps the linked-program terms out of the main
rewrite below. -/
private theorem amplify_function_eq_decide
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (arity : ℕ) (seed : BoolFunction arity) (inputCode : ℕ) :
    (algorithm.amplify arity seed).function
        (bitInputPrefixView (algorithm.outputArity ⟨arity, seed⟩) inputCode) =
      decide
        (algorithm.evaluator.execute
          (paddedAmplifierEvaluationRequest
            (algorithm.outputArity ⟨arity, seed⟩)
            (algorithm.descriptor ⟨arity, seed⟩) inputCode) ≠ 0) :=
  bne_zero_eq_decide _

/-- Case 1 of the fixed target-bit dispatcher returns exactly the amplified
hard-core bit of the supplied seed.  The descriptor and output arity are the
published construction program's own outputs, so no amplified truth table is
carried across the call boundary. -/
theorem run_targetBitProgram_caseOne_amplified
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength arity : ℕ) (seed : BoolFunction arity) (inputCode : ℕ) :
    runNPOracleProgram (targetBitProgram algorithm)
        (targetBitCaseOneBits algorithm inputLength
          (algorithm.outputArity ⟨arity, seed⟩)
          (algorithm.descriptor ⟨arity, seed⟩) inputCode)
        (targetBitCaseOneFuel algorithm
          (algorithm.outputArity ⟨arity, seed⟩)
          (algorithm.descriptor ⟨arity, seed⟩) inputCode)
        (initialNPOracleState inputLength
          (targetBitCaseOneInput (algorithm.outputArity ⟨arity, seed⟩)
            (algorithm.descriptor ⟨arity, seed⟩) inputCode)) =
      some
        ((algorithm.amplify arity seed).function
          (bitInputPrefixView (algorithm.outputArity ⟨arity, seed⟩)
            inputCode)).toNat := by
  rw [amplify_function_eq_decide algorithm arity seed inputCode]
  exact run_targetBitProgram_caseOne algorithm inputLength
    (algorithm.outputArity ⟨arity, seed⟩)
    (algorithm.descriptor ⟨arity, seed⟩) inputCode

private theorem foldl_map_eq_xorPower {arity : ℕ}
    (seed : BoolFunction arity) (copies : ℕ)
    (point : BitInput (copies * arity)) :
    (((Finset.univ : Finset (Fin copies)).toList.map
        fun block => seed (blockInput point block)).foldl xor false) =
      xorPower seed copies point := by
  rw [xorPower, List.foldl_map]

/-- Case 2 of the same dispatcher returns exactly the XOR-amplified seed bit
consumed by `commonHardCoreFromXor`.  The seed block values are data on the
public input; the parity itself is the fixed balanced fold. -/
theorem run_targetBitProgram_caseTwo_xorPower
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (inputLength arity copies : ℕ) (seed : BoolFunction arity)
    (point : BitInput (copies * arity)) :
    runNPOracleProgram (targetBitProgram algorithm)
        (targetBitCaseTwoBits inputLength
          ((Finset.univ : Finset (Fin copies)).toList.map
            fun block => seed (blockInput point block)))
        (targetBitCaseTwoFuel
          ((Finset.univ : Finset (Fin copies)).toList.map
            fun block => seed (blockInput point block)))
        (initialNPOracleState inputLength
          (targetBitCaseTwoInput
            ((Finset.univ : Finset (Fin copies)).toList.map
              fun block => seed (blockInput point block)))) =
      some (xorPower seed copies point).toNat := by
  rw [← foldl_map_eq_xorPower seed copies point]
  exact run_targetBitProgram_caseTwo algorithm inputLength
    ((Finset.univ : Finset (Fin copies)).toList.map
      fun block => seed (blockInput point block))

/-! ## 6. Exact Case-1 execution of the canonical target bit -/

/-- Canonical padding reads exactly the low target coordinates. -/
theorem padCore_apply {core target : ℕ} (function : BoolFunction core)
    (hcore : core ≤ target) (point : BitInput target) :
    padCore function hcore point =
      function fun index => point ⟨index.val, index.isLt.trans_le hcore⟩ := by
  simp only [padCore, finSplitEquiv, Equiv.trans_apply]
  rfl

/-- Two successive paddings read the same low coordinates as one. -/
theorem padCore_padCore {core middle target : ℕ}
    (function : BoolFunction core) (hmiddle : core ≤ middle)
    (htarget : middle ≤ target) (point : BitInput target) :
    padCore (padCore function hmiddle) htarget point =
      function fun index =>
        point ⟨index.val, index.isLt.trans_le (hmiddle.trans htarget)⟩ := by
  rw [padCore_apply, padCore_apply]

/-- Exact Case-1 execution.  On the inverse schedule the fixed target-bit
dispatcher, driven by the published amplifier's own output arity and
descriptor for the C.12-recovered accepting proof, returns exactly the
canonical Case-1 target bit at every requested input.  Only the amplifier
construction call that produces those two numbers is still missing between
this theorem and `hexecutes`. -/
theorem run_targetBitProgram_inverseCaseOne
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (advantageExponent : ℝ) (target : ℕ)
    (htarget :
      (inverseEnvelope contracts outer
        (inverseCoreAdvantagePower advantageExponent)).targetOnset ≤ target)
    {input : BitInput
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target))
      input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
      input)
    (hready :
      inverseCaseOneOnset contracts outer
          (inverseCoreAdvantagePower advantageExponent) ≤
        inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)
    (point : BitInput target) :
    runNPOracleProgram
        (targetBitProgram (publishedAmplifier contracts).algorithm)
        (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
          ((publishedAmplifier contracts).algorithm.outputArity
            ⟨scheduledWidth outer
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          ((publishedAmplifier contracts).algorithm.descriptor
            ⟨scheduledWidth outer
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          (encodeBitInput point))
        (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
          ((publishedAmplifier contracts).algorithm.outputArity
            ⟨scheduledWidth outer
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          ((publishedAmplifier contracts).algorithm.descriptor
            ⟨scheduledWidth outer
              (inverseSourceIndex
                (inverseSelectedSource contracts outer
                  (inverseCoreAdvantagePower advantageExponent) target)),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          (encodeBitInput point))
        (initialNPOracleState target
          (targetBitCaseOneInput
            ((publishedAmplifier contracts).algorithm.outputArity
              ⟨scheduledWidth outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target)),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            ((publishedAmplifier contracts).algorithm.descriptor
              ⟨scheduledWidth outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target)),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            (encodeBitInput point))) =
      some
        (inverseCaseOneTargetFunction contracts outer advantageExponent target
          htarget data hyes hready point).toNat := by
  obtain ⟨hamplified, hfunction⟩ :=
    inversePhysicalCore_function_eq_recoveredAmplification contracts outer
      (inverseCoreAdvantagePower advantageExponent)
      (inverseSelectedSource contracts outer
        (inverseCoreAdvantagePower advantageExponent) target)
      data hyes hready
  have hcore :=
    (inverseSelectedCoreBounds contracts outer
      (inverseCoreAdvantagePower advantageExponent) target htarget).1
  have hle :
      (publishedAmplifier contracts).algorithm.outputArity
          ⟨scheduledWidth outer
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)),
            recoveredOuterProofFunction (paddedOuterPCP outer) input⟩ ≤
        target :=
    hamplified.trans hcore
  have hprefix :=
    bitInputPrefixView_encodeBitInput
      (width := (publishedAmplifier contracts).algorithm.outputArity
        ⟨scheduledWidth outer
          (inverseSourceIndex
            (inverseSelectedSource contracts outer
              (inverseCoreAdvantagePower advantageExponent) target)),
          recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
      point hle
  have hvalue :
      inverseCaseOneTargetFunction contracts outer advantageExponent target
          htarget data hyes hready point =
        ((publishedAmplifier contracts).algorithm.amplify
          (scheduledWidth outer
            (inverseSourceIndex
              (inverseSelectedSource contracts outer
                (inverseCoreAdvantagePower advantageExponent) target)))
          (recoveredOuterProofFunction
            (paddedOuterPCP outer) input)).function
          (bitInputPrefixView
            ((publishedAmplifier contracts).algorithm.outputArity
              ⟨scheduledWidth outer
                (inverseSourceIndex
                  (inverseSelectedSource contracts outer
                    (inverseCoreAdvantagePower advantageExponent) target)),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            (encodeBitInput point)) := by
    rw [inverseCaseOneTargetFunction_eq, hfunction, padCore_padCore,
      hprefix]
    rfl
  rw [hvalue]
  exact run_targetBitProgram_caseOne_amplified
    (publishedAmplifier contracts).algorithm target
    (scheduledWidth outer
      (inverseSourceIndex
        (inverseSelectedSource contracts outer
          (inverseCoreAdvantagePower advantageExponent) target)))
    (recoveredOuterProofFunction (paddedOuterPCP outer) input)
    (encodeBitInput point)

/-- Fixed-schedule counterpart of `run_targetBitProgram_inverseCaseOne`. -/
theorem run_targetBitProgram_fixedCaseOne
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (contracts : PublishedContracts) (outer : HierarchyOuterPCP source)
    (requestedRate target : ℕ)
    (htarget :
      (fixedEnvelope contracts outer requestedRate).targetOnset ≤ target)
    {input : BitInput
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))}
    (data : ScheduledCaseOneData outer (publishedAmplifier contracts)
      (fixedRequiredDegree contracts requestedRate)
      (fixedSelectedSource contracts outer requestedRate target) input)
    (hyes : source.hierarchyMachine.accepts
      (sourceLength
        (fixedSelectedSource contracts outer requestedRate target))
      input)
    (hready :
      fixedCaseOneOnset contracts outer requestedRate ≤
        fixedSelectedSource contracts outer requestedRate target)
    (point : BitInput target) :
    runNPOracleProgram
        (targetBitProgram (publishedAmplifier contracts).algorithm)
        (targetBitCaseOneBits (publishedAmplifier contracts).algorithm target
          ((publishedAmplifier contracts).algorithm.outputArity
            ⟨scheduledWidth outer
              (fixedSelectedSource contracts outer requestedRate target),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          ((publishedAmplifier contracts).algorithm.descriptor
            ⟨scheduledWidth outer
              (fixedSelectedSource contracts outer requestedRate target),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          (encodeBitInput point))
        (targetBitCaseOneFuel (publishedAmplifier contracts).algorithm
          ((publishedAmplifier contracts).algorithm.outputArity
            ⟨scheduledWidth outer
              (fixedSelectedSource contracts outer requestedRate target),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          ((publishedAmplifier contracts).algorithm.descriptor
            ⟨scheduledWidth outer
              (fixedSelectedSource contracts outer requestedRate target),
              recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
          (encodeBitInput point))
        (initialNPOracleState target
          (targetBitCaseOneInput
            ((publishedAmplifier contracts).algorithm.outputArity
              ⟨scheduledWidth outer
                (fixedSelectedSource contracts outer requestedRate target),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            ((publishedAmplifier contracts).algorithm.descriptor
              ⟨scheduledWidth outer
                (fixedSelectedSource contracts outer requestedRate target),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            (encodeBitInput point))) =
      some
        (fixedCaseOneTargetFunction contracts outer requestedRate target
          htarget data hyes hready point).toNat := by
  obtain ⟨hamplified, hfunction⟩ :=
    fixedPhysicalCore_function_eq_recoveredAmplification contracts outer
      requestedRate
      (fixedSelectedSource contracts outer requestedRate target)
      data hyes hready
  have hcore :=
    (fixedSelectedCoreBounds contracts outer requestedRate target htarget).1
  have hle :
      (publishedAmplifier contracts).algorithm.outputArity
          ⟨scheduledWidth outer
            (fixedSelectedSource contracts outer requestedRate target),
            recoveredOuterProofFunction (paddedOuterPCP outer) input⟩ ≤
        target :=
    hamplified.trans hcore
  have hprefix :=
    bitInputPrefixView_encodeBitInput
      (width := (publishedAmplifier contracts).algorithm.outputArity
        ⟨scheduledWidth outer
          (fixedSelectedSource contracts outer requestedRate target),
          recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
      point hle
  have hvalue :
      fixedCaseOneTargetFunction contracts outer requestedRate target
          htarget data hyes hready point =
        ((publishedAmplifier contracts).algorithm.amplify
          (scheduledWidth outer
            (fixedSelectedSource contracts outer requestedRate target))
          (recoveredOuterProofFunction
            (paddedOuterPCP outer) input)).function
          (bitInputPrefixView
            ((publishedAmplifier contracts).algorithm.outputArity
              ⟨scheduledWidth outer
                (fixedSelectedSource contracts outer requestedRate target),
                recoveredOuterProofFunction (paddedOuterPCP outer) input⟩)
            (encodeBitInput point)) := by
    rw [fixedCaseOneTargetFunction_eq, hfunction, padCore_padCore, hprefix]
    rfl
  rw [hvalue]
  exact run_targetBitProgram_caseOne_amplified
    (publishedAmplifier contracts).algorithm target
    (scheduledWidth outer
      (fixedSelectedSource contracts outer requestedRate target))
    (recoveredOuterProofFunction (paddedOuterPCP outer) input)
    (encodeBitInput point)

end NearCubicWires.CanonicalTargetLanguageProgram
