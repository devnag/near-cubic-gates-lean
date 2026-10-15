import Proof.MachineModel.BoundedOracleRecoveryProgram
import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.Amplification.CaseOneRecoveryAssembly

/-!
# The recovered accepting proof as one encoded truth table

Case 1 of the canonical target language has to hand the published amplifier a
whole `AmplifierRequest`, whose code contains `encodeBoolFunction` of the
exponentially long C.12-recovered outer proof.  This module fixes that
producer.

There is no new recovery path here.  The callee is the already verified
zero-first prefix-SAT reducer `rawClausePrefixSATProgram`, applied once per
address of the recovered proof through the single balanced call ABI of
`CanonicalBalancedCall`.  Because that ABI already returns
`encodeBalancedList` of the per-request outputs and `encodeBoolFunction` is by
definition `encodeBalancedList` of the Boolean codes of the truth table, the
loop's certified output is literally the amplifier's request payload.

Two seams are closed.

* `run_recoveredProofEncodingProgram` — one fixed program, explicit width and
  fuel, whose output is `encodeBoolFunction (recoveredOuterProofFunction …)`.
* `run_amplifierConstructionCallProgram` — the single native call that turns
  that payload into the published amplifier's own `outputArity` and
  `descriptor`, which are the two data arguments still supplied by hand to
  `CanonicalTargetLanguageProgram.run_targetBitProgram_inverseCaseOne`.
-/

namespace NearCubicWires.RecoveredProofEncodingProgram

open NearCubicWires
open NearCubicWires.BoundedOracleRecoveryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. Small arithmetic facts about one recovered bit -/

private theorem latestPrefixBitCode_le_one (values : List Bool) :
    latestPrefixBitCode values ≤ 1 := by
  cases values with
  | nil => exact Nat.zero_le 1
  | cons value _ =>
      rw [latestPrefixBitCode_cons]
      cases value <;> decide

private theorem prefixSATOutput_le_one (count : ℕ) (formula : EncodedCNF) :
    prefixSATOutput count formula ≤ 1 :=
  latestPrefixBitCode_le_one _

private theorem decide_ne_zero_toNat {value : ℕ} (hvalue : value ≤ 1) :
    (decide (value ≠ 0)).toNat = value := by
  interval_cases value <;> decide

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) : value ≤ values.foldr max 0 := by
  induction values with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ Nat.le_max_left _ _
      · exact (ih htail).trans (Nat.le_max_right _ _)

/-! ## 2. The fixed request schedule of the recovered proof -/

/-- One balanced-call request: the shared raw clause stream of the C.12 outer
proof formula together with the unary prefix length that selects the requested
address. -/
def recoveredProofRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength address : ℕ) : ℕ :=
  Nat.pair inputLength
    (Nat.pair (rawClauseStream (outerProofRecoveryFormula pcp input))
      (encodeUnary (address + 1)))

/-- The exact address schedule: every truth-table row of the recovered proof,
in the increasing code order used by `boolFunctionTable`. -/
def recoveredProofRequests
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) : List ℕ :=
  (List.range (2 ^ pcp.nativeWidth n)).map
    (recoveredProofRequest pcp input inputLength)

/-- The prefix length carried by one request.  Reading it back from the
canonical request code keeps the balanced-call output, fuel, and width
functions total on `ℕ`. -/
def recoveredProofCallCount (request : ℕ) : ℕ :=
  (decodeUnary (Nat.unpair (Nat.unpair request).2).2).getD 0

@[simp] theorem recoveredProofCallCount_request
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength address : ℕ) :
    recoveredProofCallCount (recoveredProofRequest pcp input inputLength
        address) = address + 1 := by
  simp [recoveredProofCallCount, recoveredProofRequest]

def recoveredProofCallOutput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (request : ℕ) : ℕ :=
  prefixSATOutput (recoveredProofCallCount request)
    (outerProofRecoveryFormula pcp input)

def recoveredProofCallFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (request : ℕ) : ℕ :=
  rawClausePrefixSATFuel (recoveredProofCallCount request)
    (outerProofRecoveryFormula pcp input)

def recoveredProofCallBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength request : ℕ) : ℕ :=
  rawClausePrefixSATMaximumBits inputLength (recoveredProofCallCount request)
    (outerProofRecoveryFormula pcp input)

/-! ## 3. The fixed encoding loop -/

/-- The sole recovered-proof encoder: the canonical balanced call over the
already verified zero-first prefix-SAT reducer.  It performs SAT queries, so
this is exactly the `E^NP` part of the target language. -/
def recoveredProofEncodingProgram : NPOracleProgram :=
  balancedCallProgram rawClausePrefixSATProgram

def recoveredProofEncodingInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) : ℕ :=
  encodeBalancedList (recoveredProofRequests pcp input inputLength)

def recoveredProofEncodingFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) : ℕ :=
  balancedCallFuel rawClausePrefixSATProgram
    (recoveredProofCallFuel pcp input)
    (recoveredProofRequests pcp input inputLength)

def recoveredProofEncodingBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) : ℕ :=
  max
    (balancedCallRequiredBits (recoveredProofCallOutput pcp input)
      (recoveredProofRequests pcp input inputLength))
    (((recoveredProofRequests pcp input inputLength).map
      (recoveredProofCallBits pcp input inputLength)).foldr max 0)

/-- Every scheduled request executes exactly on the shared callee. -/
private theorem run_recoveredProofCall
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) {request : ℕ}
    (hmem : request ∈ recoveredProofRequests pcp input inputLength) :
    runNPOracleProgram rawClausePrefixSATProgram
        (recoveredProofEncodingBits pcp input inputLength)
        (recoveredProofCallFuel pcp input request)
        (initialNPOracleState (Nat.unpair request).1
          (Nat.unpair request).2) =
      some (recoveredProofCallOutput pcp input request) := by
  have hmemBits :
      recoveredProofCallBits pcp input inputLength request ∈
        (recoveredProofRequests pcp input inputLength).map
          (recoveredProofCallBits pcp input inputLength) :=
    List.mem_map_of_mem hmem
  have hbits :
      recoveredProofCallBits pcp input inputLength request ≤
        recoveredProofEncodingBits pcp input inputLength := by
    unfold recoveredProofEncodingBits
    exact (le_foldr_max_of_mem hmemBits).trans (Nat.le_max_right _ _)
  obtain ⟨address, _haddress, hrequest⟩ := List.mem_map.mp hmem
  subst hrequest
  have hcount :
      recoveredProofCallCount
          (recoveredProofRequest pcp input inputLength address) =
        address + 1 :=
    recoveredProofCallCount_request pcp input inputLength address
  have hfirst :
      (Nat.unpair
        (recoveredProofRequest pcp input inputLength address)).1 =
        inputLength := by
    simp [recoveredProofRequest]
  have hsecond :
      (Nat.unpair
        (recoveredProofRequest pcp input inputLength address)).2 =
        Nat.pair (rawClauseStream (outerProofRecoveryFormula pcp input))
          (encodeUnary (address + 1)) := by
    simp [recoveredProofRequest]
  rw [hfirst, hsecond, recoveredProofCallFuel, recoveredProofCallOutput,
    hcount]
  exact run_bits_mono
    (run_rawClausePrefixSATProgram inputLength (address + 1)
      (outerProofRecoveryFormula pcp input)
      (outerProofRecoveryFormula_threeLiteral pcp input))
    (hcount ▸ hbits)

private theorem recoveredProofOutputs_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) :
    (recoveredProofRequests pcp input inputLength).map
        (recoveredProofCallOutput pcp input) =
      (boolFunctionTable (recoveredOuterProofFunction pcp input)).map
        boolCode := by
  simp only [recoveredProofRequests, boolFunctionTable, List.map_map]
  refine List.map_congr_left ?_
  intro address haddress
  have hlt : address < 2 ^ pcp.nativeWidth n := List.mem_range.mp haddress
  have hbit :
      recoveredOuterProofFunction pcp input
          (fun index : Fin (pcp.nativeWidth n) =>
            address.testBit index.val) =
        decide (prefixSATOutput (address + 1)
          (outerProofRecoveryFormula pcp input) ≠ 0) := by
    rw [recoveredOuterProofFunction, binaryAddress_testBit hlt,
      recoveredTargetBit]
  simp only [Function.comp_apply, recoveredProofCallOutput,
    recoveredProofCallCount_request, hbit, boolCode]
  exact (decide_ne_zero_toNat (prefixSATOutput_le_one _ _)).symm

/-- Exact recovered-proof encoding.  One fixed instruction stream, one closed
width, and one closed fuel produce precisely the amplifier payload
`encodeBoolFunction` of the C.12-recovered accepting proof. -/
theorem run_recoveredProofEncodingProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (inputLength : ℕ) :
    runNPOracleProgram recoveredProofEncodingProgram
        (recoveredProofEncodingBits pcp input inputLength)
        (recoveredProofEncodingFuel pcp input inputLength)
        (initialNPOracleState inputLength
          (recoveredProofEncodingInput pcp input inputLength)) =
      some (encodeBoolFunction (recoveredOuterProofFunction pcp input)) := by
  have hrun :=
    run_balancedCallProgram_from
      (callee := rawClausePrefixSATProgram)
      (maximumBits := recoveredProofEncodingBits pcp input inputLength)
      inputLength (recoveredProofRequests pcp input inputLength)
      (recoveredProofCallFuel pcp input)
      (recoveredProofCallOutput pcp input)
      (Nat.le_max_left _ _)
      (fun request hmem => run_recoveredProofCall pcp input inputLength hmem)
  rw [recoveredProofOutputs_eq pcp input inputLength] at hrun
  simpa only [recoveredProofEncodingProgram, recoveredProofEncodingFuel,
    recoveredProofEncodingInput, encodeBoolFunction, encodeBoolList] using hrun

/-! ## 4. Scheduled instance and the amplifier construction call -/

/-- The scheduled recovered-proof encoder at the published padded outer PCP.
Its arity is exactly `scheduledWidth outer sourceIndex`, so the certified
output is the seed payload consumed by the published amplifier. -/
theorem run_scheduledRecoveredProofEncodingProgram
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ)
    (input : BitInput (sourceLength sourceIndex)) (inputLength : ℕ) :
    runNPOracleProgram recoveredProofEncodingProgram
        (recoveredProofEncodingBits (paddedOuterPCP outer) input inputLength)
        (recoveredProofEncodingFuel (paddedOuterPCP outer) input inputLength)
        (initialNPOracleState inputLength
          (recoveredProofEncodingInput (paddedOuterPCP outer) input
            inputLength)) =
      some
        (encodeBoolFunction
          (recoveredOuterProofFunction (paddedOuterPCP outer) input)) :=
  run_recoveredProofEncodingProgram (paddedOuterPCP outer) input inputLength

/-- The scheduled seed arity really is the schedule's own width. -/
theorem scheduledRecoveredProofArity
    {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (sourceIndex : ℕ) :
    (paddedOuterPCP outer).nativeWidth (sourceLength sourceIndex) =
      scheduledWidth outer sourceIndex :=
  rfl

/-- The exact `AmplifierRequest` code of one seed. -/
def amplifierRequestCode {arity : ℕ} (seed : BoolFunction arity) : ℕ :=
  Nat.pair arity (encodeBoolFunction seed)

@[simp] theorem amplifierRequestCode_eq {arity : ℕ}
    (seed : BoolFunction arity) :
    AmplifierRequest.code ⟨arity, seed⟩ = amplifierRequestCode seed :=
  rfl

/-- One native call on the published amplifier's own construction program.
Its certified output is the construction code, hence both the amplifier's
`outputArity` and its `descriptor`; no amplified truth table crosses the
boundary. -/
theorem run_amplifierConstructionCallProgram
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (outerInputLength arity : ℕ) (seed : BoolFunction arity) :
    runNPOracleProgram (nativeCallProgram algorithm.construction.program)
        (nativeCallBits outerInputLength arity (amplifierRequestCode seed)
          (algorithm.constructionCode ⟨arity, seed⟩)
          (algorithm.construction.budget ⟨arity, seed⟩))
        (nativeCallFuel algorithm.construction.program
          (algorithm.construction.budget ⟨arity, seed⟩) arity
          (amplifierRequestCode seed))
        (initialNPOracleState outerInputLength
          (nativeInputRequest arity (amplifierRequestCode seed))) =
      some (algorithm.constructionCode ⟨arity, seed⟩) := by
  apply run_nativeCallProgram algorithm.construction.program
  exact algorithm.construction.run_eq_execute ⟨arity, seed⟩

/-- The same call read through the amplifier's public projections. -/
theorem run_amplifierConstructionCallProgram_pair
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (outerInputLength arity : ℕ) (seed : BoolFunction arity) :
    runNPOracleProgram (nativeCallProgram algorithm.construction.program)
        (nativeCallBits outerInputLength arity (amplifierRequestCode seed)
          (algorithm.constructionCode ⟨arity, seed⟩)
          (algorithm.construction.budget ⟨arity, seed⟩))
        (nativeCallFuel algorithm.construction.program
          (algorithm.construction.budget ⟨arity, seed⟩) arity
          (amplifierRequestCode seed))
        (initialNPOracleState outerInputLength
          (nativeInputRequest arity (amplifierRequestCode seed))) =
      some
        (Nat.pair (algorithm.outputArity ⟨arity, seed⟩)
          (algorithm.descriptor ⟨arity, seed⟩)) := by
  rw [run_amplifierConstructionCallProgram algorithm outerInputLength arity
    seed]
  rw [ExecutableWorstCaseAmplifierAlgorithm.outputArity,
    ExecutableWorstCaseAmplifierAlgorithm.descriptor, Nat.pair_unpair]

end NearCubicWires.RecoveredProofEncodingProgram
