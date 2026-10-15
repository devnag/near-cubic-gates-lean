import Proof.Foundations.CanonicalBinary
import Proof.Foundations.SourceInterfaces
import Proof.Foundations.QuotientBudgetCurrency
import StatementSupport

open Finset
open scoped BigOperators

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.SourceInterfaces

/-! ## Reusable bounded runners -/

/-- Deterministic imported algorithms may not gain power from the SAT opcode. -/
def OracleFree (program : NPOracleProgram) : Prop :=
  program.all (fun instruction => match instruction with
    | .halt _ => true
    | .set _ _ _ => true
    | .copy _ _ _ => true
    | .increment _ _ => true
    | .decrement _ _ => true
    | .add _ _ _ _ => true
    | .subtract _ _ _ _ => true
    | .pair _ _ _ _ => true
    | .unpairLeft _ _ _ => true
    | .unpairRight _ _ _ => true
    | .branchZero _ _ _ => true
    | .encodeNat _ _ _ => true
    | .shiftRight _ _ _ _ => true
    | .shiftLeft _ _ _ _ => true
    | .testBit _ _ _ _ => true
    | .sat _ _ _ => false
    ) = true

/-- A program with request-dependent, explicitly charged resources. -/
structure BoundedNatProgram (Request : Type)
    (inputLength requestCode : Request → ℕ) where
  program : NPOracleProgram
  fuel : Request → ℕ
  registerBits : Request → ℕ
  fuelPositive : ∀ request, 0 < fuel request
  registerBitsPositive : ∀ request, 0 < registerBits request
  /-- The advertised cap includes the two caller-populated registers.  The
  interpreter bounds writes, so this is the missing boundary condition that
  prevents an oversized request code from acting as free read-only advice. -/
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      registerBits request

def BoundedNatProgram.execute {Request : Type}
    {inputLength requestCode : Request → ℕ}
    (runner : BoundedNatProgram Request inputLength requestCode)
    (request : Request) : ℕ :=
  (runNPOracleProgram runner.program (runner.registerBits request)
    (runner.fuel request)
    (initialNPOracleState (inputLength request) (requestCode request))).getD 0

/-- A correctness witness is an equality about the actual interpreter run. -/
structure BoundedNatProgramWitness (Request : Type)
    (inputLength requestCode expectedOutput : Request → ℕ) where
  runner : BoundedNatProgram Request inputLength requestCode
  computes : ∀ request,
    runNPOracleProgram runner.program (runner.registerBits request)
      (runner.fuel request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (expectedOutput request)

theorem BoundedNatProgramWitness.execute_eq {Request : Type}
    {inputLength requestCode expectedOutput : Request → ℕ}
    (witness : BoundedNatProgramWitness Request inputLength requestCode expectedOutput)
    (request : Request) :
    witness.runner.execute request = expectedOutput request := by
  simp [BoundedNatProgram.execute, witness.computes request]

def polynomialBudget (coefficient degree measure : ℕ) : ℕ :=
  coefficient * (measure + 1) ^ degree

/-- Polynomial resource bounds are used as the interpreter budgets themselves. -/
structure PolynomialNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  degree : ℕ
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      polynomialBudget coefficient degree (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (polynomialBudget coefficient degree (measure request))
      (polynomialBudget coefficient degree (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def PolynomialNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  polynomialBudget runner.coefficient runner.degree (measure request)

def PolynomialNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := by
    intro request
    exact Nat.mul_pos runner.coefficientPositive (pow_pos (by omega) _)
  registerBitsPositive := by
    intro request
    exact Nat.mul_pos runner.coefficientPositive (pow_pos (by omega) _)
  initialBitsFit := runner.initialBitsFit

def PolynomialNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

theorem PolynomialNatProgram.run_eq_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (request : Request) :
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (runner.execute request) := by
  obtain ⟨output, houtput⟩ := runner.halts request
  simp [PolynomialNatProgram.budget, PolynomialNatProgram.execute,
    PolynomialNatProgram.toBounded, BoundedNatProgram.execute, houtput]

structure PolynomialNatProgramWitness (Request : Type)
    (inputLength requestCode measure expectedOutput : Request → ℕ) where
  runner : PolynomialNatProgram Request inputLength requestCode measure
  computes : ∀ request,
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (expectedOutput request)

theorem PolynomialNatProgramWitness.execute_eq {Request : Type}
    {inputLength requestCode measure expectedOutput : Request → ℕ}
    (witness :
      PolynomialNatProgramWitness Request inputLength requestCode measure expectedOutput)
    (request : Request) :
    witness.runner.execute request = expectedOutput request := by
  simp [PolynomialNatProgram.execute, PolynomialNatProgram.toBounded,
    BoundedNatProgram.execute, witness.computes request]

/-- **The quotient-budget program carrier**.  Same field names as `PolynomialNatProgram` plus `logPower`,
so every `verifier.<field>` projection site keeps its spelling; only the
budget currency changes: `⌊coefficient·(m+1)^degree / L(m)^logPower⌋`.
`savingFits` keeps the floored budget positive — the saving divisor never
exceeds the whole budget. -/
structure QuotientNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  degree : ℕ
  logPower : ℕ
  savingFits : ∀ request,
    logScale (measure request) ^ logPower ≤
      coefficient * (measure request + 1) ^ degree
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      quotientBudget coefficient degree logPower (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (quotientBudget coefficient degree logPower (measure request))
      (quotientBudget coefficient degree logPower (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def QuotientNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  quotientBudget runner.coefficient runner.degree runner.logPower
    (measure request)

theorem QuotientNatProgram.budget_pos {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : 0 < runner.budget request :=
  Nat.div_pos (runner.savingFits request)
    (pow_pos (Nat.clog_pos (by norm_num) (by omega)) _)

def QuotientNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := runner.budget_pos
  registerBitsPositive := runner.budget_pos
  initialBitsFit := runner.initialBitsFit

def QuotientNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

theorem QuotientNatProgram.run_eq_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) :
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (runner.execute request) := by
  obtain ⟨output, houtput⟩ := runner.halts request
  simp [QuotientNatProgram.budget, QuotientNatProgram.execute,
    QuotientNatProgram.toBounded, BoundedNatProgram.execute, houtput]

def exponentialBudget (exponent measure : ℕ) : ℕ := 2 ^ (exponent * measure)

structure ExponentialNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  exponent : ℕ
  exponentPositive : 0 < exponent
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      exponentialBudget exponent (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (exponentialBudget exponent (measure request))
      (exponentialBudget exponent (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def ExponentialNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  exponentialBudget runner.exponent (measure request)

def ExponentialNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := fun _ => pow_pos (by omega) _
  registerBitsPositive := fun _ => pow_pos (by omega) _
  initialBitsFit := runner.initialBitsFit

def ExponentialNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

theorem ExponentialNatProgram.run_eq_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure)
    (request : Request) :
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (runner.execute request) := by
  obtain ⟨output, houtput⟩ := runner.halts request
  simp [ExponentialNatProgram.budget, ExponentialNatProgram.execute,
    ExponentialNatProgram.toBounded, BoundedNatProgram.execute, houtput]

structure ExponentialNatProgramWitness (Request : Type)
    (inputLength requestCode measure expectedOutput : Request → ℕ) where
  runner : ExponentialNatProgram Request inputLength requestCode measure
  computes : ∀ request,
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (expectedOutput request)

theorem ExponentialNatProgramWitness.execute_eq {Request : Type}
    {inputLength requestCode measure expectedOutput : Request → ℕ}
    (witness :
      ExponentialNatProgramWitness Request inputLength requestCode measure expectedOutput)
    (request : Request) :
    witness.runner.execute request = expectedOutput request := by
  simp [ExponentialNatProgram.execute, ExponentialNatProgram.toBounded,
    BoundedNatProgram.execute, witness.computes request]

/-! ## Exponential programs as total `E^NP` languages -/

/-- Canonical dependent request for evaluating one bit of a language.  The
input code is exactly the public code expected by `ENPCertificate`; the arity
already occupies interpreter register one and is not duplicated in the code. -/
structure LanguageEvaluationRequest where
  inputArity : ℕ
  input : BitInput inputArity

def LanguageEvaluationRequest.length
    (request : LanguageEvaluationRequest) : ℕ :=
  request.inputArity

def LanguageEvaluationRequest.code
    (request : LanguageEvaluationRequest) : ℕ :=
  encodeBitInput request.input

def LanguageEvaluationRequest.measure
    (request : LanguageEvaluationRequest) : ℕ :=
  max 1 request.inputArity

/-- A single exponential interpreter with a proved Boolean output.  Keeping
the output condition beside the runner rules out a semantic language path
whose values are unrelated to the certified execution trace. -/
structure ExecutableLanguageProgram where
  runner : ExponentialNatProgram LanguageEvaluationRequest
    LanguageEvaluationRequest.length LanguageEvaluationRequest.code
    LanguageEvaluationRequest.measure
  booleanOutput : ∀ request, runner.execute request ≤ 1

def ExecutableLanguageProgram.request
    (_program : ExecutableLanguageProgram)
    {n : ℕ} (input : BitInput n) : LanguageEvaluationRequest :=
  ⟨n, input⟩

def ExecutableLanguageProgram.language
    (program : ExecutableLanguageProgram) : Language :=
  fun _n input =>
    decide (program.runner.execute (program.request input) ≠ 0)

theorem ExecutableLanguageProgram.output_eq_languageBit
    (program : ExecutableLanguageProgram)
    {n : ℕ} (input : BitInput n) :
    program.runner.execute (program.request input) =
      (program.language n input).toNat := by
  have hbound := program.booleanOutput (program.request input)
  have hcases :
      program.runner.execute (program.request input) = 0 ∨
        program.runner.execute (program.request input) = 1 := by
    omega
  rcases hcases with hzero | hone
  · simp [ExecutableLanguageProgram.language, hzero]
  · simp [ExecutableLanguageProgram.language, hone]

/-- Extensional closure from the runner's exact output theorem.  Final
recovery linkers use this lemma directly, so language equality introduces no
separate semantic evaluator or callback. -/
theorem ExecutableLanguageProgram.language_eq_of_execute
    (program : ExecutableLanguageProgram)
    {n : ℕ} (target : BoolFunction n)
    (hexecutes :
      ∀ input : BitInput n,
        program.runner.execute (program.request input) =
          (target input).toNat) :
    program.language n = target := by
  funext input
  have hbits :
      (program.language n input).toNat = (target input).toNat :=
    (program.output_eq_languageBit input).symm.trans (hexecutes input)
  cases hlanguage : program.language n input <;>
    cases htarget : target input <;>
      simp_all

/-- The runner itself is the `E^NP` certificate; no extensional evaluator or
caller-supplied runtime proof is admitted at this boundary. -/
theorem ExecutableLanguageProgram.inENP
    (program : ExecutableLanguageProgram) :
    InENP program.language := by
  refine ⟨{
    program := program.runner.program
    exponent := program.runner.exponent
    exponentPositive := program.runner.exponentPositive
    /- At length zero the raw exponential budget is one instruction, which
    would force every total evaluator to halt at its entry point.  The runner
    charges `max 1 n`; from the first asymptotic length onward this is exactly
    the standard `2^(e·n)` certificate budget. -/
    onset := 1
    computes := ?_
  }⟩
  intro n hn input
  let request := program.request input
  have hrun := program.runner.run_eq_execute request
  rw [program.output_eq_languageBit input] at hrun
  simpa [request, ExecutableLanguageProgram.request,
    ExponentialNatProgram.budget, exponentialBudget,
    LanguageEvaluationRequest.length, LanguageEvaluationRequest.measure,
    LanguageEvaluationRequest.code, max_eq_right hn] using hrun

/-! ## Canonical finite encodings -/

def encodeNormalizedThresholdGate {n : ℕ}
    (gate : NormalizedThresholdGate n) : ℕ :=
  encodeTaggedList
    [encodeIntList (List.ofFn gate.weight),
      encodeInt gate.threshold]

def encodeExactThresholdGate {n : ℕ} (gate : ExactThresholdGate n) : ℕ :=
  Encodable.encode (List.ofFn gate.weight, gate.target)

def encodeExactThresholdGates {n : ℕ}
    (gates : List (ExactThresholdGate n)) : ℕ :=
  Encodable.encode (gates.map encodeExactThresholdGate)

def bitMatrixEntries {rows columns : ℕ}
    (matrix : BitMatrix rows columns) : List ℕ :=
  (List.ofFn fun row =>
    List.ofFn fun column => (matrix row column).toNat).flatten

def natMatrixEntries {rows columns : ℕ}
    (matrix : NatMatrix rows columns) : List ℕ :=
  (List.ofFn fun row =>
    List.ofFn fun column => matrix row column).flatten

/-- Dense matrices use one midpoint-balanced row-major sequence.  Recursive
`Encodable` lists double the register width at every cell and therefore cannot
serve as a polynomial-width machine ABI. -/
def encodeBitMatrix {rows columns : ℕ} (matrix : BitMatrix rows columns) : ℕ :=
  encodeBalancedList (bitMatrixEntries matrix)

def encodeNatMatrix {rows columns : ℕ} (matrix : NatMatrix rows columns) : ℕ :=
  encodeBalancedList (natMatrixEntries matrix)

@[simp] theorem bitMatrixEntries_length {rows columns : ℕ}
    (matrix : BitMatrix rows columns) :
    (bitMatrixEntries matrix).length = rows * columns := by
  simp [bitMatrixEntries, List.length_flatten, List.sum_ofFn]

theorem bitMatrixEntries_atomBits {rows columns : ℕ}
    (matrix : BitMatrix rows columns) (value : ℕ)
    (hvalue : value ∈ bitMatrixEntries matrix) :
    natBitLength value ≤ 1 := by
  simp only [bitMatrixEntries, List.mem_flatten, List.mem_ofFn] at hvalue
  rcases hvalue with ⟨rowValues, ⟨row, rfl⟩, hvalue⟩
  rcases List.mem_ofFn.mp hvalue with ⟨column, rfl⟩
  cases matrix row column <;> decide

/-- A dense Boolean matrix has polynomial structural width in its number of
cells.  This is the reusable public bound for request-budget proofs; callers
never need to charge the numeric value of the encoded tree. -/
theorem encodeBitMatrix_bits_le {rows columns : ℕ}
    (matrix : BitMatrix rows columns) :
    natBitLength (encodeBitMatrix matrix) ≤
      1 + 2 * (rows * columns) ^ 4 * (rows * columns + 1) := by
  unfold encodeBitMatrix
  apply balancedListCodeBits_le (bitMatrixEntries matrix) |>.trans
  unfold balancedListAtomBits
  have hsum :
      ((bitMatrixEntries matrix).map natBitLength).sum ≤
        (bitMatrixEntries matrix).length := by
    have hgeneral :
        ∀ values : List ℕ,
          (∀ value ∈ values, natBitLength value ≤ 1) →
            (values.map natBitLength).sum ≤ values.length := by
      intro values hvalues
      induction values with
      | nil => simp
      | cons value values ih =>
          have hvalue := hvalues value (by simp)
          have htail :
              ∀ tailValue ∈ values, natBitLength tailValue ≤ 1 := by
            intro tailValue htailValue
            exact hvalues tailValue (by simp [htailValue])
          simpa [Nat.add_comm] using Nat.add_le_add hvalue (ih htail)
    exact hgeneral (bitMatrixEntries matrix)
      (bitMatrixEntries_atomBits matrix)
  rw [bitMatrixEntries_length] at hsum ⊢
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right hsum 1

def encodeProjectedRandomBit {width : ℕ}
    (projection : ProjectedRandomBit width) : ℕ :=
  match projection with
  | .bit index => Nat.pair 0 index.val
  | .negatedBit index => Nat.pair 1 index.val
  | .constant value => Nat.pair 2 value.toNat

def encodeLiteral {arity : ℕ} (literal : Literal arity) : ℕ :=
  match literal with
  | .positive index => Nat.pair 0 index.val
  | .negative index => Nat.pair 1 index.val

def encodeThreeCNF {arity : ℕ} (formula : ThreeCNF arity) : ℕ :=
  Encodable.encode (formula.clauses.map fun clause =>
    List.ofFn fun index => encodeLiteral (clause index))

def encodeTwoLiteralClause {arity : ℕ}
    (clause : TwoLiteralClause arity) : ℕ :=
  Nat.pair (encodeLiteral clause.left) (encodeLiteral clause.right)

def encodeBoolFunction {n : ℕ} (function : BoolFunction n) : ℕ :=
  encodeBoolList (boolFunctionTable function)

@[simp] theorem decodeBoolList_encodeBoolFunction {n : ℕ}
    (function : BoolFunction n) :
    decodeBoolList (encodeBoolFunction function) =
      some (boolFunctionTable function) := by
  exact decodeBoolList_encode _

def encodeNPOracleInstruction : NPOracleInstruction → ℕ
  | .halt output => Nat.pair 0 output
  | .set register value next =>
      Nat.pair 1 (Nat.pair register (Nat.pair value next))
  | .copy source destination next =>
      Nat.pair 2 (Nat.pair source (Nat.pair destination next))
  | .increment register next => Nat.pair 3 (Nat.pair register next)
  | .decrement register next => Nat.pair 11 (Nat.pair register next)
  | .pair left right destination next =>
      Nat.pair 4 (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .unpairLeft source destination next =>
      Nat.pair 5 (Nat.pair source (Nat.pair destination next))
  | .unpairRight source destination next =>
      Nat.pair 6 (Nat.pair source (Nat.pair destination next))
  | .branchZero register zeroTarget nonzeroTarget =>
      Nat.pair 7 (Nat.pair register (Nat.pair zeroTarget nonzeroTarget))
  | .sat query destination next =>
      Nat.pair 8 (Nat.pair query (Nat.pair destination next))
  | .encodeNat source destination next =>
      Nat.pair 9 (Nat.pair source (Nat.pair destination next))
  | .shiftRight source amount destination next =>
      Nat.pair 10
        (Nat.pair source (Nat.pair amount (Nat.pair destination next)))
  | .testBit source index destination next =>
      Nat.pair 12
        (Nat.pair source (Nat.pair index (Nat.pair destination next)))
  | .add left right destination next =>
      Nat.pair 13
        (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .subtract left right destination next =>
      Nat.pair 14
        (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .shiftLeft source amount destination next =>
      Nat.pair 15
        (Nat.pair source (Nat.pair amount (Nat.pair destination next)))

def encodeNPOracleProgram (program : NPOracleProgram) : ℕ :=
  Encodable.encode (program.map encodeNPOracleInstruction)

/-! ## Executable refinements of finite algorithms -/

structure ExactDecompositionRequest where
  arity : ℕ
  gate : NormalizedThresholdGate arity

def ExactDecompositionRequest.length (request : ExactDecompositionRequest) : ℕ :=
  request.arity

def ExactDecompositionRequest.code (request : ExactDecompositionRequest) : ℕ :=
  encodeNormalizedThresholdGate request.gate

def ExactDecompositionRequest.measure (request : ExactDecompositionRequest) : ℕ :=
  request.arity + request.gate.encodingBits

def decodeExactThresholdGates (n code : ℕ) : List (ExactThresholdGate n) :=
  let raw := (Encodable.decode code : Option (List (List ℤ × ℤ))).getD []
  raw.map fun gate =>
    { weight := fun index => gate.1.getD index.val 0
      target := gate.2 }

/-- Both the output list and the resource charge are derived from one runner. -/
structure ExecutableExactDecompositionAlgorithm where
  runner : PolynomialNatProgram ExactDecompositionRequest
    ExactDecompositionRequest.length ExactDecompositionRequest.code
    ExactDecompositionRequest.measure
  oracleFree : OracleFree runner.program
  equivalent : ∀ request input,
    request.gate.strictEval input =
      (decodeExactThresholdGates request.arity
        (runner.execute request)).any (fun child => child.eval input)
  disjoint : ∀ request input,
    ((decodeExactThresholdGates request.arity
      (runner.execute request)).filter fun child => child.eval input).length ≤ 1

def ExecutableExactDecompositionAlgorithm.run
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : NormalizedThresholdGate n) : ExactDecomposition gate :=
  let request : ExactDecompositionRequest := ⟨n, gate⟩
  { children := decodeExactThresholdGates n (algorithm.runner.execute request)
    equivalent := algorithm.equivalent request
    disjoint := algorithm.disjoint request }

def ExecutableExactDecompositionAlgorithm.toSemantic
    (algorithm : ExecutableExactDecompositionAlgorithm) :
    ExactDecompositionAlgorithm where
  run := algorithm.run
  steps := fun {n} gate =>
    algorithm.runner.budget (⟨n, gate⟩ : ExactDecompositionRequest)

structure RectangularProductRequest where
  dimension : ℕ
  left : BitMatrix dimension (rectangularInnerDimension dimension)
  right : BitMatrix (rectangularInnerDimension dimension) dimension

def RectangularProductRequest.length (request : RectangularProductRequest) : ℕ :=
  request.dimension

def RectangularProductRequest.code (request : RectangularProductRequest) : ℕ :=
  Nat.pair (encodeBitMatrix request.left) (encodeBitMatrix request.right)

def RectangularProductRequest.measure (request : RectangularProductRequest) : ℕ :=
  request.dimension

def decodeNatMatrix (rows columns code : ℕ) : NatMatrix rows columns :=
  let raw := (decodeBalancedList code).getD []
  fun row column => raw.getD (row.val * columns + column.val) 0

structure ExecutableRectangularProductAlgorithm where
  runner : PolynomialNatProgram RectangularProductRequest
    RectangularProductRequest.length RectangularProductRequest.code
    RectangularProductRequest.measure
  oracleFree : OracleFree runner.program

def ExecutableRectangularProductAlgorithm.compute
    (algorithm : ExecutableRectangularProductAlgorithm) (U : ℕ)
    (left : BitMatrix U (rectangularInnerDimension U))
    (right : BitMatrix (rectangularInnerDimension U) U) : NatMatrix U U :=
  let request : RectangularProductRequest := ⟨U, left, right⟩
  decodeNatMatrix U U (algorithm.runner.execute request)

def ExecutableRectangularProductAlgorithm.toSemantic
    (algorithm : ExecutableRectangularProductAlgorithm) :
    RectangularProductAlgorithm where
  compute := algorithm.compute
  steps := fun U left right =>
    algorithm.runner.budget
      (⟨U, left, right⟩ : RectangularProductRequest)

/-- The **retired** form of the published decomposition row: the algorithm
together with a polynomial bound on the number of children it emits.  Kept only
so that the weakening below is a checked Lean fact rather than a claim in a
comment.  Nothing in the development assumes this. -/
def LegacyDisjointExactDecompositionContract : Prop :=
  ∃ algorithm : ExecutableExactDecompositionAlgorithm,
    ∀ request : ExactDecompositionRequest,
      (algorithm.run request.gate).children.length ≤
        algorithm.runner.budget request

/-- The published decomposition row assumes **only** that the algorithm exists.

The child-count clause the row used to carry is not a fact about the imported
source at all: it is forced by the fixed `NPOracleProgram` interpreter, because
the child list is decoded from the runner's single output word whose binary
width is already charged to `runner.budget`.  See
`TrustExactDecompositionChildCount`, which derives it
(`ExecutableExactDecompositionAlgorithm.children_length_le_budget`) and proves
this definition equivalent to `LegacyDisjointExactDecompositionContract`, so the
weakening loses nothing.

This matters because the row is presented as literature.  `paper.tex:2306-2310`
imports only the *qualitative* conversion, "with the complete construction and
safe quantitative bounds replayed locally in Appendix A.12", and A.12 exists
because CW19's printed Lemma 48 proof contains three identified errors, the
replay importing "no one of those three literal claims"
(`paper.tex:2698-2705`).  Storing the quantitative half here re-imported exactly
the dependency the manuscript declines.  It no longer does.

The semantic projection `executableDisjointDecomposition_implies_semantic` lives
in that module, since it now consumes the derived bound; it keeps this
namespace, so no consumer is renamed. -/
def ExecutableDisjointExactDecompositionContract : Prop :=
  Nonempty ExecutableExactDecompositionAlgorithm

def ExecutableBooleanRectangularProductContract : Prop :=
  ∃ algorithm : ExecutableRectangularProductAlgorithm,
    ∃ onset coefficient logExponent : ℕ, 0 < coefficient ∧
      ∀ request : RectangularProductRequest, onset ≤ request.dimension →
        algorithm.compute request.dimension request.left request.right =
            integerMatrixProduct request.left request.right ∧
          algorithm.runner.budget request ≤
            coefficient * request.dimension ^ 2 *
              logScale request.dimension ^ logExponent

theorem executableRectangularProduct_implies_semantic :
    ExecutableBooleanRectangularProductContract →
      BooleanRectangularProductContract := by
  rintro ⟨algorithm, onset, coefficient, logExponent, hcoefficient, contract⟩
  refine ⟨algorithm.toSemantic, onset, coefficient, logExponent,
    hcoefficient, ?_⟩
  intro U hU left right
  simpa [ExecutableRectangularProductAlgorithm.toSemantic] using
    contract (⟨U, left, right⟩ : RectangularProductRequest) hU

/-! ## Projection PCP: construction and every queried coordinate are executable -/

def decodeProjectedRandomBit (width code : ℕ) : ProjectedRandomBit width :=
  let tagAndIndex := Nat.unpair code
  if hwidth : width = 0 then
    .constant (tagAndIndex.2.testBit 0)
  else
    let index : Fin width :=
      ⟨tagAndIndex.2 % width, Nat.mod_lt _ (Nat.pos_of_ne_zero hwidth)⟩
    if tagAndIndex.1 % 3 = 0 then .bit index
    else if tagAndIndex.1 % 3 = 1 then .negatedBit index
    else .constant (tagAndIndex.2.testBit 0)

def decodeLiteral {arity : ℕ} (arityPositive : 0 < arity)
    (code : ℕ) : Literal arity :=
  let tagAndIndex := Nat.unpair code
  let index : Fin arity :=
    ⟨tagAndIndex.2 % arity, Nat.mod_lt _ arityPositive⟩
  if tagAndIndex.1 % 2 = 0 then .positive index else .negative index

def decodeThreeCNF (arity code : ℕ) : ThreeCNF arity :=
  if harity : 0 < arity then
    let raw := (Encodable.decode code : Option (List (List ℕ))).getD []
    { clauses := raw.map fun clause index =>
        decodeLiteral harity (clause.getD index.val 0) }
  else
    { clauses := [] }

structure ProjectionQueryRequest where
  inputArity : ℕ
  width : ℕ
  count : ℕ
  input : BitInput inputArity
  query : Fin count
  bit : Fin width

def ProjectionQueryRequest.length (request : ProjectionQueryRequest) : ℕ :=
  request.inputArity

def ProjectionQueryRequest.code (request : ProjectionQueryRequest) : ℕ :=
  Nat.pair request.inputArity (Nat.pair (encodeBitInput request.input)
    (Nat.pair request.query.val request.bit.val))

def ProjectionQueryRequest.measure (request : ProjectionQueryRequest) : ℕ :=
  request.inputArity + request.width + request.count

structure ProjectionDecisionRequest where
  inputArity : ℕ
  width : ℕ
  count : ℕ
  input : BitInput inputArity
  randomness : BitInput width

def ProjectionDecisionRequest.length (request : ProjectionDecisionRequest) : ℕ :=
  request.inputArity

def ProjectionDecisionRequest.code (request : ProjectionDecisionRequest) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input)
      (encodeBitInput request.randomness))

def ProjectionDecisionRequest.measure (request : ProjectionDecisionRequest) : ℕ :=
  request.inputArity + request.width + request.count

structure ExecutableProjectionPCP (machine : TimedDecisionMachine)
    (timeBound : ℕ → ℕ) where
  shape : PolynomialNatProgram ℕ id id
    (fun n => n + logScale (timeBound n))
  shapeOracleFree : OracleFree shape.program
  query : PolynomialNatProgram ProjectionQueryRequest
    ProjectionQueryRequest.length ProjectionQueryRequest.code
    ProjectionQueryRequest.measure
  queryOracleFree : OracleFree query.program
  decisionRunner : PolynomialNatProgram ProjectionDecisionRequest
    ProjectionDecisionRequest.length ProjectionDecisionRequest.code
    ProjectionDecisionRequest.measure
  decisionOracleFree : OracleFree decisionRunner.program

def ExecutableProjectionPCP.shapeCode {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  pcp.shape.execute n

def ExecutableProjectionPCP.nativeWidth {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  (Nat.unpair (pcp.shapeCode n)).1

def ExecutableProjectionPCP.queryCount {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  (Nat.unpair (pcp.shapeCode n)).2

def ExecutableProjectionPCP.queryRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) : ProjectionQueryRequest :=
  ⟨n, pcp.nativeWidth n, pcp.queryCount n, input, query, bit⟩

def ExecutableProjectionPCP.queryAddressBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    ProjectedRandomBit (pcp.nativeWidth n) :=
  let outputCode := pcp.query.execute (pcp.queryRequest input query bit)
  decodeProjectedRandomBit (pcp.nativeWidth n) outputCode

def ExecutableProjectionPCP.decisionRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    ProjectionDecisionRequest :=
  ⟨n, pcp.nativeWidth n, pcp.queryCount n, input, randomness⟩

def ExecutableProjectionPCP.decision
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    ThreeCNF (pcp.queryCount n) :=
  let outputCode :=
    pcp.decisionRunner.execute (pcp.decisionRequest input randomness)
  decodeThreeCNF (pcp.queryCount n) outputCode

def ExecutableProjectionPCP.toSemantic
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    ProjectionPCP machine timeBound where
  nativeWidth := pcp.nativeWidth
  queryCount := pcp.queryCount
  queryAddressBits := pcp.queryAddressBits
  decision := pcp.decision
  constructionSteps := pcp.shape.budget

@[simp] theorem ExecutableProjectionPCP.toSemantic_nativeWidth
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    pcp.toSemantic.nativeWidth n = pcp.nativeWidth n := rfl

@[simp] theorem ExecutableProjectionPCP.toSemantic_queryCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    pcp.toSemantic.queryCount n = pcp.queryCount n := rfl

@[simp] theorem ExecutableProjectionPCP.toSemantic_constructionSteps
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    pcp.toSemantic.constructionSteps n =
      pcp.shape.coefficient *
        (n + logScale (timeBound n) + 1) ^ pcp.shape.degree := by
  rfl

/-- The source PCP's compact substitution receives one fixed input and a
candidate oracle circuit.  The charged measure includes every variable-sized
part of the request; in particular, the oracle is charged by DAG size. -/
structure ProjectionSubstitutionRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) where
  inputArity : ℕ
  input : BitInput inputArity
  oracle : BooleanCircuit (pcp.nativeWidth inputArity)

def ProjectionSubstitutionRequest.length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  request.inputArity

def ProjectionSubstitutionRequest.code
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input)
      (encodeBooleanCircuit request.oracle))

def ProjectionSubstitutionRequest.measure
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  request.inputArity + pcp.nativeWidth request.inputArity + request.oracle.size

structure ExecutableProjectionSubstitution
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) where
  circuit : (request : ProjectionSubstitutionRequest pcp) →
    BooleanCircuit (pcp.nativeWidth request.inputArity)
  runner : PolynomialNatProgram (ProjectionSubstitutionRequest pcp)
    ProjectionSubstitutionRequest.length
    ProjectionSubstitutionRequest.code
    ProjectionSubstitutionRequest.measure
  runnerOracleFree : OracleFree runner.program
  computes : ∀ request,
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState request.inputArity
        (ProjectionSubstitutionRequest.code request)) =
      some (encodeBooleanCircuit (circuit request))
  equivalent : ∀ request randomness,
    (circuit request).eval randomness =
      (pcp.decision request.input randomness).eval fun query =>
        request.oracle.eval fun bit =>
          (pcp.queryAddressBits request.input query bit).eval randomness
  sizeCoefficient : ℕ
  sizeCoefficientPositive : 0 < sizeCoefficient

def ExecutableProjectionPCPGuarantee
    (runnerDegree queryExponent substitutionExponent : ℕ) : Prop :=
  ∀ (machine : TimedDecisionMachine) (timeBound : ℕ → ℕ),
    (∀ n input, machine.steps n input ≤ timeBound n) →
    (∀ n, n ≤ timeBound n) →
    ∃ pcp : ExecutableProjectionPCP machine timeBound,
      ∃ proofExponent : ℕ,
        ∃ substitution : ExecutableProjectionSubstitution pcp,
        pcp.shape.degree ≤ runnerDegree ∧
        pcp.query.degree ≤ runnerDegree ∧
        pcp.decisionRunner.degree ≤ runnerDegree ∧
        substitution.runner.degree ≤ runnerDegree ∧
        (∀ n, pcp.queryCount n ≤ pcp.shape.budget n) ∧
        (∀ n,
          pcp.queryCount n ≤
            pcp.shape.coefficient *
              (pcp.nativeWidth n + 1) ^ queryExponent) ∧
        (∀ n input randomness,
          (pcp.decision (n := n) input randomness).clauses.length ≤
            pcp.decisionRunner.budget
              (pcp.decisionRequest input randomness)) ∧
        (∀ n,
          2 ^ pcp.nativeWidth n ≤
            pcp.shape.coefficient * timeBound n *
              logScale (timeBound n) ^ proofExponent) ∧
        (∀ request,
          (substitution.circuit request).size ≤
            substitution.sizeCoefficient *
              (pcp.nativeWidth request.inputArity +
                request.oracle.size + 1) ^ substitutionExponent) ∧
        (∀ n input, machine.accepts n input →
          ∃ proof, ∀ randomness, pcp.toSemantic.accepts input proof randomness) ∧
        (∀ n input, ¬machine.accepts n input →
          ∀ proof, pcp.toSemantic.acceptanceFraction input proof ≤
            1 / ((n + 1 : ℕ) : ℝ) ^ 10)

def ExecutableProjectionPCPContract : Prop :=
  ∃ runnerDegree queryExponent substitutionExponent : ℕ,
    ExecutableProjectionPCPGuarantee
      runnerDegree queryExponent substitutionExponent

/-- Uniform projection-PCP parameters selected before any hierarchy machine or
refuter source.  This package is the only safe input to a verifier-degree
ledger whose clock must be frozen before the refuter contract is instantiated. -/
structure UniformProjectionPCPSource where
  runnerDegree : ℕ
  queryExponent : ℕ
  substitutionExponent : ℕ
  guarantee : ExecutableProjectionPCPGuarantee
    runnerDegree queryExponent substitutionExponent

theorem existsUniformProjectionPCPSource
    (contract : ExecutableProjectionPCPContract) :
    Nonempty UniformProjectionPCPSource := by
  rcases contract with
    ⟨runnerDegree, queryExponent, substitutionExponent, guarantee⟩
  exact
    ⟨{ runnerDegree := runnerDegree
       queryExponent := queryExponent
       substitutionExponent := substitutionExponent
       guarantee := guarantee }⟩

theorem executableProjectionPCP_implies_semantic :
    ExecutableProjectionPCPContract → ProjectionPCPContract := by
  rintro ⟨_runnerDegree, _queryExponent, _substitutionExponent, contract⟩
    machine timeBound hsteps htime
  obtain ⟨pcp, proofExponent, _substitution, _, _, _, _, _, _, _,
      hproof, _, hcomplete, hsound⟩ :=
    contract machine timeBound hsteps htime
  refine ⟨pcp.toSemantic, pcp.shape.coefficient, proofExponent,
    pcp.shape.degree, pcp.shape.coefficientPositive, ?_, ?_, ?_, ?_⟩
  · simpa using hproof
  · simpa using hcomplete
  · simpa using hsound
  · intro n
    exact le_rfl

/-! ## Pointwise PCPP: shape, clauses, supports, and honest words are executable -/

structure PointwiseShapeRequest where
  inputArity : ℕ
  circuitSize : ℕ
  circuitCode : ℕ

def PointwiseShapeRequest.length (request : PointwiseShapeRequest) : ℕ :=
  request.inputArity

def PointwiseShapeRequest.code (request : PointwiseShapeRequest) : ℕ :=
  request.circuitCode

def PointwiseShapeRequest.measure (request : PointwiseShapeRequest) : ℕ :=
  request.circuitSize

abbrev PointwiseShapeRunner {n : ℕ} (circuit : BooleanCircuit n) :=
  PolynomialNatProgram Unit (fun _ => n)
    (fun _ => encodeBooleanCircuit circuit) (fun _ => circuit.size)

def pointwiseShapeCode {n : ℕ} {circuit : BooleanCircuit n}
    (shape : PointwiseShapeRunner circuit) : ℕ :=
  shape.execute ()

/-- The offset makes the decoded assignment arity positive by construction. -/
def pointwiseSystematicBits {n : ℕ} {circuit : BooleanCircuit n}
    (shape : PointwiseShapeRunner circuit) : ℕ :=
  (Nat.unpair (pointwiseShapeCode shape)).1 + 1

def pointwiseAuxiliaryBits {n : ℕ} {circuit : BooleanCircuit n}
    (shape : PointwiseShapeRunner circuit) : ℕ :=
  (Nat.unpair (Nat.unpair (pointwiseShapeCode shape)).2).1

def pointwiseClauseBits {n : ℕ} {circuit : BooleanCircuit n}
    (shape : PointwiseShapeRunner circuit) : ℕ :=
  (Nat.unpair (Nat.unpair (pointwiseShapeCode shape)).2).2

def decodeSupport (n code : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun index => code.testBit index.val

def decodeTwoLiteralClause (arity : ℕ) (arityPositive : 0 < arity)
    (code : ℕ) : TwoLiteralClause arity :=
  { left := decodeLiteral arityPositive (Nat.unpair code).1
    right := decodeLiteral arityPositive (Nat.unpair code).2 }

structure PointwiseSupportRequest where
  inputArity : ℕ
  circuitSize : ℕ
  circuitCode : ℕ
  systematicIndex : ℕ

def PointwiseSupportRequest.length (request : PointwiseSupportRequest) : ℕ :=
  request.inputArity

def PointwiseSupportRequest.code (request : PointwiseSupportRequest) : ℕ :=
  Nat.pair request.circuitCode request.systematicIndex

def PointwiseSupportRequest.measure (request : PointwiseSupportRequest) : ℕ :=
  request.circuitSize + request.inputArity

structure PointwiseClauseRequest where
  inputArity : ℕ
  circuitSize : ℕ
  circuitCode : ℕ
  assignmentArity : ℕ
  clauseIndex : ℕ

def PointwiseClauseRequest.length (request : PointwiseClauseRequest) : ℕ :=
  request.inputArity

def PointwiseClauseRequest.code (request : PointwiseClauseRequest) : ℕ :=
  Nat.pair request.circuitCode request.clauseIndex

def PointwiseClauseRequest.measure (request : PointwiseClauseRequest) : ℕ :=
  request.circuitSize + request.assignmentArity

structure PointwiseHonestRequest where
  inputArity : ℕ
  circuitSize : ℕ
  circuitCode : ℕ
  input : BitInput inputArity

def PointwiseHonestRequest.length (request : PointwiseHonestRequest) : ℕ :=
  request.inputArity

def PointwiseHonestRequest.code (request : PointwiseHonestRequest) : ℕ :=
  Nat.pair request.circuitCode (encodeBitInput request.input)

def PointwiseHonestRequest.measure (request : PointwiseHonestRequest) : ℕ :=
  request.circuitSize + request.inputArity

structure ExecutablePointwisePCPP {n : ℕ} (circuit : BooleanCircuit n) where
  shape : PointwiseShapeRunner circuit
  shapeOracleFree : OracleFree shape.program
  supportRunner : PolynomialNatProgram PointwiseSupportRequest
    PointwiseSupportRequest.length PointwiseSupportRequest.code
    PointwiseSupportRequest.measure
  supportOracleFree : OracleFree supportRunner.program
  clauseRunner : PolynomialNatProgram PointwiseClauseRequest
    PointwiseClauseRequest.length PointwiseClauseRequest.code
    PointwiseClauseRequest.measure
  clauseOracleFree : OracleFree clauseRunner.program
  honestRunner : PolynomialNatProgram PointwiseHonestRequest
    PointwiseHonestRequest.length PointwiseHonestRequest.code
    PointwiseHonestRequest.measure
  honestOracleFree : OracleFree honestRunner.program

/-- One uniform source algorithm serves every substituted circuit.  The
circuit code is data in each request; no runner program may be selected after
the weak machine sees a guessed oracle. -/
structure ExecutablePointwisePCPPFactory where
  shapeRunner : PolynomialNatProgram PointwiseShapeRequest
    PointwiseShapeRequest.length PointwiseShapeRequest.code
    PointwiseShapeRequest.measure
  shapeOracleFree : OracleFree shapeRunner.program
  supportRunner : PolynomialNatProgram PointwiseSupportRequest
    PointwiseSupportRequest.length PointwiseSupportRequest.code
    PointwiseSupportRequest.measure
  supportOracleFree : OracleFree supportRunner.program
  clauseRunner : PolynomialNatProgram PointwiseClauseRequest
    PointwiseClauseRequest.length PointwiseClauseRequest.code
    PointwiseClauseRequest.measure
  clauseOracleFree : OracleFree clauseRunner.program
  honestRunner : PolynomialNatProgram PointwiseHonestRequest
    PointwiseHonestRequest.length PointwiseHonestRequest.code
    PointwiseHonestRequest.measure
  honestOracleFree : OracleFree honestRunner.program

def ExecutablePointwisePCPPFactory.shapeRequest
    (_factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) : PointwiseShapeRequest :=
  ⟨n, circuit.size, encodeBooleanCircuit circuit⟩

/-- Specialize the sole uniform shape runner to the dependent PCPP view
required by the semantic source interface. -/
def ExecutablePointwisePCPPFactory.shapeFor
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) : PointwiseShapeRunner circuit where
  program := factory.shapeRunner.program
  coefficient := factory.shapeRunner.coefficient
  coefficientPositive := factory.shapeRunner.coefficientPositive
  degree := factory.shapeRunner.degree
  initialBitsFit := by
    intro _
    simpa [PointwiseShapeRequest.length, PointwiseShapeRequest.code,
      PointwiseShapeRequest.measure,
      ExecutablePointwisePCPPFactory.shapeRequest] using
      factory.shapeRunner.initialBitsFit (factory.shapeRequest circuit)
  halts := by
    intro _
    simpa [PointwiseShapeRequest.length, PointwiseShapeRequest.code,
      PointwiseShapeRequest.measure,
      ExecutablePointwisePCPPFactory.shapeRequest] using
      factory.shapeRunner.halts (factory.shapeRequest circuit)

/-- The dependent semantic object is a view of the single factory, not a
second circuit-specific source implementation. -/
def ExecutablePointwisePCPPFactory.forCircuit
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) :
    ExecutablePointwisePCPP circuit where
  shape := factory.shapeFor circuit
  shapeOracleFree := factory.shapeOracleFree
  supportRunner := factory.supportRunner
  supportOracleFree := factory.supportOracleFree
  clauseRunner := factory.clauseRunner
  clauseOracleFree := factory.clauseOracleFree
  honestRunner := factory.honestRunner
  honestOracleFree := factory.honestOracleFree

def ExecutablePointwisePCPP.systematicBits {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit) : ℕ :=
  pointwiseSystematicBits pcpp.shape

def ExecutablePointwisePCPP.auxiliaryBits {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit) : ℕ :=
  pointwiseAuxiliaryBits pcpp.shape

def ExecutablePointwisePCPP.clauseBits {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit) : ℕ :=
  pointwiseClauseBits pcpp.shape

def ExecutablePointwisePCPP.systematicSupport {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit)
    (index : Fin pcpp.systematicBits) : Finset (Fin n) :=
  let request : PointwiseSupportRequest :=
    ⟨n, circuit.size, encodeBooleanCircuit circuit, index.val⟩
  let outputCode := pcpp.supportRunner.execute request
  decodeSupport n outputCode

def ExecutablePointwisePCPP.clause {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit)
    (index : Fin (2 ^ pcpp.clauseBits)) :
    TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  let request : PointwiseClauseRequest :=
    ⟨n, circuit.size, encodeBooleanCircuit circuit,
      pcpp.systematicBits + pcpp.auxiliaryBits, index.val⟩
  let outputCode := pcpp.clauseRunner.execute request
  decodeTwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits)
    (by
      apply Nat.add_pos_left
      simp [ExecutablePointwisePCPP.systematicBits, pointwiseSystematicBits])
    outputCode

def ExecutablePointwisePCPP.honestAuxiliary {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit)
    (input : BitInput n) : BitInput pcpp.auxiliaryBits :=
  let request : PointwiseHonestRequest :=
    ⟨n, circuit.size, encodeBooleanCircuit circuit, input⟩
  let outputCode := pcpp.honestRunner.execute request
  fun index => outputCode.testBit index.val

def ExecutablePointwisePCPP.toSemantic {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : ExecutablePointwisePCPP circuit)
    (supportBound :
      ∀ i, (pcpp.systematicSupport i).card ≤ n / 2) :
    PointwisePCPP circuit where
  systematicBits := pcpp.systematicBits
  auxiliaryBits := pcpp.auxiliaryBits
  clauseBits := pcpp.clauseBits
  systematicSupport := pcpp.systematicSupport
  systematicSupportBound := supportBound
  clauses := pcpp.clause
  honestAuxiliary := pcpp.honestAuxiliary
  constructionSteps := pcpp.shape.budget ()
  honestSteps := fun input =>
    pcpp.honestRunner.budget
      (⟨n, circuit.size, encodeBooleanCircuit circuit, input⟩ :
        PointwiseHonestRequest)

@[simp] theorem ExecutablePointwisePCPP.toSemantic_constructionSteps
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (supportBound : ∀ i, (pcpp.systematicSupport i).card ≤ n / 2) :
    (pcpp.toSemantic supportBound).constructionSteps =
      pcpp.shape.coefficient * (circuit.size + 1) ^ pcpp.shape.degree := by
  rfl

@[simp] theorem ExecutablePointwisePCPP.toSemantic_honestSteps
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (supportBound : ∀ i, (pcpp.systematicSupport i).card ≤ n / 2)
    (input : BitInput n) :
    (pcpp.toSemantic supportBound).honestSteps input =
      pcpp.honestRunner.coefficient *
        (circuit.size + n + 1) ^ pcpp.honestRunner.degree := by
  rfl

/-- Executable form of the imported pointwise two-query PCPP.  The explicit
`2 ^ clauseBits` bound records the source theorem's polynomial-size clause
list; bounding the address width alone would permit exponentially many
clauses in a polynomial-width address and would not support the fixed recovery
schedule. -/
def ExecutablePointwisePCPPContract : Prop :=
  ∃ completeness soundness : ℝ, soundness < completeness ∧
    ∃ coefficient degree runnerDegree : ℕ,
    ∃ factory : ExecutablePointwisePCPPFactory, 0 < coefficient ∧
      ∀ {n : ℕ} (circuit : BooleanCircuit n), n ≤ circuit.size →
        let pcpp := factory.forCircuit circuit
        ∃ supportBound :
            ∀ i, (pcpp.systematicSupport i).card ≤ n / 2,
          pcpp.shape.degree ≤ runnerDegree ∧
          pcpp.supportRunner.degree ≤ runnerDegree ∧
          pcpp.clauseRunner.degree ≤ runnerDegree ∧
          pcpp.honestRunner.degree ≤ runnerDegree ∧
          pcpp.systematicBits + pcpp.auxiliaryBits + pcpp.clauseBits ≤
            pcpp.shape.budget () ∧
          2 ^ pcpp.clauseBits ≤
            coefficient * (circuit.size + 1) ^ degree ∧
          (pcpp.toSemantic supportBound).constructionSteps ≤
              coefficient * (circuit.size + 1) ^ degree ∧
          (∀ input, circuit.eval input →
            (pcpp.toSemantic supportBound).satisfiedFraction input
                ((pcpp.toSemantic supportBound).honestAuxiliary input) ≥
              completeness) ∧
          (∀ input, ¬circuit.eval input →
            ∀ auxiliary,
              (pcpp.toSemantic supportBound).satisfiedFraction input auxiliary ≤
                soundness) ∧
          (∀ input, (pcpp.toSemantic supportBound).honestSteps input ≤
            coefficient * (circuit.size + 1) ^ degree)

/-- The fixed data obtained by opening the published PCPP contract once.
Keeping the factory beside its semantic guarantees makes the program
uniformity available to the weak verifier without accepting any new premise. -/
structure UniformPointwisePCPPSource where
  completeness : ℝ
  soundness : ℝ
  gap : soundness < completeness
  coefficient : ℕ
  degree : ℕ
  runnerDegree : ℕ
  factory : ExecutablePointwisePCPPFactory
  coefficientPositive : 0 < coefficient
  guarantee : ∀ {n : ℕ} (circuit : BooleanCircuit n), n ≤ circuit.size →
    let pcpp := factory.forCircuit circuit
    ∃ supportBound :
        ∀ i, (pcpp.systematicSupport i).card ≤ n / 2,
      pcpp.shape.degree ≤ runnerDegree ∧
      pcpp.supportRunner.degree ≤ runnerDegree ∧
      pcpp.clauseRunner.degree ≤ runnerDegree ∧
      pcpp.honestRunner.degree ≤ runnerDegree ∧
      pcpp.systematicBits + pcpp.auxiliaryBits + pcpp.clauseBits ≤
        pcpp.shape.budget () ∧
      2 ^ pcpp.clauseBits ≤
        coefficient * (circuit.size + 1) ^ degree ∧
      (pcpp.toSemantic supportBound).constructionSteps ≤
          coefficient * (circuit.size + 1) ^ degree ∧
      (∀ input, circuit.eval input →
        (pcpp.toSemantic supportBound).satisfiedFraction input
            ((pcpp.toSemantic supportBound).honestAuxiliary input) ≥
          completeness) ∧
      (∀ input, ¬circuit.eval input →
        ∀ auxiliary,
          (pcpp.toSemantic supportBound).satisfiedFraction input auxiliary ≤
            soundness) ∧
      (∀ input, (pcpp.toSemantic supportBound).honestSteps input ≤
        coefficient * (circuit.size + 1) ^ degree)

theorem existsUniformPointwisePCPPSource
    (contract : ExecutablePointwisePCPPContract) :
    Nonempty UniformPointwisePCPPSource := by
  rcases contract with
    ⟨completeness, soundness, gap, coefficient, degree, runnerDegree,
      factory, coefficientPositive, guarantee⟩
  exact
    ⟨{ completeness := completeness
       soundness := soundness
       gap := gap
       coefficient := coefficient
       degree := degree
       runnerDegree := runnerDegree
       factory := factory
       coefficientPositive := coefficientPositive
       guarantee := guarantee }⟩

theorem executablePointwisePCPP_implies_semantic :
    ExecutablePointwisePCPPContract → PointwisePCPPContract := by
  intro contract
  obtain ⟨completeness, soundness, hgap, coefficient, degree, _runnerDegree,
    factory, hcoefficient, contract⟩ := contract
  refine ⟨completeness, soundness, hgap, coefficient, degree,
    hcoefficient, ?_⟩
  intro n circuit hsize
  obtain ⟨supportBound, _, _, _, _, _, _,
      hconstruction, hcomplete, hsound, hhonest⟩ :=
    contract circuit hsize
  let pcpp := factory.forCircuit circuit
  exact ⟨pcpp.toSemantic supportBound, hconstruction, hcomplete, hsound, hhonest⟩

def ExecutableProjectionPcpAndPcppContract : Prop :=
  ExecutableProjectionPCPContract ∧ ExecutablePointwisePCPPContract

theorem executableProjectionPcpAndPcpp_implies_semantic :
    ExecutableProjectionPcpAndPcppContract →
      ProjectionPcpAndPcppContract := by
  rintro ⟨hpcp, hpcpp⟩
  exact ⟨executableProjectionPCP_implies_semantic hpcp,
    executablePointwisePCPP_implies_semantic hpcpp⟩

/-! ## Executable weak machines and the SAT-oracle refuter -/

structure WeakVerifierRequest where
  inputArity : ℕ
  witnessArity : ℕ
  input : BitInput inputArity
  witness : BitInput witnessArity

def WeakVerifierRequest.length (request : WeakVerifierRequest) : ℕ :=
  request.inputArity

def WeakVerifierRequest.code (request : WeakVerifierRequest) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input) (encodeBitInput request.witness))

def WeakVerifierRequest.measure (request : WeakVerifierRequest) : ℕ :=
  request.inputArity + request.witnessArity

/-- The machine's verifier and witness-length function are both interpreter
programs.  Its semantic `run` and `steps` fields below are derived, not stored. -/
structure ExecutableWeakNondeterministicMachine where
  witnessShape : PolynomialNatProgram ℕ id id id
  witnessShapeOracleFree : OracleFree witnessShape.program
  verifier : QuotientNatProgram WeakVerifierRequest
    WeakVerifierRequest.length WeakVerifierRequest.code WeakVerifierRequest.measure
  verifierOracleFree : OracleFree verifier.program

def ExecutableWeakNondeterministicMachine.witnessBits
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  machine.witnessShape.execute n

def ExecutableWeakNondeterministicMachine.verifierBudget
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  machine.verifier.budget
    { inputArity := n
      witnessArity := machine.witnessBits n
      input := fun _ => false
      witness := fun _ => false }

def ExecutableWeakNondeterministicMachine.verifierRequest
    (machine : ExecutableWeakNondeterministicMachine) {n : ℕ}
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    WeakVerifierRequest :=
  ⟨n, machine.witnessBits n, input, witness⟩

def ExecutableWeakNondeterministicMachine.run
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) : Bool :=
  let outputCode :=
    machine.verifier.execute (machine.verifierRequest input witness)
  outputCode != 0

def ExecutableWeakNondeterministicMachine.toSemantic
    (machine : ExecutableWeakNondeterministicMachine) :
    WeakNondeterministicMachine where
  witnessBits := machine.witnessBits
  run := machine.run
  steps := fun n _ _ => machine.verifierBudget n

def ExecutableWeakNondeterministicMachine.description
    (machine : ExecutableWeakNondeterministicMachine) : ℕ :=
  Nat.pair (encodeNPOracleProgram machine.witnessShape.program)
    (Nat.pair machine.witnessShape.coefficient
      (Nat.pair machine.witnessShape.degree
        (Nat.pair (encodeNPOracleProgram machine.verifier.program)
          (Nat.pair machine.verifier.coefficient
            (Nat.pair machine.verifier.degree machine.verifier.logPower)))))

structure RefuterRequest where
  inputArity : ℕ
  machineDescription : ℕ
  boundValue : ℕ

def RefuterRequest.length (request : RefuterRequest) : ℕ :=
  request.inputArity

def RefuterRequest.code (request : RefuterRequest) : ℕ :=
  Nat.pair request.machineDescription request.inputArity

def RefuterRequest.measure (request : RefuterRequest) : ℕ :=
  request.boundValue

structure ExecutableSATOracleRefuter (hierarchy : Language)
    (bound : ℕ → ℕ) where
  runner : PolynomialNatProgram RefuterRequest
    RefuterRequest.length RefuterRequest.code RefuterRequest.measure

def ExecutableSATOracleRefuter.request {hierarchy : Language}
    {bound : ℕ → ℕ} (_refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) :
    RefuterRequest :=
  ⟨n, machine.description, bound n⟩

def ExecutableSATOracleRefuter.budget {hierarchy : Language}
    {bound : ℕ → ℕ} (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (n : ℕ) : ℕ :=
  refuter.runner.budget
    (⟨n, 0, bound n⟩ : RefuterRequest)

def ExecutableSATOracleRefuter.outputCode {hierarchy : Language}
    {bound : ℕ → ℕ} (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  refuter.runner.execute (refuter.request machine n)

def ExecutableSATOracleRefuter.output {hierarchy : Language}
    {bound : ℕ → ℕ} (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : BitInput n :=
  fun index => (refuter.outputCode machine n).testBit index.val

/-- The refuter's hierarchy is supplied with the actual timed machine consumed
by the projection-PCP theorem.  Making the language definitionally equal to
that machine's acceptance function prevents a caller from attaching a
fabricated step counter to an arbitrary language. -/
structure ExecutableRefuterSource (bound : ℕ → ℕ) where
  hierarchyMachine : TimedDecisionMachine
  hierarchySteps :
    ∀ n input, hierarchyMachine.steps n input ≤ bound n
  refuter : ExecutableSATOracleRefuter hierarchyMachine.accepts bound
  sound : ∀ machine : ExecutableWeakNondeterministicMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine n) ↔
        hierarchyMachine.accepts n (refuter.output machine n) = false)

def ExecutableRefuterContract : Prop :=
  ∀ (bound : ℕ → ℕ), RefuterClockAdmissible bound →
    Nonempty (ExecutableRefuterSource bound)

def ExecutableRefuterAndXorContract : Prop :=
  ExecutableRefuterContract ∧ XorContract

/-! ## Worst-case amplification with an executable constructor and evaluator -/

def AmplifierRequest.length (request : AmplifierRequest) : ℕ :=
  request.inputArity

def AmplifierRequest.code (request : AmplifierRequest) : ℕ :=
  Nat.pair request.inputArity (encodeBoolFunction request.function)

def AmplifierRequest.measure (request : AmplifierRequest) : ℕ :=
  request.inputArity

structure AmplifierEvaluationRequest where
  outputArity : ℕ
  descriptor : ℕ
  input : BitInput outputArity

def AmplifierEvaluationRequest.length
    (request : AmplifierEvaluationRequest) : ℕ :=
  request.outputArity

def AmplifierEvaluationRequest.code
    (request : AmplifierEvaluationRequest) : ℕ :=
  Nat.pair request.descriptor (encodeBitInput request.input)

def AmplifierEvaluationRequest.measure
    (request : AmplifierEvaluationRequest) : ℕ :=
  request.outputArity

/-- The construction program returns `(outputArity, descriptor)`.  The second
program evaluates that descriptor, so the amplified truth table is not stored
as an arbitrary Lean function. -/
structure ExecutableWorstCaseAmplifierAlgorithm where
  construction : ExponentialNatProgram AmplifierRequest
    AmplifierRequest.length AmplifierRequest.code AmplifierRequest.measure
  constructionOracleFree : OracleFree construction.program
  evaluator : PolynomialNatProgram AmplifierEvaluationRequest
    AmplifierEvaluationRequest.length AmplifierEvaluationRequest.code
    AmplifierEvaluationRequest.measure
  evaluatorOracleFree : OracleFree evaluator.program

def ExecutableWorstCaseAmplifierAlgorithm.constructionCode
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  algorithm.construction.execute request

def ExecutableWorstCaseAmplifierAlgorithm.outputArity
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  (Nat.unpair (algorithm.constructionCode request)).1

def ExecutableWorstCaseAmplifierAlgorithm.descriptor
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  (Nat.unpair (algorithm.constructionCode request)).2

def ExecutableWorstCaseAmplifierAlgorithm.evaluatorBudget
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  algorithm.evaluator.budget
    { outputArity := algorithm.outputArity request
      descriptor := algorithm.descriptor request
      input := fun _ => false }

def ExecutableWorstCaseAmplifierAlgorithm.outputFunction
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) :
    BoolFunction (algorithm.outputArity request) :=
  fun input =>
    let evaluationRequest : AmplifierEvaluationRequest :=
      ⟨algorithm.outputArity request, algorithm.descriptor request, input⟩
    let outputCode := algorithm.evaluator.execute evaluationRequest
    outputCode != 0

def ExecutableWorstCaseAmplifierAlgorithm.amplify
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (n : ℕ) (function : BoolFunction n) : AmplifiedTruthTable n :=
  let request : AmplifierRequest := ⟨n, function⟩
  { outputArity := algorithm.outputArity request
    function := algorithm.outputFunction request
    constructionSteps := algorithm.construction.budget request }

def ExecutableWorstCaseAmplifierAlgorithm.toSemantic
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm) :
    WorstCaseAmplifierAlgorithm where
  amplify := algorithm.amplify

@[simp] theorem ExecutableWorstCaseAmplifierAlgorithm.constructionSteps_eq
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (n : ℕ) (function : BoolFunction n) :
    (algorithm.amplify n function).constructionSteps =
      2 ^ (algorithm.construction.exponent * n) := by
  rfl

def ExecutableWorstCaseAmplifierContract : Prop :=
  ∃ algorithm : ExecutableWorstCaseAmplifierAlgorithm,
    ∃ stvExponent arityCoefficient : ℕ,
    1 ≤ stvExponent ∧ 1 ≤ arityCoefficient ∧
    ∀ (sizeBound : ℕ → ℕ), TimeConstructible sizeBound →
    ∀ (n : ℕ) (function : BoolFunction n),
      WorstCaseHardAt function (sizeBound n) →
      let output := algorithm.amplify n function
      output.outputArity ≤ arityCoefficient * n ∧
        (∀ circuit : BooleanCircuit output.outputArity,
          circuit.size ≤ integerFloorRoot stvExponent (sizeBound n) →
          agreement circuit.eval output.function ≤
            1 / 2 + Real.rpow (sizeBound n : ℝ) (-(1 : ℝ) / stvExponent))

theorem executableWorstCaseAmplifier_implies_semantic :
    ExecutableWorstCaseAmplifierContract → WorstCaseAmplifierContract := by
  intro contract
  obtain ⟨algorithm, stvExponent, arityCoefficient, hstv, harity, contract⟩ :=
    contract
  refine ⟨algorithm.toSemantic, stvExponent, arityCoefficient,
    algorithm.construction.exponent, hstv, harity, ?_⟩
  intro sizeBound constructible n function hhard
  have hproperties := contract sizeBound constructible n function hhard
  exact ⟨hproperties.1, hproperties.2,
    algorithm.constructionSteps_eq n function ▸ le_rfl⟩

end NearCubicWires.ExecutableInterfaces
