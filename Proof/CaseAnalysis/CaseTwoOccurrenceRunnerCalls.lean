import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceEvaluation

/-!
# The four factory runner calls of one Case-2 occurrence

`CaseTwoOccurrenceEvaluation` reduces one honest occurrence value to four
`PolynomialNatProgram.execute` calls on the published factory.  This module
makes each of them an actual interpreter run of the single canonical
native-input caller: the callee is the factory's own program, selected at link
time, and the request is data on the caller's input.

Every theorem below is an exact run at explicitly charged width and fuel, so
the remaining Case-2 evaluator has to route request codes only, never
programs.
-/

namespace NearCubicWires.CaseTwoOccurrenceRunnerCalls

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## 1. Shape -/

def shapeCallProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  nativeCallProgram factory.shapeRunner.program

theorem shapeCallProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (shapeCallProgram factory) :=
  nativeCallProgram_oracleFree factory.shapeOracleFree

def shapeCallFuel (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  nativeCallFuel factory.shapeRunner.program
    (factory.shapeRunner.budget (factory.shapeRequest circuit))
    n (encodeBooleanCircuit circuit)

def shapeCallBits (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  nativeCallBits outerInputLength n (encodeBooleanCircuit circuit)
    (occurrenceShapeCode factory circuit)
    (factory.shapeRunner.budget (factory.shapeRequest circuit))

theorem run_shapeCallProgram (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n) :
    runNPOracleProgram (shapeCallProgram factory)
        (shapeCallBits factory outerInputLength circuit)
        (shapeCallFuel factory circuit)
        (initialNPOracleState outerInputLength
          (nativeInputRequest n (encodeBooleanCircuit circuit))) =
      some (occurrenceShapeCode factory circuit) := by
  apply run_nativeCallProgram
  exact factory.shapeRunner.run_eq_execute (factory.shapeRequest circuit)

/-! ## 2. Systematic support -/

def supportRequest {n : ℕ} (circuit : BooleanCircuit n) (index : ℕ) :
    PointwiseSupportRequest :=
  ⟨n, circuit.size, encodeBooleanCircuit circuit, index⟩

def supportRequestCode {n : ℕ} (circuit : BooleanCircuit n) (index : ℕ) :
    ℕ :=
  Nat.pair (encodeBooleanCircuit circuit) index

def supportCallProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  nativeCallProgram factory.supportRunner.program

theorem supportCallProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (supportCallProgram factory) :=
  nativeCallProgram_oracleFree factory.supportOracleFree

def supportCallFuel (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (index : ℕ) : ℕ :=
  nativeCallFuel factory.supportRunner.program
    (factory.supportRunner.budget (supportRequest circuit index))
    n (supportRequestCode circuit index)

def supportCallBits (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (index : ℕ) : ℕ :=
  nativeCallBits outerInputLength n (supportRequestCode circuit index)
    (occurrenceSupportCode factory circuit index)
    (factory.supportRunner.budget (supportRequest circuit index))

theorem run_supportCallProgram (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (index : ℕ) :
    runNPOracleProgram (supportCallProgram factory)
        (supportCallBits factory outerInputLength circuit index)
        (supportCallFuel factory circuit index)
        (initialNPOracleState outerInputLength
          (nativeInputRequest n (supportRequestCode circuit index))) =
      some (occurrenceSupportCode factory circuit index) := by
  apply run_nativeCallProgram
  exact factory.supportRunner.run_eq_execute (supportRequest circuit index)

/-! ## 3. Clause -/

def clauseRequest (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (address : ℕ) :
    PointwiseClauseRequest :=
  ⟨n, circuit.size, encodeBooleanCircuit circuit,
    (factory.forCircuit circuit).systematicBits +
      (factory.forCircuit circuit).auxiliaryBits,
    address⟩

def clauseRequestCode {n : ℕ} (circuit : BooleanCircuit n) (address : ℕ) :
    ℕ :=
  Nat.pair (encodeBooleanCircuit circuit) address

def clauseCallProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  nativeCallProgram factory.clauseRunner.program

theorem clauseCallProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (clauseCallProgram factory) :=
  nativeCallProgram_oracleFree factory.clauseOracleFree

def clauseCallFuel (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (address : ℕ) : ℕ :=
  nativeCallFuel factory.clauseRunner.program
    (factory.clauseRunner.budget (clauseRequest factory circuit address))
    n (clauseRequestCode circuit address)

def clauseCallBits (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (address : ℕ) : ℕ :=
  nativeCallBits outerInputLength n (clauseRequestCode circuit address)
    (occurrenceClauseCode factory circuit address)
    (factory.clauseRunner.budget (clauseRequest factory circuit address))

theorem run_clauseCallProgram (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (address : ℕ) :
    runNPOracleProgram (clauseCallProgram factory)
        (clauseCallBits factory outerInputLength circuit address)
        (clauseCallFuel factory circuit address)
        (initialNPOracleState outerInputLength
          (nativeInputRequest n (clauseRequestCode circuit address))) =
      some (occurrenceClauseCode factory circuit address) := by
  apply run_nativeCallProgram
  exact factory.clauseRunner.run_eq_execute
    (clauseRequest factory circuit address)

/-! ## 4. Honest auxiliary word -/

def honestRequest {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) :
    PointwiseHonestRequest :=
  ⟨n, circuit.size, encodeBooleanCircuit circuit,
    bitInputPrefixView n inputCode⟩

def honestRequestCode {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  Nat.pair (encodeBooleanCircuit circuit) (bitInputPrefix n inputCode)

/-- The honest request code is computable from the public input code: the
encoded PCPP input is exactly its low digit window. -/
theorem honestRequest_code_eq {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) :
    PointwiseHonestRequest.code (honestRequest circuit inputCode) =
      honestRequestCode circuit inputCode := by
  unfold PointwiseHonestRequest.code honestRequest honestRequestCode
  rw [← bitInputPrefix_eq_encodeView]

def honestCallProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  nativeCallProgram factory.honestRunner.program

theorem honestCallProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (honestCallProgram factory) :=
  nativeCallProgram_oracleFree factory.honestOracleFree

def honestCallFuel (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  nativeCallFuel factory.honestRunner.program
    (factory.honestRunner.budget (honestRequest circuit inputCode))
    n (honestRequestCode circuit inputCode)

def honestCallBits (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  nativeCallBits outerInputLength n (honestRequestCode circuit inputCode)
    (occurrenceHonestCode factory circuit
      (bitInputPrefixView n inputCode))
    (factory.honestRunner.budget (honestRequest circuit inputCode))

theorem run_honestCallProgram (factory : ExecutablePointwisePCPPFactory)
    (outerInputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) :
    runNPOracleProgram (honestCallProgram factory)
        (honestCallBits factory outerInputLength circuit inputCode)
        (honestCallFuel factory circuit inputCode)
        (initialNPOracleState outerInputLength
          (nativeInputRequest n (honestRequestCode circuit inputCode))) =
      some
        (occurrenceHonestCode factory circuit
          (bitInputPrefixView n inputCode)) := by
  apply run_nativeCallProgram
  have hrun :=
    factory.honestRunner.run_eq_execute (honestRequest circuit inputCode)
  rw [honestRequest_code_eq] at hrun
  exact hrun

end NearCubicWires.CaseTwoOccurrenceRunnerCalls
