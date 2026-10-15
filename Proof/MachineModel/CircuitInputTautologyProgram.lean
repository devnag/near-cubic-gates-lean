import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Fixed emitter for free-input tautology clauses

`circuitInputFormula` begins with one three-literal tautology for each free
input variable.  This fixed program emits that exact raw clause from only its
variable index, completing the non-gate structural template needed by the
recovery controller.
-/

namespace NearCubicWires.CircuitInputTautologyProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF

/-- The request is the free-input variable index itself. -/
def circuitInputTautologyProgram : NPOracleProgram :=
  [ .set 2 1 1
  , .set 3 0 2
  , .pair 2 0 4 3
  , .pair 3 0 5 4
  , .pair 5 4 6 5
  , .pair 4 6 7 6
  , .pair 7 3 8 7
  , .pair 2 8 0 8
  , .halt 0
  ]

@[simp] theorem circuitInputTautologyProgram_length :
    circuitInputTautologyProgram.length = 9 := by
  rfl

theorem circuitInputTautologyProgram_oracleFree :
    OracleFree circuitInputTautologyProgram := by
  rfl

def circuitInputTautologyFuel : ℕ := 9

private def circuitInputTautologyWorkingValues (index : ℕ) : List ℕ :=
  let positiveCode := Nat.pair 1 index
  let negativeCode := Nat.pair 0 index
  let literalTail := Nat.pair negativeCode positiveCode
  let rawClause := Nat.pair positiveCode literalTail
  let streamPayload := Nat.pair rawClause 0
  let output := Nat.pair 1 streamPayload
  [index, 0, 1, positiveCode, negativeCode, literalTail, rawClause,
    streamPayload, output]

private def circuitInputTautologyWorkBound (index : ℕ) : ℕ :=
  (circuitInputTautologyWorkingValues index).foldr max 0

def circuitInputTautologyMaximumBits (index : ℕ) : ℕ :=
  natBitLength (circuitInputTautologyWorkBound index)

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr_cons]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem workingValue_fits (index : ℕ) {value : ℕ}
    (hmem : value ∈ circuitInputTautologyWorkingValues index) :
    natBitLength value ≤ circuitInputTautologyMaximumBits index := by
  unfold circuitInputTautologyMaximumBits
    circuitInputTautologyWorkBound
  exact PolynomialClock.natBitLength_mono (member_le_foldr_max hmem)

/-- Exact raw stream for the `index`th input tautology. -/
theorem run_circuitInputTautologyProgram
    (inputLength index : ℕ) :
    runNPOracleProgram circuitInputTautologyProgram
        (circuitInputTautologyMaximumBits index)
        circuitInputTautologyFuel
        (initialNPOracleState inputLength index) =
      some (rawClauseStream [circuitInputTautology index]) := by
  simp (config := { maxSteps := 100000 })
    [circuitInputTautologyProgram, circuitInputTautologyFuel,
    runNPOracleProgram, initialNPOracleState,
    NPOracleState.boundedWrite, circuitInputTautology,
    rawClauseStream, rawEncodedClause, rawClauseCode, triple,
    positive, negative, encodeTaggedList, workingValue_fits,
    circuitInputTautologyWorkingValues]

end NearCubicWires.CircuitInputTautologyProgram
