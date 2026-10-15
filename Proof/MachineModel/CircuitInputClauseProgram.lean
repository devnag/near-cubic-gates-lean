import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Fixed circuit-input Tseitin clause emitter

Structural compilers should emit ordinary gate records, not duplicate CNF
templates throughout every loop.  This module is the single executable bridge
from one topological Boolean-DAG node to the exact forward raw triples used by
`StructuralClauseStreamProgram`.

The request contains the already shifted variable of the current gate and a
small structural node tag.  Child gate variables are shifted by the caller;
input-node sources remain free-input variables.  This convention avoids a
second arithmetic path in the emitter while exactly matching
`circuitInputNodeClauses`.
-/

namespace NearCubicWires.CircuitInputClauseProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF

def rawCircuitNodeCode {n : ℕ} : BooleanNode n → ℕ
  | .const value => Nat.pair 0 value.toNat
  | .input source => Nat.pair 1 source.val
  | .not child => Nat.pair 2 (n + child)
  | .and left right => Nat.pair 3 (Nat.pair (n + left) (n + right))
  | .or left right => Nat.pair 4 (Nat.pair (n + left) (n + right))

def circuitInputClauseRequest {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : ℕ :=
  Nat.pair (circuitInputGateVariable n index) (rawCircuitNodeCode node)

/-- Register ABI:

* `r0`: request, then the forward raw-clause stream;
* `r2`: current absolute gate variable;
* `r4`/`r5`: structural tag and payload;
* `r8`--`r17`: positive/negative literal codes;
* `r23`--`r31`: normalized three-clause template.

The five node cases join three shared list constructors.  No branch selects a
host function and no instruction has gate- or recovery-specific semantics.
-/
def circuitInputClauseProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 1 5
  , .set 7 0 6
  , .pair 6 2 8 7
  , .pair 7 2 9 8
  , .pair 6 5 10 9
  , .pair 7 5 11 10
  , .unpairLeft 5 12 11
  , .unpairRight 5 13 12
  , .pair 6 12 14 13
  , .pair 7 12 15 14
  , .pair 6 13 16 15
  , .pair 7 13 17 16
  , .copy 4 22 17
  , .branchZero 22 25 18
  , .decrement 22 19
  , .branchZero 22 28 20
  , .decrement 22 21
  , .branchZero 22 30 22
  , .decrement 22 23
  , .branchZero 22 32 24
  , .branchZero 7 41 41
    -- Constant case: select one literal, then use the unit builder.
  , .branchZero 5 26 27
  , .copy 9 23 50
  , .copy 8 23 50
    -- Input and negation normalize into the same two-clause builder.
  , .copy 10 23 29
  , .copy 11 24 56
  , .copy 11 23 31
  , .copy 10 24 56
    -- Conjunction template.
  , .copy 9 23 33
  , .copy 14 24 34
  , .copy 14 25 35
  , .copy 9 26 36
  , .copy 16 27 37
  , .copy 16 28 38
  , .copy 8 29 39
  , .copy 15 30 40
  , .copy 17 31 66
    -- Disjunction template.
  , .copy 8 23 42
  , .copy 15 24 43
  , .copy 15 25 44
  , .copy 8 26 45
  , .copy 17 27 46
  , .copy 17 28 47
  , .copy 9 29 48
  , .copy 14 30 49
  , .copy 16 31 66
    -- One-clause forward tagged list.
  , .pair 23 23 18 51
  , .pair 23 18 19 52
  , .set 20 0 53
  , .pair 19 20 20 54
  , .pair 6 20 0 55
  , .halt 0
    -- Two-clause forward tagged list, built from the tail.
  , .pair 24 24 18 57
  , .pair 8 18 19 58
  , .set 20 0 59
  , .pair 19 20 20 60
  , .pair 6 20 21 61
  , .pair 23 23 18 62
  , .pair 9 18 19 63
  , .pair 19 21 20 64
  , .pair 6 20 0 65
  , .halt 0
    -- Three-clause forward tagged list, built from the tail.
  , .set 20 0 67
  , .pair 30 31 18 68
  , .pair 29 18 19 69
  , .pair 19 20 20 70
  , .pair 6 20 21 71
  , .pair 27 28 18 72
  , .pair 26 18 19 73
  , .pair 19 21 20 74
  , .pair 6 20 21 75
  , .pair 24 25 18 76
  , .pair 23 18 19 77
  , .pair 19 21 20 78
  , .pair 6 20 0 79
  , .halt 0
  ]

@[simp] theorem circuitInputClauseProgram_length :
    circuitInputClauseProgram.length = 80 := by
  rfl

theorem circuitInputClauseProgram_oracleFree :
    OracleFree circuitInputClauseProgram := by
  rfl

def circuitInputClauseFuel : ℕ := 48

private def rawClauseConstructionValues : EncodedCNF → List ℕ
  | [] => [0]
  | clause :: rest =>
      let rawClause := rawEncodedClause clause
      let tail := rawClauseStream rest
      let payload := Nat.pair rawClause tail
      let stream := Nat.pair 1 payload
      let literals :=
        match clause with
        | [first, second, third] =>
            let firstCode := Encodable.encode first
            let secondCode := Encodable.encode second
            let thirdCode := Encodable.encode third
            [ firstCode, secondCode, thirdCode
            , Nat.pair secondCode thirdCode
            , rawClause
            ]
        | _ => [0]
      literals ++ [tail, payload, stream] ++
        rawClauseConstructionValues rest

private def circuitInputClauseWorkingValues {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : List ℕ :=
  let request := circuitInputClauseRequest index node
  let formula := circuitInputNodeClauses index node
  let output := rawClauseStream formula
  let nodeCode := rawCircuitNodeCode node
  let current := circuitInputGateVariable n index
  let tag := (Nat.unpair nodeCode).1
  let payload := (Nat.unpair nodeCode).2
  let left := (Nat.unpair payload).1
  let right := (Nat.unpair payload).2
  let literals :=
    [ Nat.pair 1 current, Nat.pair 0 current
    , Nat.pair 1 payload, Nat.pair 0 payload
    , Nat.pair 1 left, Nat.pair 0 left
    , Nat.pair 1 right, Nat.pair 0 right
    ]
  [ request, output, nodeCode, current, tag, payload, left, right
  , tag.pred, tag.pred.pred, tag.pred.pred.pred, 1, 0
  ] ++ literals ++ rawClauseConstructionValues formula

private def circuitInputClauseWorkBound {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : ℕ :=
  (circuitInputClauseWorkingValues index node).foldr max 0

def circuitInputClauseMaximumBits {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : ℕ :=
  natBitLength (circuitInputClauseWorkBound index node)

private theorem member_le_foldr_max {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr_cons]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem workingValue_fits {n : ℕ}
    (index : ℕ) (node : BooleanNode n) {value : ℕ}
    (hmem : value ∈ circuitInputClauseWorkingValues index node) :
    natBitLength value ≤ circuitInputClauseMaximumBits index node := by
  unfold circuitInputClauseMaximumBits circuitInputClauseWorkBound
  exact PolynomialClock.natBitLength_mono (member_le_foldr_max hmem)

private def circuitInputClausePreludeState {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : NPOracleState :=
  let initial :=
    initialNPOracleState n (circuitInputClauseRequest index node)
  let current := circuitInputGateVariable n index
  let nodeCode := rawCircuitNodeCode node
  let tag := (Nat.unpair nodeCode).1
  let payload := (Nat.unpair nodeCode).2
  let left := (Nat.unpair payload).1
  let right := (Nat.unpair payload).2
  let state1 := (initial.write 2 current).jump 1
  let state2 := (state1.write 3 nodeCode).jump 2
  let state3 := (state2.write 4 tag).jump 3
  let state4 := (state3.write 5 payload).jump 4
  let state5 := (state4.write 6 1).jump 5
  let state6 := (state5.write 7 0).jump 6
  let state7 := (state6.write 8 (Nat.pair 1 current)).jump 7
  let state8 := (state7.write 9 (Nat.pair 0 current)).jump 8
  let state9 := (state8.write 10 (Nat.pair 1 payload)).jump 9
  let state10 := (state9.write 11 (Nat.pair 0 payload)).jump 10
  let state11 := (state10.write 12 left).jump 11
  let state12 := (state11.write 13 right).jump 12
  let state13 := (state12.write 14 (Nat.pair 1 left)).jump 13
  let state14 := (state13.write 15 (Nat.pair 0 left)).jump 14
  let state15 := (state14.write 16 (Nat.pair 1 right)).jump 15
  let state16 := (state15.write 17 (Nat.pair 0 right)).jump 16
  (state16.write 22 tag).jump 17

private theorem run_circuitInputClausePrelude {n : ℕ}
    (index : ℕ) (node : BooleanNode n) (extraFuel : ℕ) :
    runNPOracleProgram circuitInputClauseProgram
        (circuitInputClauseMaximumBits index node)
        (extraFuel + 17)
        (initialNPOracleState n (circuitInputClauseRequest index node)) =
      runNPOracleProgram circuitInputClauseProgram
        (circuitInputClauseMaximumBits index node) extraFuel
        (circuitInputClausePreludeState index node) := by
  have fits :
      ∀ {value : ℕ},
        value ∈ circuitInputClauseWorkingValues index node →
          natBitLength value ≤
            circuitInputClauseMaximumBits index node :=
    fun {value} hmem => workingValue_fits index node hmem
  rw [show extraFuel + 17 = (extraFuel + 16) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (fuel := extraFuel + 16)
    (value := circuitInputGateVariable n index) (by rfl) rfl
    (by simp [circuitInputClauseRequest, initialNPOracleState])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 16 = (extraFuel + 15) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (fuel := extraFuel + 15) (value := rawCircuitNodeCode node)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, initialNPOracleState,
      NPOracleState.write, NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 15 = (extraFuel + 14) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (fuel := extraFuel + 14)
    (value := (Nat.unpair (rawCircuitNodeCode node)).1)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 14 = (extraFuel + 13) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (fuel := extraFuel + 13)
    (value := (Nat.unpair (rawCircuitNodeCode node)).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 13 = (extraFuel + 12) + 1 by omega]
  rw [CanonicalBinaryProgram.run_set_instruction
    (fuel := extraFuel + 12) (by rfl) rfl
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 12 = (extraFuel + 11) + 1 by omega]
  rw [CanonicalBinaryProgram.run_set_instruction
    (fuel := extraFuel + 11) (by rfl) rfl
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 11 = (extraFuel + 10) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 10)
    (value := Nat.pair 1 (circuitInputGateVariable n index))
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 10 = (extraFuel + 9) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 9)
    (value := Nat.pair 0 (circuitInputGateVariable n index))
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 9 = (extraFuel + 8) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 8)
    (value := Nat.pair 1
      (Nat.unpair (rawCircuitNodeCode node)).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 8 = (extraFuel + 7) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 7)
    (value := Nat.pair 0
      (Nat.unpair (rawCircuitNodeCode node)).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 7 = (extraFuel + 6) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (fuel := extraFuel + 6)
    (value :=
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).1)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 6 = (extraFuel + 5) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (fuel := extraFuel + 5)
    (value :=
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 5 = (extraFuel + 4) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 4)
    (value := Nat.pair 1
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).1)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 4 = (extraFuel + 3) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 3)
    (value := Nat.pair 0
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).1)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 3 = (extraFuel + 2) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 2)
    (value := Nat.pair 1
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 2 = (extraFuel + 1) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (fuel := extraFuel + 1)
    (value := Nat.pair 0
      (Nat.unpair (Nat.unpair (rawCircuitNodeCode node)).2).2)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rw [show extraFuel + 1 = extraFuel + 1 by rfl]
  rw [CanonicalBinaryProgram.run_copy_instruction
    (fuel := extraFuel)
    (value := (Nat.unpair (rawCircuitNodeCode node)).1)
    (by rfl) rfl
    (by simp [circuitInputClauseRequest, NPOracleState.write,
      NPOracleState.jump])
    (fits (by simp [circuitInputClauseWorkingValues]))]
  rfl

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
-- The five exact symbolic traces normalize deeply nested state writes.
/-- Exact gate-template theorem.  The fixed program emits the same forward
literal triples as `circuitInputNodeClauses`; the next linked stage is therefore
the repository's sole canonical-list builder. -/
theorem run_circuitInputClauseProgram {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    runNPOracleProgram circuitInputClauseProgram
        (circuitInputClauseMaximumBits index node)
        circuitInputClauseFuel
        (initialNPOracleState n (circuitInputClauseRequest index node)) =
      some (rawClauseStream (circuitInputNodeClauses index node)) := by
  rw [show circuitInputClauseFuel = 31 + 17 by
    simp [circuitInputClauseFuel]]
  rw [run_circuitInputClausePrelude index node 31]
  cases node with
  | const value =>
      cases value <;>
        simp (config := { maxSteps := 300000 })
          [circuitInputClauseProgram, circuitInputClausePreludeState,
          circuitInputClauseRequest, rawCircuitNodeCode,
          NPOracleState.boundedWrite,
          runNPOracleProgram, initialNPOracleState,
          circuitInputNodeClauses, rawClauseStream, rawEncodedClause,
          rawClauseCode, positiveUnit, negativeUnit, triple,
          positive, negative, gateVariable, encodeTaggedList,
          workingValue_fits, circuitInputClauseWorkingValues,
          rawClauseConstructionValues]
  | input source =>
      simp (config := { maxSteps := 300000 })
        [circuitInputClauseProgram, circuitInputClausePreludeState,
        circuitInputClauseRequest, rawCircuitNodeCode,
        NPOracleState.boundedWrite,
        runNPOracleProgram, initialNPOracleState,
        circuitInputNodeClauses, rawClauseStream, rawEncodedClause,
        rawClauseCode, triple, positive, negative, encodeTaggedList,
        gateVariable,
        workingValue_fits, circuitInputClauseWorkingValues,
        rawClauseConstructionValues]
  | not child =>
      simp (config := { maxSteps := 300000 })
        [circuitInputClauseProgram, circuitInputClausePreludeState,
        circuitInputClauseRequest, rawCircuitNodeCode,
        NPOracleState.boundedWrite,
        runNPOracleProgram, initialNPOracleState,
        circuitInputNodeClauses, rawClauseStream, rawEncodedClause,
        rawClauseCode, triple, positive, negative, encodeTaggedList,
        gateVariable,
        workingValue_fits, circuitInputClauseWorkingValues,
        rawClauseConstructionValues]
  | and left right =>
      simp (config := { maxSteps := 300000 })
        [circuitInputClauseProgram, circuitInputClausePreludeState,
        circuitInputClauseRequest, rawCircuitNodeCode,
        NPOracleState.boundedWrite,
        runNPOracleProgram, initialNPOracleState,
        circuitInputNodeClauses, rawClauseStream, rawEncodedClause,
        rawClauseCode, triple, positive, negative, encodeTaggedList,
        gateVariable,
        workingValue_fits, circuitInputClauseWorkingValues,
        rawClauseConstructionValues]
  | or left right =>
      simp (config := { maxSteps := 300000 })
        [circuitInputClauseProgram, circuitInputClausePreludeState,
        circuitInputClauseRequest, rawCircuitNodeCode,
        NPOracleState.boundedWrite,
        runNPOracleProgram, initialNPOracleState,
        circuitInputNodeClauses, rawClauseStream, rawEncodedClause,
        rawClauseCode, triple, positive, negative, encodeTaggedList,
        gateVariable,
        workingValue_fits, circuitInputClauseWorkingValues,
        rawClauseConstructionValues]

end NearCubicWires.CircuitInputClauseProgram
