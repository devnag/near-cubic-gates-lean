import Proof.Circuits.CircuitInputCNF
import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.DynamicCNFBuilder

/-!
# Fixed structural-clause stream encoder

Structural circuit compilers naturally emit Tseitin clauses in forward order,
while `DynamicCNFBuilder` consumes canonical clause codes in reverse order.
This module provides the single fixed bridge between those representations.
Its input is only a tagged stream of raw three-literal tuples; the interpreter
constructs every canonical list cell and reverses the stream by accumulation.
-/

namespace NearCubicWires.StructuralClauseStreamProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TseitinCNF

/-- A raw clause contains exactly the three already-canonical literal codes.
The missing list tags are deliberately constructed by the fixed program. -/
def rawClauseCode (first second third : EncodedLiteral) : ℕ :=
  Nat.pair (Encodable.encode first)
    (Nat.pair (Encodable.encode second) (Encodable.encode third))

def rawEncodedClause : EncodedClause → ℕ
  | [first, second, third] => rawClauseCode first second third
  | _ => 0

def rawClauseStream (formula : EncodedCNF) : ℕ :=
  encodeTaggedList (formula.map rawEncodedClause)

def canonicalReverseClauseStream (formula : EncodedCNF) : ℕ :=
  encodeTaggedList ((formula.map Encodable.encode).reverse)

theorem encodeTaggedList_suffix_le
    (listPrefix suffix : List ℕ) :
    encodeTaggedList suffix ≤ encodeTaggedList (listPrefix ++ suffix) := by
  induction listPrefix with
  | nil =>
      rfl
  | cons value tail ih =>
      exact ih.trans (DynamicCNFBuilder.encodeTaggedList_tail_le
        value (tail ++ suffix))

/-- Register ABI:

* `r0`: forward raw-clause cursor;
* `r2`: reverse canonical-clause accumulator;
* `r3`--`r13`: structural scratch.

The loop contains no semantic operation and no SAT call. -/
def structuralClauseStreamProgram : NPOracleProgram :=
  [ .branchZero 0 19 1,
    .unpairRight 0 3 2,
    .unpairLeft 3 4 3,
    .unpairRight 3 0 4,
    .unpairLeft 4 7 5,
    .unpairRight 4 6 6,
    .unpairLeft 6 9 7,
    .unpairRight 6 10 8,
    .set 11 0 9,
    .pair 10 11 11 10,
    .increment 11 11,
    .pair 9 11 11 12,
    .increment 11 13,
    .pair 7 11 11 14,
    .increment 11 15,
    .pair 11 2 12 16,
    .set 13 1 17,
    .pair 13 12 2 18,
    .branchZero 13 0 0,
    .halt 2 ]

@[simp] theorem structuralClauseStreamProgram_length :
    structuralClauseStreamProgram.length = 20 := by
  rfl

theorem structuralClauseStreamProgram_oracleFree :
    OracleFree structuralClauseStreamProgram := by
  rfl

def structuralClauseStreamFuel (formula : EncodedCNF) : ℕ :=
  19 * formula.length + 2

private theorem rawEncodedClause_eq
    (first second third : EncodedLiteral) :
    rawEncodedClause [first, second, third] =
      rawClauseCode first second third := by
  rfl

private theorem encode_triple
    (first second third : EncodedLiteral) :
    Encodable.encode [first, second, third] =
      encodeCodeList
        [Encodable.encode first, Encodable.encode second,
          Encodable.encode third] := by
  symm
  exact encodeCodeList_map_encode [first, second, third]

private theorem boundedWrite_eq
    {maximumBits register value : ℕ} {state : NPOracleState}
    (hvalue : natBitLength value ≤ maximumBits) :
    state.boundedWrite maximumBits register value =
      some (state.write register value) := by
  simp [NPOracleState.boundedWrite, hvalue]

private def structuralClauseNextState
    (first second third : EncodedLiteral)
    (rest : List EncodedClause) (accumulator : List ℕ)
    (state : NPOracleState) : NPOracleState :=
  let rawTail := encodeTaggedList (rest.map rawEncodedClause)
  let rawClause := rawClauseCode first second third
  let payload := Nat.pair rawClause rawTail
  let firstCode := Encodable.encode first
  let secondCode := Encodable.encode second
  let thirdCode := Encodable.encode third
  let thirdList := encodeCodeList [thirdCode]
  let secondList := encodeCodeList [secondCode, thirdCode]
  let clauseCode := Encodable.encode [first, second, third]
  let oldStream := encodeTaggedList accumulator
  let streamPayload := Nat.pair clauseCode oldStream
  let newStream := encodeTaggedList (clauseCode :: accumulator)
  let state1 := (state.jump 1).write 3 payload |>.jump 2
  let state2 := state1.write 4 rawClause |>.jump 3
  let state3 := state2.write 0 rawTail |>.jump 4
  let state4 := state3.write 7 firstCode |>.jump 5
  let state5 :=
    state4.write 6 (Nat.pair secondCode thirdCode) |>.jump 6
  let state6 := state5.write 9 secondCode |>.jump 7
  let state7 := state6.write 10 thirdCode |>.jump 8
  let state8 := state7.write 11 0 |>.jump 9
  let state9 := state8.write 11 (Nat.pair thirdCode 0) |>.jump 10
  let state10 := state9.write 11 thirdList |>.jump 11
  let state11 :=
    state10.write 11 (Nat.pair secondCode thirdList) |>.jump 12
  let state12 := state11.write 11 secondList |>.jump 13
  let state13 :=
    state12.write 11 (Nat.pair firstCode secondList) |>.jump 14
  let state14 := state13.write 11 clauseCode |>.jump 15
  let state15 := state14.write 12 streamPayload |>.jump 16
  let state16 := state15.write 13 1 |>.jump 17
  let state17 := state16.write 2 newStream |>.jump 18
  state17.jump 0

private theorem run_iteration
    (first second third : EncodedLiteral)
    (rest : List EncodedClause) (accumulator : List ℕ)
    {maximumBits fuel sourceBound outputBound : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcursor :
      state.registers 0 =
        encodeTaggedList
          (rawClauseCode first second third ::
            rest.map rawEncodedClause))
    (haccumulator :
      state.registers 2 = encodeTaggedList accumulator)
    (hsource :
      encodeTaggedList
          (rawClauseCode first second third ::
            rest.map rawEncodedClause) ≤ sourceBound)
    (houtput :
      encodeTaggedList
          (Encodable.encode [first, second, third] :: accumulator) ≤
        outputBound)
    (hbits :
      natBitLength (max sourceBound outputBound) ≤ maximumBits) :
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 19) state =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state) := by
  let rawTail := encodeTaggedList (rest.map rawEncodedClause)
  let rawClause := rawClauseCode first second third
  let payload := Nat.pair rawClause rawTail
  let firstCode := Encodable.encode first
  let secondCode := Encodable.encode second
  let thirdCode := Encodable.encode third
  let thirdList := encodeCodeList [thirdCode]
  let secondList := encodeCodeList [secondCode, thirdCode]
  let clauseCode := Encodable.encode [first, second, third]
  let oldStream := encodeTaggedList accumulator
  let streamPayload := Nat.pair clauseCode oldStream
  let newStream := encodeTaggedList (clauseCode :: accumulator)
  have hclauseCodeEq :
      clauseCode = encodeCodeList [firstCode, secondCode, thirdCode] := by
    simpa [clauseCode, firstCode, secondCode, thirdCode] using
      encode_triple first second third
  have hclauseSucc :
      Nat.pair firstCode secondList + 1 = clauseCode := by
    rw [hclauseCodeEq]
    rfl
  have hsourceBits :
      ∀ value ≤ sourceBound, natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact (natBitLength_mono
      (hvalue.trans (Nat.le_max_left _ _))).trans hbits
  have houtputBits :
      ∀ value ≤ outputBound, natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact (natBitLength_mono
      (hvalue.trans (Nat.le_max_right _ _))).trans hbits
  have hpayloadLe : payload ≤ sourceBound := by
    apply le_trans (Nat.right_le_pair 1 payload)
    simpa only [encodeTaggedList, rawClause, rawTail, payload] using hsource
  have hrawClauseLe : rawClause ≤ sourceBound :=
    (Nat.left_le_pair rawClause rawTail).trans hpayloadLe
  have hrawTailLe : rawTail ≤ sourceBound :=
    (Nat.right_le_pair rawClause rawTail).trans hpayloadLe
  have hfirstCodeLe : firstCode ≤ sourceBound := by
    exact
      (Nat.left_le_pair firstCode (Nat.pair secondCode thirdCode)).trans
        hrawClauseLe
  have hsecondThirdLe :
      Nat.pair secondCode thirdCode ≤ sourceBound := by
    exact
      (Nat.right_le_pair firstCode (Nat.pair secondCode thirdCode)).trans
        hrawClauseLe
  have hsecondCodeLe : secondCode ≤ sourceBound :=
    (Nat.left_le_pair secondCode thirdCode).trans hsecondThirdLe
  have hthirdCodeLe : thirdCode ≤ sourceBound :=
    (Nat.right_le_pair secondCode thirdCode).trans hsecondThirdLe
  have hstreamPayloadLe : streamPayload ≤ outputBound := by
    apply le_trans (Nat.right_le_pair 1 streamPayload)
    simpa only [encodeTaggedList, clauseCode, oldStream, streamPayload,
      newStream] using houtput
  have hclauseCodeLe : clauseCode ≤ outputBound :=
    (Nat.left_le_pair clauseCode oldStream).trans hstreamPayloadLe
  have holdStreamLe : oldStream ≤ outputBound :=
    (Nat.right_le_pair clauseCode oldStream).trans hstreamPayloadLe
  have hnewStreamLe : newStream ≤ outputBound := by
    simpa only [newStream] using houtput
  have hthirdListLe : thirdList ≤ outputBound := by
    apply le_trans _ hclauseCodeLe
    rw [hclauseCodeEq]
    exact encodeCodeList_suffix_le
      [firstCode, secondCode] [thirdCode]
  have hsecondListLe : secondList ≤ outputBound := by
    apply le_trans _ hclauseCodeLe
    rw [hclauseCodeEq]
    exact encodeCodeList_suffix_le [firstCode] [secondCode, thirdCode]
  have hthirdPairLe :
      Nat.pair thirdCode 0 ≤ outputBound := by
    have : Nat.pair thirdCode 0 < thirdList := by
      simp only [thirdList, encodeCodeList]
      omega
    exact this.le.trans hthirdListLe
  have hsecondPairLe :
      Nat.pair secondCode thirdList ≤ outputBound := by
    have : Nat.pair secondCode thirdList < secondList := by
      simp only [secondList, thirdList, encodeCodeList]
      omega
    exact this.le.trans hsecondListLe
  have hfirstPairLe :
      Nat.pair firstCode secondList ≤ outputBound := by
    have hclause :
        clauseCode = Nat.pair firstCode secondList + 1 := by
      rw [hclauseCodeEq]
      rfl
    have : Nat.pair firstCode secondList < clauseCode := by omega
    exact this.le.trans hclauseCodeLe
  have honeLe : 1 ≤ outputBound := by
    have : 1 ≤ newStream := by
      simpa only [newStream, encodeTaggedList, streamPayload] using
        Nat.left_le_pair 1 streamPayload
    exact this.trans hnewStreamLe
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le _)).trans
      (houtputBits newStream hnewStreamLe)
  let state1 := state.jump 1
  let state2 := (state1.write 3 payload).jump 2
  let state3 := (state2.write 4 rawClause).jump 3
  let state4 := (state3.write 0 rawTail).jump 4
  let state5 := (state4.write 7 firstCode).jump 5
  let state6 :=
    (state5.write 6 (Nat.pair secondCode thirdCode)).jump 6
  let state7 := (state6.write 9 secondCode).jump 7
  let state8 := (state7.write 10 thirdCode).jump 8
  let state9 := (state8.write 11 0).jump 9
  let state10 := (state9.write 11 (Nat.pair thirdCode 0)).jump 10
  let state11 := (state10.write 11 thirdList).jump 11
  let state12 :=
    (state11.write 11 (Nat.pair secondCode thirdList)).jump 12
  let state13 := (state12.write 11 secondList).jump 13
  let state14 :=
    (state13.write 11 (Nat.pair firstCode secondList)).jump 14
  let state15 := (state14.write 11 clauseCode).jump 15
  let state16 := (state15.write 12 streamPayload).jump 16
  let state17 := (state16.write 13 1).jump 17
  let state18 := (state17.write 2 newStream).jump 18
  rw [show fuel + 19 = (fuel + 18) + 1 by omega]
  rw [CanonicalBinaryProgram.run_branchZero_instruction
    (program := structuralClauseStreamProgram)
    (pc := 0) (register := 0) (zeroTarget := 19)
    (nonzeroTarget := 1) (state := state)
    (by rfl) hpc]
  rw [hcursor]
  have hcursorNonzero :
      encodeTaggedList
          (rawClauseCode first second third ::
            rest.map rawEncodedClause) ≠ 0 := by
    have hpositive :
        0 <
          Nat.pair 1
            (Nat.pair (rawClauseCode first second third)
              (encodeTaggedList (rest.map rawEncodedClause))) :=
      lt_of_lt_of_le (by omega) <|
        Nat.left_le_pair 1
          (Nat.pair (rawClauseCode first second third)
            (encodeTaggedList (rest.map rawEncodedClause)))
    simpa only [encodeTaggedList] using hpositive.ne'
  rw [if_neg hcursorNonzero]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 18) state1 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 18 = (fuel + 17) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (program := structuralClauseStreamProgram)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := payload) (state := state1)
    (by rfl) (by rfl)
    (by simp [state1, hcursor, payload, rawClause, rawTail,
      encodeTaggedList])
    (hsourceBits payload hpayloadLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 17) state2 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 17 = (fuel + 16) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (program := structuralClauseStreamProgram)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := rawClause) (state := state2)
    (by rfl) (by rfl)
    (by simp [state2, state1, payload])
    (hsourceBits rawClause hrawClauseLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 16) state3 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 16 = (fuel + 15) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (program := structuralClauseStreamProgram)
    (pc := 3) (source := 3) (destination := 0) (next := 4)
    (value := rawTail) (state := state3)
    (by rfl) (by rfl)
    (by simp [state3, state2, state1, payload])
    (hsourceBits rawTail hrawTailLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 15) state4 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 15 = (fuel + 14) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (program := structuralClauseStreamProgram)
    (pc := 4) (source := 4) (destination := 7) (next := 5)
    (value := firstCode) (state := state4)
    (by rfl) (by rfl)
    (by simp [state4, state3, state2, state1, rawClause,
      rawClauseCode, firstCode])
    (hsourceBits firstCode hfirstCodeLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 14) state5 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 14 = (fuel + 13) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (program := structuralClauseStreamProgram)
    (pc := 5) (source := 4) (destination := 6) (next := 6)
    (value := Nat.pair secondCode thirdCode) (state := state5)
    (by rfl) (by rfl)
    (by simp [state5, state4, state3, state2, state1, rawClause,
      rawClauseCode, firstCode, secondCode, thirdCode])
    (hsourceBits (Nat.pair secondCode thirdCode) hsecondThirdLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 13) state6 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 13 = (fuel + 12) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairLeft_instruction
    (program := structuralClauseStreamProgram)
    (pc := 6) (source := 6) (destination := 9) (next := 7)
    (value := secondCode) (state := state6)
    (by rfl) (by rfl)
    (by simp [state6, state5, state4, state3, state2, state1])
    (hsourceBits secondCode hsecondCodeLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 12) state7 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 12 = (fuel + 11) + 1 by omega]
  rw [CanonicalBinaryProgram.run_unpairRight_instruction
    (program := structuralClauseStreamProgram)
    (pc := 7) (source := 6) (destination := 10) (next := 8)
    (value := thirdCode) (state := state7)
    (by rfl) (by rfl)
    (by simp [state7, state6, state5, state4, state3, state2, state1])
    (hsourceBits thirdCode hthirdCodeLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 11) state8 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 11 = (fuel + 10) + 1 by omega]
  rw [CanonicalBinaryProgram.run_set_instruction
    (program := structuralClauseStreamProgram)
    (pc := 8) (register := 11) (value := 0) (next := 9)
    (state := state8) (by rfl) (by rfl) hzeroBits]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 10) state9 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (program := structuralClauseStreamProgram)
    (pc := 9) (left := 10) (right := 11) (destination := 11)
    (next := 10) (value := Nat.pair thirdCode 0) (state := state9)
    (by rfl) (by rfl)
    (by simp [state9, state8, state7, state6, state5, state4, state3,
      state2, state1])
    (houtputBits (Nat.pair thirdCode 0) hthirdPairLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 9) state10 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [CanonicalBinaryProgram.run_increment_instruction
    (program := structuralClauseStreamProgram)
    (pc := 10) (register := 11) (next := 11)
    (value := thirdList) (state := state10)
    (by rfl) (by rfl)
    (by simp [state10, thirdList, encodeCodeList])
    (houtputBits thirdList hthirdListLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 8) state11 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (program := structuralClauseStreamProgram)
    (pc := 11) (left := 9) (right := 11) (destination := 11)
    (next := 12) (value := Nat.pair secondCode thirdList)
    (state := state11)
    (by rfl) (by rfl)
    (by simp [state11, state10, state9, state8, state7, state6, state5,
      state4, state3, state2, state1])
    (houtputBits (Nat.pair secondCode thirdList) hsecondPairLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 7) state12 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [CanonicalBinaryProgram.run_increment_instruction
    (program := structuralClauseStreamProgram)
    (pc := 12) (register := 11) (next := 13)
    (value := secondList) (state := state12)
    (by rfl) (by rfl)
    (by simp [state12, secondList, thirdList, encodeCodeList])
    (houtputBits secondList hsecondListLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 6) state13 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (program := structuralClauseStreamProgram)
    (pc := 13) (left := 7) (right := 11) (destination := 11)
    (next := 14) (value := Nat.pair firstCode secondList)
    (state := state13)
    (by rfl) (by rfl)
    (by simp [state13, state12, state11, state10, state9, state8, state7,
      state6, state5, state4, state3, state2, state1])
    (houtputBits (Nat.pair firstCode secondList) hfirstPairLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 5) state14 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [CanonicalBinaryProgram.run_increment_instruction
    (program := structuralClauseStreamProgram)
    (pc := 14) (register := 11) (next := 15)
    (value := clauseCode) (state := state14)
    (by rfl) (by rfl)
    (by
      simp only [state14, NPOracleState.jump, NPOracleState.write,
        if_pos]
      exact hclauseSucc)
    (houtputBits clauseCode hclauseCodeLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 4) state15 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (program := structuralClauseStreamProgram)
    (pc := 15) (left := 11) (right := 2) (destination := 12)
    (next := 16) (value := streamPayload) (state := state15)
    (by rfl) (by rfl)
    (by simp [state15, state14, state13, state12, state11, state10,
      state9, state8, state7, state6, state5, state4, state3, state2,
      state1, streamPayload, oldStream, haccumulator])
    (houtputBits streamPayload hstreamPayloadLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 3) state16 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [CanonicalBinaryProgram.run_set_instruction
    (program := structuralClauseStreamProgram)
    (pc := 16) (register := 13) (value := 1) (next := 17)
    (state := state16) (by rfl) (by rfl)
    (houtputBits 1 honeLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 2) state17 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [CanonicalBinaryProgram.run_pair_instruction
    (program := structuralClauseStreamProgram)
    (pc := 17) (left := 13) (right := 12) (destination := 2)
    (next := 18) (value := newStream) (state := state17)
    (by rfl) (by rfl)
    (by
      simp [state17, state16, state15, state14, state13, state12, state11,
        state10, state9, state8, state7, state6, state5, state4, state3,
        state2, state1]
      rfl)
    (houtputBits newStream hnewStreamLe)]
  change
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (fuel + 1) state18 =
      runNPOracleProgram structuralClauseStreamProgram maximumBits fuel
        (structuralClauseNextState first second third rest accumulator state)
  rw [CanonicalBinaryProgram.run_branchZero_instruction
    (program := structuralClauseStreamProgram)
    (pc := 18) (register := 13) (zeroTarget := 0)
    (nonzeroTarget := 0) (state := state18)
    (by rfl) (by rfl)]
  simp only [ite_self]
  congr 2

private theorem clause_eq_triple_of_length
    (clause : EncodedClause) (hlength : clause.length = 3) :
    ∃ first second third, clause = [first, second, third] := by
  cases clause with
  | nil =>
      simp at hlength
  | cons first tail =>
      cases tail with
      | nil =>
          simp at hlength
      | cons second tail =>
          cases tail with
          | nil =>
              simp at hlength
          | cons third tail =>
              cases tail with
              | nil =>
                  exact ⟨first, second, third, rfl⟩
              | cons fourth tail =>
                  simp at hlength

private theorem run_structuralClauseStream_from
    (formula : EncodedCNF) (accumulator : List ℕ)
    {maximumBits sourceBound outputBound : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcursor :
      state.registers 0 =
        encodeTaggedList (formula.map rawEncodedClause))
    (haccumulator :
      state.registers 2 = encodeTaggedList accumulator)
    (hthree :
      formula.all (fun clause => clause.length = 3) = true)
    (hsource :
      encodeTaggedList (formula.map rawEncodedClause) ≤ sourceBound)
    (houtput :
      encodeTaggedList
          ((formula.map Encodable.encode).reverse ++ accumulator) ≤
        outputBound)
    (hbits :
      natBitLength (max sourceBound outputBound) ≤ maximumBits) :
    runNPOracleProgram structuralClauseStreamProgram maximumBits
        (structuralClauseStreamFuel formula) state =
      some
        (encodeTaggedList
          ((formula.map Encodable.encode).reverse ++ accumulator)) := by
  induction formula generalizing accumulator state with
  | nil =>
      rw [show structuralClauseStreamFuel [] = 1 + 1 by rfl]
      rw [CanonicalBinaryProgram.run_branchZero_instruction
        (program := structuralClauseStreamProgram)
        (pc := 0) (register := 0) (zeroTarget := 19)
        (nonzeroTarget := 1) (state := state)
        (by rfl) hpc]
      rw [hcursor]
      simp only [List.map_nil, encodeTaggedList, if_pos]
      have haccumulatorLe :
          encodeTaggedList accumulator ≤ outputBound := by
        simpa only [List.map_nil, List.reverse_nil, List.nil_append] using
          houtput
      have haccumulatorBits :
          natBitLength (encodeTaggedList accumulator) ≤ maximumBits := by
        exact
          (natBitLength_mono
            (haccumulatorLe.trans (Nat.le_max_right _ _))).trans hbits
      rw [CanonicalBinaryProgram.run_halt_instruction
        (program := structuralClauseStreamProgram)
        (pc := 19) (outputRegister := 2)
        (value := encodeTaggedList accumulator) (state := state.jump 19)
        (by rfl) (by rfl)
        (by simpa [NPOracleState.jump] using haccumulator)
        haccumulatorBits]
      simp
  | cons clause rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hthree
      rcases hthree with ⟨hclauseLength, hrestThree⟩
      have hclauseLength' : clause.length = 3 :=
        of_decide_eq_true hclauseLength
      rcases clause_eq_triple_of_length clause hclauseLength' with
        ⟨first, second, third, rfl⟩
      let clauseCode := Encodable.encode [first, second, third]
      let nextAccumulator := clauseCode :: accumulator
      have hsourceTail :
          encodeTaggedList (rest.map rawEncodedClause) ≤ sourceBound := by
        exact
          (encodeTaggedList_tail_le
            (rawClauseCode first second third)
            (rest.map rawEncodedClause)).trans <| by
              simpa only [List.map_cons, rawEncodedClause_eq] using hsource
      have houtputNext :
          encodeTaggedList
              ((rest.map Encodable.encode).reverse ++ nextAccumulator) ≤
            outputBound := by
        simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append, nextAccumulator, clauseCode] using houtput
      have hiterationOutput :
          encodeTaggedList (clauseCode :: accumulator) ≤ outputBound := by
        exact (encodeTaggedList_suffix_le
          (rest.map Encodable.encode).reverse
          nextAccumulator).trans houtputNext
      rw [show
        structuralClauseStreamFuel ([first, second, third] :: rest) =
          structuralClauseStreamFuel rest + 19 by
            simp [structuralClauseStreamFuel]
            omega]
      rw [run_iteration first second third rest accumulator
        (state := state) hpc
        (by simpa only [List.map_cons, rawEncodedClause_eq] using hcursor)
        haccumulator
        (by simpa only [List.map_cons, rawEncodedClause_eq] using hsource)
        hiterationOutput hbits]
      rw [show
        (([first, second, third] :: rest).map Encodable.encode).reverse ++
            accumulator =
          (rest.map Encodable.encode).reverse ++ nextAccumulator by
            simp [nextAccumulator, clauseCode, List.append_assoc]]
      apply ih nextAccumulator
      · rfl
      · simp [structuralClauseNextState]
      · simp [structuralClauseNextState, nextAccumulator, clauseCode]
      · exact hrestThree
      · exact hsourceTail
      · exact houtputNext

def structuralClauseStreamMaximumBits (formula : EncodedCNF) : ℕ :=
  natBitLength
    (max (rawClauseStream formula)
      (canonicalReverseClauseStream formula))

/-- Exact fixed-program refinement.  The only premise is the structural
three-literal invariant already proved for the Tseitin formula family. -/
theorem run_structuralClauseStreamProgram
    (formula : EncodedCNF)
    (hthree :
      formula.all (fun clause => clause.length = 3) = true)
    (inputLength : ℕ) :
    runNPOracleProgram structuralClauseStreamProgram
        (structuralClauseStreamMaximumBits formula)
        (structuralClauseStreamFuel formula)
        (initialNPOracleState inputLength (rawClauseStream formula)) =
      some (canonicalReverseClauseStream formula) := by
  have hrun :=
    run_structuralClauseStream_from formula []
      (maximumBits := structuralClauseStreamMaximumBits formula)
      (sourceBound := rawClauseStream formula)
      (outputBound := canonicalReverseClauseStream formula)
      (initialNPOracleState inputLength (rawClauseStream formula))
      (by rfl)
      (by rfl)
      (by simp [initialNPOracleState, encodeTaggedList])
      hthree le_rfl
      (by simp [canonicalReverseClauseStream])
      (by rfl)
  simpa [rawClauseStream, canonicalReverseClauseStream] using hrun

end NearCubicWires.StructuralClauseStreamProgram
