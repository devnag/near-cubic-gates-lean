import Proof.Circuits.StructuralAddressRun

/-!
# Level 11 of the nested structural compiler: the clause compiler

`selectiveClauseProgram` is the `241`-instruction stream that compiles one
decoded three-literal clause.  Its `76`-instruction controller relocates three
callees — the published literal decoder, the private tagged lookup and the
append transition — and walks the clause's fixed five-append schedule with a
phase register rather than a spine.

The controller's cycle is:

* `16`–`29` decode one literal of the clause and read its live wire value;
* `30` dispatches on the literal's sign, appending a `not` in phase `0` when it
  is negative;
* `36` joins the two sign branches and dispatches on the position cursor: at
  position `0` the wire is retained as the clause's first operand and the cursor
  advances, at position `1` the first canonical `or` is appended in phase `1`,
  at position `2` the second canonical `or` is appended in phase `2`;
* `57`–`68` is the single shared append block (`SelectiveClauseRun` §9), and
  `69` is the phase dispatcher: phase `0` re-enters the sign join at `36`, phase
  `1` retains the first disjunction and advances the cursor, phase `2` halts.

`SelectiveClauseRun` §3 fixes the typed schedule, §6 runs the private lookup at
an arbitrary entry state, and `SelectiveClauseLeafEntry` §6 runs the published
literal decoder on a relocated frame.  This module therefore closes level 11:
`selectiveClauseRunner` has no premise at all.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveCompileLiteral_ordered
  from Proof.Supplier.SelectiveCountCasesRun

open private selectiveClauseProgram selectiveClauseControllerProgram
  selectiveClauseControllerProgram_length selectiveClauseInput
  structuralTaggedLookupProgram structuralTaggedLookupInput
  structuralTaggedLookupFuel structuralTaggedLookupBits
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The two fields of an encoded literal -/

/-- Live-wire index of a literal, as the machine reads it back. -/
private def literalIndexValue {q : ℕ} : Literal q → ℕ
  | .positive query => query.val
  | .negative query => query.val

/-- Sign tag of a literal, as the machine reads it back. -/
private def literalTagCode {q : ℕ} : Literal q → ℕ
  | .positive _ => 0
  | .negative _ => 1

private theorem encodeLiteral_eq_pair {q : ℕ} (literal : Literal q) :
    encodeLiteral literal =
      Nat.pair (literalTagCode literal) (literalIndexValue literal) := by
  cases literal <;> rfl

/-! ## 2. The sign dispatch

A positive literal falls straight through to the position join; a negative one
appends a `not` in phase `0` and re-enters the join from the phase
dispatcher. -/

/-- Register width of the sign dispatch: nothing at all on a positive literal,
the `not` append on a negative one. -/
private def selectiveClauseSignBits {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) : Literal q → ℕ
  | .positive _ => 0
  | .negative query =>
      max (natBitLength (n + values.getD query.val 0)) <|
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := n)
                (.not (values.getD query.val 0)))))
          (natBitLength
            (Nat.pair 0
              (selectiveWireCode
                (selectiveNot state (values.getD query.val 0)))))

/-- Interpreter fuel of the sign dispatch. -/
private def selectiveClauseSignFuel {q n : ℕ} (state : SelectiveState n) :
    Literal q → ℕ
  | .positive _ => 1
  | .negative _ =>
      19 +
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected)

set_option maxHeartbeats 1600000 in
-- Five request-building steps around the relocated append on the negative
-- branch, each re-deriving the append's own width envelope.
private theorem run_selectiveClauseSignStep {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ) (literal : Literal q)
    (hordered : selectiveStateOrdered state)
    (maximumBits extraFuel finalOutput : ℕ)
    (valuesCode literalArity decisionCode clauseIndex position first
      firstOrSecond : ℕ)
    (machine : NPOracleState)
    (hbits : selectiveClauseSignBits state values literal ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (htwoBits : natBitLength 2 ≤ maximumBits)
    (hpc : machine.pc = 30)
    (htag : machine.registers 18 = literalTagCode literal)
    (hvalue :
      machine.registers 20 = values.getD (literalIndexValue literal) 0)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harityRegister : machine.registers 8 = n)
    (hvaluesRegister : machine.registers 10 = valuesCode)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hposition : machine.registers 17 = position)
    (hfirst : machine.registers 21 = first)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 36 →
      resumed.registers 4 =
        (selectiveCompileLiteral state values literal).state.target -
          (selectiveCompileLiteral state values literal).state.next →
      resumed.registers 6 =
        (selectiveCompileLiteral state values literal).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveCompileLiteral state values literal).state.selected →
      resumed.registers 20 =
        (selectiveCompileLiteral state values literal).output →
      resumed.registers 8 = n →
      resumed.registers 10 = valuesCode →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = position →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClauseProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits
        (selectiveClauseSignFuel state literal + extraFuel) machine =
      some finalOutput := by
  cases literal with
  | positive query =>
      rw [show selectiveClauseSignFuel state (Literal.positive query) +
          extraFuel = extraFuel + 1 by
        simp only [selectiveClauseSignFuel]
        omega]
      rw [run_branchZero_instruction
        (selectiveClauseProgram_controllerAt (pc := 30) rfl) hpc]
      rw [if_pos (by rw [htag]; rfl)]
      refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp [NPOracleState.jump, selectiveCompileLiteral, hremaining, hnext,
          hselected, hvalue, harityRegister, hvaluesRegister, hliteralArity,
          hdecisionCode, hclauseIndex, hposition, hfirst, hfirstOrSecond,
          hzeroRegister, literalIndexValue]
  | negative query =>
      have hvalueLocal :
          machine.registers 20 = values.getD query.val 0 := by
        simpa [literalIndexValue] using hvalue
      have hsignBits :
          selectiveClauseSignBits state values (Literal.negative query) =
            max (natBitLength (n + values.getD query.val 0))
              (max
                (natBitLength
                  (selectiveEmitInput (state.target - state.next) state.next
                    (selectiveSelectedCode state.selected)
                    (rawCircuitNodeCode (n := n)
                      (.not (values.getD query.val 0)))))
                (natBitLength
                  (Nat.pair 0
                    (selectiveWireCode
                      (selectiveNot state (values.getD query.val 0)))))) := rfl
      rw [hsignBits] at hbits
      have hchildBits :
          natBitLength (n + values.getD query.val 0) ≤ maximumBits :=
        (Nat.le_max_left _ _).trans hbits
      have hbitsTail := (Nat.le_max_right _ _).trans hbits
      have hinputBits :
          natBitLength
              (selectiveEmitInput (state.target - state.next) state.next
                (selectiveSelectedCode state.selected)
                (rawCircuitNodeCode (n := n)
                  (.not (values.getD query.val 0)))) ≤
            maximumBits :=
        (Nat.le_max_left _ _).trans hbitsTail
      have hwireBits :
          natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveNot state (values.getD query.val 0)))) ≤
            maximumBits :=
        (Nat.le_max_right _ _).trans hbitsTail
      have hnodeBits :
          natBitLength
              (rawCircuitNodeCode (n := n)
                (.not (values.getD query.val 0))) ≤
            maximumBits :=
        natBitLength_pair_right hinputBits
      rw [show selectiveClauseSignFuel state (Literal.negative query) +
          extraFuel =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 5 + 1 by
        simp only [selectiveClauseSignFuel]
        omega]
      rw [run_branchZero_instruction
        (selectiveClauseProgram_controllerAt (pc := 30) rfl) hpc]
      rw [if_neg (by rw [htag]; simp [literalTagCode])]
      rw [show (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 5 =
        ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 4) + 1 by omega]
      rw [run_add_instruction (value := n + values.getD query.val 0)
        (selectiveClauseProgram_controllerAt (pc := 31) rfl) rfl
        (by
          simp [NPOracleState.jump, harityRegister, hvalueLocal])
        hchildBits]
      rw [show ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 4) =
        ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 3) + 1 by omega]
      rw [run_set_instruction
        (selectiveClauseProgram_controllerAt (pc := 32) rfl) rfl htwoBits]
      rw [show ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 3) =
        ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 2) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := n) (.not (values.getD query.val 0)))
        (selectiveClauseProgram_controllerAt (pc := 33) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, rawCircuitNodeCode])
        hnodeBits]
      rw [show ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 2) =
        ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 1) + 1 by omega]
      rw [run_set_instruction
        (selectiveClauseProgram_controllerAt (pc := 34) rfl) rfl hzeroBits]
      rw [show ((5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 1) =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 + (1 + extraFuel)))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveClauseProgram_controllerAt (pc := 35) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveClauseEmitCall state
        (.not (values.getD query.val 0)) hordered maximumBits _ (1 + extraFuel)
        finalOutput n valuesCode literalArity decisionCode clauseIndex position
        first firstOrSecond 0 _ rfl hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, harityRegister]
      · simp [NPOracleState.write, NPOracleState.jump, hvaluesRegister]
      · simp [NPOracleState.write, NPOracleState.jump, hliteralArity]
      · simp [NPOracleState.write, NPOracleState.jump, hdecisionCode]
      · simp [NPOracleState.write, NPOracleState.jump, hclauseIndex]
      · simp [NPOracleState.write, NPOracleState.jump, hposition]
      · simp [NPOracleState.write, NPOracleState.jump, hfirst]
      · simp [NPOracleState.write, NPOracleState.jump, hfirstOrSecond]
      · simp [NPOracleState.write, NPOracleState.jump, hzeroRegister]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc _hresumedWire _hresumedState hresumedRemaining
          hresumedNext hresumedSelected hresumedOutput hresumedArity
          hresumedValues hresumedLiteralArity hresumedDecisionCode
          hresumedClauseIndex hresumedPosition hresumedFirst
          hresumedFirstOrSecond hresumedZero hresumedPhase
        rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveClauseProgram_controllerAt (pc := 69) rfl) hresumedPc]
        rw [if_pos (by rw [hresumedPhase])]
        refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simpa [NPOracleState.jump, selectiveCompileLiteral, selectiveNot]
            using hresumedRemaining
        · simpa [NPOracleState.jump, selectiveCompileLiteral, selectiveNot]
            using hresumedNext
        · simpa [NPOracleState.jump, selectiveCompileLiteral, selectiveNot]
            using hresumedSelected
        · simpa [NPOracleState.jump, selectiveCompileLiteral, selectiveNot]
            using hresumedOutput
        · simpa [NPOracleState.jump] using hresumedArity
        · simpa [NPOracleState.jump] using hresumedValues
        · simpa [NPOracleState.jump] using hresumedLiteralArity
        · simpa [NPOracleState.jump] using hresumedDecisionCode
        · simpa [NPOracleState.jump] using hresumedClauseIndex
        · simpa [NPOracleState.jump] using hresumedPosition
        · simpa [NPOracleState.jump] using hresumedFirst
        · simpa [NPOracleState.jump] using hresumedFirstOrSecond
        · simpa [NPOracleState.jump] using hresumedZero

/-! ## 3. One literal of the clause

The block from `16` to `36`: build the level's literal request, decode it with
the published decoder, read the named live wire with the private tagged lookup
and dispatch on the sign. -/

/-- Register width of one literal of the clause. -/
private def selectiveClauseLiteralBits {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (literalArity decisionCode clauseIndex position : ℕ)
    (literal : Literal q) : ℕ :=
  max
    (natBitLength
      (threeCNFLiteralInput literalArity decisionCode clauseIndex position)) <|
    max (threeCNFLiteralBits 0 literalArity decisionCode clauseIndex position) <|
      max (natBitLength (Nat.pair 0 (encodeLiteral literal))) <|
        max
          (natBitLength
            (structuralTaggedLookupInput (encodeTaggedList values)
              (literalIndexValue literal))) <|
          max (structuralTaggedLookupBits values (literalIndexValue literal)) <|
            max
              (natBitLength
                (Nat.pair 0 (values.getD (literalIndexValue literal) 0)))
              (selectiveClauseSignBits state values literal)

/-- Interpreter fuel of one literal of the clause. -/
private def selectiveClauseLiteralFuel {q n : ℕ} (state : SelectiveState n)
    (literalArity decisionCode clauseIndex position : ℕ)
    (literal : Literal q) : ℕ :=
  7 +
    (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
      (6 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + selectiveClauseSignFuel state literal))))

set_option maxHeartbeats 3200000 in
-- Two relocated calls and fourteen controller steps, each re-deriving the
-- callee's own width envelope from the level request.
private theorem run_selectiveClauseLiteralStep {n literalArity : ℕ}
    (harity : 0 < literalArity) (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex position : ℕ) (literal : Literal literalArity)
    (hliteral :
      threeCNFLiteralOutput literalArity decisionCode clauseIndex position =
        encodeLiteral literal)
    (hordered : selectiveStateOrdered state)
    (maximumBits extraFuel finalOutput first firstOrSecond : ℕ)
    (machine : NPOracleState)
    (hbits :
      selectiveClauseLiteralBits state values literalArity decisionCode
          clauseIndex position literal ≤
        maximumBits)
    (htwoBits : natBitLength 2 ≤ maximumBits)
    (hpc : machine.pc = 16)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harityRegister : machine.registers 8 = n)
    (hvaluesRegister : machine.registers 10 = encodeTaggedList values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hposition : machine.registers 17 = position)
    (hfirst : machine.registers 21 = first)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 36 →
      resumed.registers 4 =
        (selectiveCompileLiteral state values literal).state.target -
          (selectiveCompileLiteral state values literal).state.next →
      resumed.registers 6 =
        (selectiveCompileLiteral state values literal).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveCompileLiteral state values literal).state.selected →
      resumed.registers 20 =
        (selectiveCompileLiteral state values literal).output →
      resumed.registers 8 = n →
      resumed.registers 10 = encodeTaggedList values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = position →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClauseProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits
        (selectiveClauseLiteralFuel state literalArity decisionCode clauseIndex
          position literal + extraFuel) machine =
      some finalOutput := by
  rw [selectiveClauseLiteralBits] at hbits
  have hrequestBits :
      natBitLength
          (threeCNFLiteralInput literalArity decisionCode clauseIndex
            position) ≤
        maximumBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hdecoderBits :
      threeCNFLiteralBits 0 literalArity decisionCode clauseIndex position ≤
        maximumBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hliteralPairBits :
      natBitLength (Nat.pair 0 (encodeLiteral literal)) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hlookupRequestBits :
      natBitLength
          (structuralTaggedLookupInput (encodeTaggedList values)
            (literalIndexValue literal)) ≤
        maximumBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hlookupBits :
      structuralTaggedLookupBits values (literalIndexValue literal) ≤
        maximumBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hvaluePairBits :
      natBitLength
          (Nat.pair 0 (values.getD (literalIndexValue literal) 0)) ≤
        maximumBits := (Nat.le_max_left _ _).trans hbitsFive
  have hsignBits :
      selectiveClauseSignBits state values literal ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbitsFive
  have hrequestFlat := hrequestBits
  simp only [threeCNFLiteralInput, encodedNestedListLookupInput,
    encodedListLookupInput] at hrequestFlat
  have hnestedBits := natBitLength_pair_left hrequestFlat
  have houterBits := natBitLength_pair_left hnestedBits
  have hpositionPairBits := natBitLength_pair_right hnestedBits
  have hclausePairBits := natBitLength_pair_right houterBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    natBitLength_pair_right hpositionPairBits
  have hliteralCodeBits :
      natBitLength (encodeLiteral literal) ≤ maximumBits :=
    natBitLength_pair_right hliteralPairBits
  have hliteralFlat := hliteralCodeBits
  rw [encodeLiteral_eq_pair] at hliteralFlat
  have htagBits : natBitLength (literalTagCode literal) ≤ maximumBits :=
    natBitLength_pair_left hliteralFlat
  have hindexBits : natBitLength (literalIndexValue literal) ≤ maximumBits :=
    natBitLength_pair_right hliteralFlat
  have hvalueBits :
      natBitLength (values.getD (literalIndexValue literal) 0) ≤ maximumBits :=
    natBitLength_pair_right hvaluePairBits
  rw [selectiveClauseLiteralFuel]
  rw [show 7 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + selectiveClauseSignFuel state literal)))) + extraFuel =
    (6 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_pair_instruction (value := Nat.pair position 0)
    (selectiveClauseProgram_controllerAt (pc := 16) rfl) hpc
    (by rw [hposition, hzeroRegister]) hpositionPairBits]
  rw [show 6 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (5 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_pair_instruction (value := Nat.pair clauseIndex 0)
    (selectiveClauseProgram_controllerAt (pc := 17) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hclauseIndex,
        hzeroRegister])
    hclausePairBits]
  rw [show 5 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (4 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value := Nat.pair decisionCode (Nat.pair clauseIndex 0))
    (selectiveClauseProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hdecisionCode])
    houterBits]
  rw [show 4 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (3 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair decisionCode (Nat.pair clauseIndex 0))
        (Nat.pair position 0))
    (selectiveClauseProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnestedBits]
  rw [show 3 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (2 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value := threeCNFLiteralInput literalArity decisionCode clauseIndex
      position)
    (selectiveClauseProgram_controllerAt (pc := 20) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hliteralArity,
        threeCNFLiteralInput, encodedNestedListLookupInput,
        encodedListLookupInput])
    hrequestBits]
  rw [show 2 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (1 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel)))))) + 1 by
    omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 21) rfl) rfl hzeroBits]
  rw [show 1 +
      (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
        (6 +
          (structuralTaggedLookupFuel (literalIndexValue literal) +
            (1 + (selectiveClauseSignFuel state literal + extraFuel))))) =
    (threeCNFLiteralFuel literalArity decisionCode clauseIndex position +
      (6 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))))) + 1 by
    omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 22) rfl) rfl hzeroBits]
  refine run_selectiveRelocatedCall_frame
    (source := threeCNFLiteralProgram)
    (calleeOutput := encodeLiteral literal)
    selectiveClauseProgram_literalCallable (by omega) rfl ?_ ?_
    hliteralPairBits ?_
  · intro entry hentryPc hentryInput hentryLength
    rw [← hliteral]
    refine run_bits_mono
      (run_threeCNFLiteralProgram_anyEntry 0 literalArity decisionCode
        clauseIndex position harity entry hentryPc ?_ ?_) hdecoderBits
    · rw [hentryInput]
      simp [NPOracleState.write, NPOracleState.jump]
    · have hzeroSlot : entry.registers 1 = 0 := by
        rw [hentryLength]
        simp [NPOracleState.write, NPOracleState.jump]
      rw [hzeroSlot]
      exact Nat.le_max_left _ _
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro literalHalt
    rw [show 6 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (5 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel)))) + 1 by
      omega]
    rw [run_unpairRight_instruction (value := encodeLiteral literal)
      (selectiveClauseProgram_controllerAt (pc := 23) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hliteralCodeBits]
    rw [show 5 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (4 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel)))) + 1 by
      omega]
    rw [run_unpairLeft_instruction (value := literalTagCode literal)
      (selectiveClauseProgram_controllerAt (pc := 24) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, encodeLiteral_eq_pair])
      htagBits]
    rw [show 4 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (3 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel)))) + 1 by
      omega]
    rw [run_unpairRight_instruction (value := literalIndexValue literal)
      (selectiveClauseProgram_controllerAt (pc := 25) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, encodeLiteral_eq_pair])
      hindexBits]
    rw [show 3 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (2 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel)))) + 1 by
      omega]
    rw [run_pair_instruction
      (value :=
        structuralTaggedLookupInput (encodeTaggedList values)
          (literalIndexValue literal))
      (selectiveClauseProgram_controllerAt (pc := 26) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hvaluesRegister, structuralTaggedLookupInput])
      hlookupRequestBits]
    rw [show 2 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (1 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel)))) + 1 by
      omega]
    rw [run_set_instruction
      (selectiveClauseProgram_controllerAt (pc := 27) rfl) rfl hzeroBits]
    rw [show 1 +
        (structuralTaggedLookupFuel (literalIndexValue literal) +
          (1 + (selectiveClauseSignFuel state literal + extraFuel))) =
      (structuralTaggedLookupFuel (literalIndexValue literal) +
        (1 + (selectiveClauseSignFuel state literal + extraFuel))) + 1 by
      omega]
    rw [run_branchZero_instruction
      (selectiveClauseProgram_controllerAt (pc := 28) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveRelocatedCall
      (source := structuralTaggedLookupProgram)
      (calleeOutput := values.getD (literalIndexValue literal) 0)
      selectiveClauseProgram_lookupCallable (by omega) rfl ?_ ?_
      hvaluePairBits ?_
    · intro frame hframePc hframeInput
      refine run_bits_mono
        (run_structuralTaggedLookupProgram_anyEntry values
          (literalIndexValue literal) frame hframePc ?_) hlookupBits
      rw [hframeInput]
      simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · intro lookupHalt
      rw [show 1 + (selectiveClauseSignFuel state literal + extraFuel) =
        (selectiveClauseSignFuel state literal + extraFuel) + 1 by omega]
      rw [run_unpairRight_instruction
        (value := values.getD (literalIndexValue literal) 0)
        (selectiveClauseProgram_controllerAt (pc := 29) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      refine run_selectiveClauseSignStep state values literal hordered
        maximumBits extraFuel finalOutput (encodeTaggedList values) literalArity
        decisionCode clauseIndex position first firstOrSecond _ hsignBits
        hzeroBits htwoBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        hcontinue
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, relocateState]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          harityRegister]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hvaluesRegister]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hliteralArity]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hdecisionCode]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hclauseIndex]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState, hposition]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState, hfirst]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hfirstOrSecond]
      · simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hzeroRegister]

/-! ## 4. The position joins and the phase dispatcher

Four small blocks close the controller's cycle.  Each is stated as a
continuation over the registers it rewrites, so the whole-stream trace below
never carries a compound clock through an arithmetic step. -/

/-- Register width of one canonical disjunction of the clause. -/
private def selectiveClauseOrBits {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected)
        (rawCircuitNodeCode (n := n) (.or left right))))
    (natBitLength
      (Nat.pair 0 (selectiveWireCode (selectiveOr state left right))))

-- The position-zero join retains the first literal's wire and advances the
-- cursor.
private theorem run_selectiveClauseJoinZero
    {maximumBits tailFuel finalOutput : ℕ}
    (remaining next selected arity valuesCode literalArity decisionCode
      clauseIndex value firstOrSecond : ℕ)
    (machine : NPOracleState)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hfourBits : natBitLength 4 ≤ maximumBits)
    (hpc : machine.pc = 36)
    (hposition : machine.registers 17 = 0)
    (hremaining : machine.registers 4 = remaining)
    (hnext : machine.registers 6 = next)
    (hselected : machine.registers 7 = selected)
    (harity : machine.registers 8 = arity)
    (hvalues : machine.registers 10 = valuesCode)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hvalue : machine.registers 20 = value)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 16 →
      resumed.registers 4 = remaining →
      resumed.registers 6 = next →
      resumed.registers 7 = selected →
      resumed.registers 8 = arity →
      resumed.registers 10 = valuesCode →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = 1 →
      resumed.registers 21 = value →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClauseProgram maximumBits tailFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits (4 + tailFuel)
        machine =
      some finalOutput := by
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  rw [show 4 + tailFuel = (3 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 36) rfl) hpc]
  rw [if_pos (by rw [hposition])]
  rw [show 3 + tailFuel = (2 + tailFuel) + 1 by omega]
  rw [run_copy_instruction (value := value)
    (selectiveClauseProgram_controllerAt (pc := 40) rfl) rfl
    (by simp [NPOracleState.jump, hvalue]) hvalueBits]
  rw [show 2 + tailFuel = (1 + tailFuel) + 1 by omega]
  rw [run_increment_instruction (value := 1)
    (selectiveClauseProgram_controllerAt (pc := 41) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hposition]) honeBits]
  rw [show 1 + tailFuel = tailFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 42) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext, hselected,
      harity, hvalues, hliteralArity, hdecisionCode, hclauseIndex,
      hfirstOrSecond, hzeroRegister]

-- The position-one join builds the clause's first canonical disjunction and
-- enters the shared append block in phase one.
private theorem run_selectiveClauseJoinOne {n : ℕ}
    {maximumBits tailFuel finalOutput : ℕ}
    (remaining next selected valuesCode literalArity decisionCode clauseIndex
      first second firstOrSecond : ℕ)
    (machine : NPOracleState)
    (hnodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.or first second)) ≤
        maximumBits)
    (hfourBits : natBitLength 4 ≤ maximumBits)
    (hpc : machine.pc = 36)
    (hposition : machine.registers 17 = 1)
    (hremaining : machine.registers 4 = remaining)
    (hnext : machine.registers 6 = next)
    (hselected : machine.registers 7 = selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = valuesCode)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hsecond : machine.registers 20 = second)
    (hfirst : machine.registers 21 = first)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 4 = remaining →
      resumed.registers 6 = next →
      resumed.registers 7 = selected →
      resumed.registers 8 = n →
      resumed.registers 10 = valuesCode →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = 1 →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 23 = rawCircuitNodeCode (n := n) (.or first second) →
      resumed.registers 29 = 0 →
      resumed.registers 30 = 1 →
      runNPOracleProgram selectiveClauseProgram maximumBits tailFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits (11 + tailFuel)
        machine =
      some finalOutput := by
  have hnodeForm :
      rawCircuitNodeCode (n := n) (.or first second) =
        Nat.pair 4 (Nat.pair (n + first) (n + second)) := rfl
  have hchildrenBits :
      natBitLength (Nat.pair (n + first) (n + second)) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hnodeBits
    rw [hnodeForm]
    exact Nat.right_le_pair 4 _
  have hleftBits : natBitLength (n + first) ≤ maximumBits :=
    natBitLength_pair_left hchildrenBits
  have hrightBits : natBitLength (n + second) ≤ maximumBits :=
    natBitLength_pair_right hchildrenBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  rw [show 11 + tailFuel = (10 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 36) rfl) hpc]
  rw [if_neg (by rw [hposition]; omega)]
  rw [show 10 + tailFuel = (9 + tailFuel) + 1 by omega]
  rw [run_copy_instruction (value := 1)
    (selectiveClauseProgram_controllerAt (pc := 37) rfl) rfl
    (by simp [NPOracleState.jump, hposition]) honeBits]
  rw [show 9 + tailFuel = (8 + tailFuel) + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveClauseProgram_controllerAt (pc := 38) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits]
  rw [show 8 + tailFuel = (7 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 39) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 7 + tailFuel = (6 + tailFuel) + 1 by omega]
  rw [run_add_instruction (value := n + first)
    (selectiveClauseProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, hfirst])
    hleftBits]
  rw [show 6 + tailFuel = (5 + tailFuel) + 1 by omega]
  rw [run_add_instruction (value := n + second)
    (selectiveClauseProgram_controllerAt (pc := 44) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, hsecond])
    hrightBits]
  rw [show 5 + tailFuel = (4 + tailFuel) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + first) (n + second))
    (selectiveClauseProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 4 + tailFuel = (3 + tailFuel) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 46) rfl) rfl hfourBits]
  rw [show 3 + tailFuel = (2 + tailFuel) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.or first second))
    (selectiveClauseProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm]) hnodeBits]
  rw [show 2 + tailFuel = (1 + tailFuel) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 48) rfl) rfl honeBits]
  rw [show 1 + tailFuel = tailFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 49) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext, hselected,
      harity, hvalues, hliteralArity, hdecisionCode, hclauseIndex, hposition,
      hfirst, hfirstOrSecond, hzeroRegister]

-- The position-two join builds the clause's second canonical disjunction and
-- enters the shared append block in phase two.
private theorem run_selectiveClauseJoinTwo {n : ℕ}
    {maximumBits tailFuel finalOutput : ℕ}
    (remaining next selected valuesCode literalArity decisionCode clauseIndex
      first firstOrSecond third : ℕ)
    (machine : NPOracleState)
    (hnodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.or firstOrSecond third)) ≤
        maximumBits)
    (hfourBits : natBitLength 4 ≤ maximumBits)
    (hpc : machine.pc = 36)
    (hposition : machine.registers 17 = 2)
    (hremaining : machine.registers 4 = remaining)
    (hnext : machine.registers 6 = next)
    (hselected : machine.registers 7 = selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = valuesCode)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hthird : machine.registers 20 = third)
    (hfirst : machine.registers 21 = first)
    (hfirstOrSecond : machine.registers 22 = firstOrSecond)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 4 = remaining →
      resumed.registers 6 = next →
      resumed.registers 7 = selected →
      resumed.registers 8 = n →
      resumed.registers 10 = valuesCode →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = 2 →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 23 =
        rawCircuitNodeCode (n := n) (.or firstOrSecond third) →
      resumed.registers 29 = 0 →
      resumed.registers 30 = 2 →
      runNPOracleProgram selectiveClauseProgram maximumBits tailFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits (11 + tailFuel)
        machine =
      some finalOutput := by
  have hnodeForm :
      rawCircuitNodeCode (n := n) (.or firstOrSecond third) =
        Nat.pair 4 (Nat.pair (n + firstOrSecond) (n + third)) := rfl
  have hchildrenBits :
      natBitLength (Nat.pair (n + firstOrSecond) (n + third)) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hnodeBits
    rw [hnodeForm]
    exact Nat.right_le_pair 4 _
  have hleftBits : natBitLength (n + firstOrSecond) ≤ maximumBits :=
    natBitLength_pair_left hchildrenBits
  have hrightBits : natBitLength (n + third) ≤ maximumBits :=
    natBitLength_pair_right hchildrenBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  rw [show 11 + tailFuel = (10 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 36) rfl) hpc]
  rw [if_neg (by rw [hposition]; omega)]
  rw [show 10 + tailFuel = (9 + tailFuel) + 1 by omega]
  rw [run_copy_instruction (value := 2)
    (selectiveClauseProgram_controllerAt (pc := 37) rfl) rfl
    (by simp [NPOracleState.jump, hposition]) htwoBits]
  rw [show 9 + tailFuel = (8 + tailFuel) + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveClauseProgram_controllerAt (pc := 38) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) honeBits]
  rw [show 8 + tailFuel = (7 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 39) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 7 + tailFuel = (6 + tailFuel) + 1 by omega]
  rw [run_add_instruction (value := n + firstOrSecond)
    (selectiveClauseProgram_controllerAt (pc := 50) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, harity, hfirstOrSecond])
    hleftBits]
  rw [show 6 + tailFuel = (5 + tailFuel) + 1 by omega]
  rw [run_add_instruction (value := n + third)
    (selectiveClauseProgram_controllerAt (pc := 51) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, hthird])
    hrightBits]
  rw [show 5 + tailFuel = (4 + tailFuel) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + firstOrSecond) (n + third))
    (selectiveClauseProgram_controllerAt (pc := 52) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 4 + tailFuel = (3 + tailFuel) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 53) rfl) rfl hfourBits]
  rw [show 3 + tailFuel = (2 + tailFuel) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.or firstOrSecond third))
    (selectiveClauseProgram_controllerAt (pc := 54) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm]) hnodeBits]
  rw [show 2 + tailFuel = (1 + tailFuel) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 55) rfl) rfl htwoBits]
  rw [show 1 + tailFuel = tailFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 56) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext, hselected,
      harity, hvalues, hliteralArity, hdecisionCode, hclauseIndex, hposition,
      hfirst, hfirstOrSecond, hzeroRegister]

-- Phase one retains the first disjunction and advances the cursor.
private theorem run_selectiveClausePhaseOne
    {maximumBits tailFuel finalOutput : ℕ}
    (remaining next selected arity valuesCode literalArity decisionCode
      clauseIndex first value : ℕ)
    (machine : NPOracleState)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hfourBits : natBitLength 4 ≤ maximumBits)
    (hpc : machine.pc = 69)
    (hphase : machine.registers 30 = 1)
    (hremaining : machine.registers 4 = remaining)
    (hnext : machine.registers 6 = next)
    (hselected : machine.registers 7 = selected)
    (harity : machine.registers 8 = arity)
    (hvalues : machine.registers 10 = valuesCode)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 16 = clauseIndex)
    (hposition : machine.registers 17 = 1)
    (hfirst : machine.registers 21 = first)
    (hvalue : machine.registers 20 = value)
    (hzeroRegister : machine.registers 29 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 16 →
      resumed.registers 4 = remaining →
      resumed.registers 6 = next →
      resumed.registers 7 = selected →
      resumed.registers 8 = arity →
      resumed.registers 10 = valuesCode →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = 2 →
      resumed.registers 21 = first →
      resumed.registers 22 = value →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClauseProgram maximumBits tailFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits (6 + tailFuel)
        machine =
      some finalOutput := by
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  rw [show 6 + tailFuel = (5 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 69) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 5 + tailFuel = (4 + tailFuel) + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveClauseProgram_controllerAt (pc := 70) rfl) rfl
    (by simp [NPOracleState.jump, hphase]) hzeroBits]
  rw [show 4 + tailFuel = (3 + tailFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 71) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 3 + tailFuel = (2 + tailFuel) + 1 by omega]
  rw [run_copy_instruction (value := value)
    (selectiveClauseProgram_controllerAt (pc := 72) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hvalue]) hvalueBits]
  rw [show 2 + tailFuel = (1 + tailFuel) + 1 by omega]
  rw [run_increment_instruction (value := 2)
    (selectiveClauseProgram_controllerAt (pc := 73) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hposition]) htwoBits]
  rw [show 1 + tailFuel = tailFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 74) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext, hselected,
      harity, hvalues, hliteralArity, hdecisionCode, hclauseIndex, hfirst,
      hzeroRegister]

-- Phase two halts on the clause's compiled wire.
private theorem run_selectiveClausePhaseTwo {maximumBits output : ℕ}
    (machine : NPOracleState)
    (houtputBits : natBitLength output ≤ maximumBits)
    (hfourBits : natBitLength 4 ≤ maximumBits)
    (hpc : machine.pc = 69)
    (hphase : machine.registers 30 = 2)
    (houtput : machine.registers 0 = output) :
    runNPOracleProgram selectiveClauseProgram maximumBits 4 machine =
      some output := by
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  rw [show (4 : ℕ) = ((1 + 1) + 1) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 69) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [run_decrement_instruction (value := 1)
    (selectiveClauseProgram_controllerAt (pc := 70) rfl) rfl
    (by simp [NPOracleState.jump, hphase]) honeBits]
  rw [run_branchZero_instruction
    (selectiveClauseProgram_controllerAt (pc := 71) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  exact run_halt_instruction (fuel := 0)
    (selectiveClauseProgram_controllerAt (pc := 75) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, houtput]) houtputBits

-- The sixteen-step request parser feeds the literal block at `16`.
private theorem run_selectiveClauseParse {n literalArity : ℕ}
    {maximumBits tailFuel finalOutput : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex first firstOrSecond : ℕ)
    (entry : NPOracleState)
    (hrequestBits :
      natBitLength
          (selectiveClauseInput (selectiveStateCode state) n
            (encodeTaggedList values) literalArity decisionCode clauseIndex) ≤
        maximumBits)
    (hpc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveClauseInput (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode clauseIndex)
    (hfirst : entry.registers 21 = first)
    (hfirstOrSecond : entry.registers 22 = firstOrSecond)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 16 →
      resumed.registers 4 = state.target - state.next →
      resumed.registers 6 = state.next →
      resumed.registers 7 = selectiveSelectedCode state.selected →
      resumed.registers 8 = n →
      resumed.registers 10 = encodeTaggedList values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = clauseIndex →
      resumed.registers 17 = 0 →
      resumed.registers 21 = first →
      resumed.registers 22 = firstOrSecond →
      resumed.registers 29 = 0 →
      runNPOracleProgram selectiveClauseProgram maximumBits tailFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClauseProgram maximumBits (16 + tailFuel)
        entry =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveClauseInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hfieldOne := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hfieldOne
  have hfieldTwo := natBitLength_pair_right hfieldOne
  have hvaluesBits := natBitLength_pair_left hfieldTwo
  have hfieldThree := natBitLength_pair_right hfieldTwo
  have hliteralArityBits := natBitLength_pair_left hfieldThree
  have hfieldFour := natBitLength_pair_right hfieldThree
  have hdecisionBits := natBitLength_pair_left hfieldFour
  have hclauseBits := natBitLength_pair_right hfieldFour
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailBits
  have hselectedBits := natBitLength_pair_right htailBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  rw [show 16 + tailFuel = (15 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveClauseProgram_controllerAt (pc := 0) rfl) hpc
    (by simp [hentryInput, selectiveClauseInput]) hstateBits]
  rw [show 15 + tailFuel = (14 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair n
        (Nat.pair (encodeTaggedList values)
          (Nat.pair literalArity (Nat.pair decisionCode clauseIndex))))
    (selectiveClauseProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveClauseInput])
    hfieldOne]
  rw [show 14 + tailFuel = (13 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveClauseProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 13 + tailFuel = (12 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClauseProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailBits]
  rw [show 12 + tailFuel = (11 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveClauseProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 11 + tailFuel = (10 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveClauseProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 10 + tailFuel = (9 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveClauseProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 9 + tailFuel = (8 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (encodeTaggedList values)
        (Nat.pair literalArity (Nat.pair decisionCode clauseIndex)))
    (selectiveClauseProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldTwo]
  rw [show 8 + tailFuel = (7 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := encodeTaggedList values)
    (selectiveClauseProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvaluesBits]
  rw [show 7 + tailFuel = (6 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair literalArity (Nat.pair decisionCode clauseIndex))
    (selectiveClauseProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldThree]
  rw [show 6 + tailFuel = (5 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := literalArity)
    (selectiveClauseProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hliteralArityBits]
  rw [show 5 + tailFuel = (4 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair decisionCode clauseIndex)
    (selectiveClauseProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldFour]
  rw [show 4 + tailFuel = (3 + tailFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := decisionCode)
    (selectiveClauseProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdecisionBits]
  rw [show 3 + tailFuel = (2 + tailFuel) + 1 by omega]
  rw [run_unpairRight_instruction (value := clauseIndex)
    (selectiveClauseProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hclauseBits]
  rw [show 2 + tailFuel = (1 + tailFuel) + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 14) rfl) rfl hzeroBits]
  rw [show 1 + tailFuel = tailFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveClauseProgram_controllerAt (pc := 15) rfl) rfl hzeroBits]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump, hfirst, hfirstOrSecond]

/-! ## 5. The whole `241`-instruction stream

The clause's five appends are the fixed schedule of `SelectiveClauseRun` §3, so
the controller's cycle unrolls exactly three times. -/

/-- The clause compiler's first literal wire, at the level's own request. -/
private abbrev clauseWireOne {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : SelectiveWire n :=
  selectiveCompileLiteral state values
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 0)

/-- The clause compiler's second literal wire. -/
private abbrev clauseWireTwo {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : SelectiveWire n :=
  selectiveCompileLiteral
    (clauseWireOne harity state values decisionCode clauseIndex).state values
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 1)

/-- The clause compiler's first disjunction. -/
private abbrev clauseWireOr {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : SelectiveWire n :=
  selectiveOr (clauseWireTwo harity state values decisionCode clauseIndex).state
    (clauseWireOne harity state values decisionCode clauseIndex).output
    (clauseWireTwo harity state values decisionCode clauseIndex).output

/-- The clause compiler's third literal wire. -/
private abbrev clauseWireThree {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : SelectiveWire n :=
  selectiveCompileLiteral
    (clauseWireOr harity state values decisionCode clauseIndex).state values
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 2)

private theorem selectiveCompileClause_eq_wires {n literalArity : ℕ}
    (harity : 0 < literalArity) (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) :
    selectiveCompileClause state values
        (selectiveClauseOf literalArity harity decisionCode clauseIndex) =
      selectiveOr
        (clauseWireThree harity state values decisionCode clauseIndex).state
        (clauseWireOr harity state values decisionCode clauseIndex).output
        (clauseWireThree harity state values decisionCode clauseIndex).output :=
  rfl

private theorem selectiveClauseLiteralBits_output {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (literalArity decisionCode clauseIndex position : ℕ)
    (literal : Literal q) :
    natBitLength (selectiveCompileLiteral state values literal).output ≤
      selectiveClauseLiteralBits state values literalArity decisionCode
        clauseIndex position literal := by
  have hvaluePair :
      natBitLength
          (Nat.pair 0 (values.getD (literalIndexValue literal) 0)) ≤
        selectiveClauseLiteralBits state values literalArity decisionCode
          clauseIndex position literal := by
    unfold selectiveClauseLiteralBits
    omega
  have hsign :
      selectiveClauseSignBits state values literal ≤
        selectiveClauseLiteralBits state values literalArity decisionCode
          clauseIndex position literal := by
    unfold selectiveClauseLiteralBits
    omega
  cases literal with
  | positive query =>
      exact natBitLength_pair_right hvaluePair
  | negative query =>
      have hpair :
          natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveNot state (values.getD query.val 0)))) ≤
            selectiveClauseLiteralBits state values literalArity decisionCode
              clauseIndex position (Literal.negative query) := by
        refine le_trans ?_ hsign
        simp only [selectiveClauseSignBits]
        omega
      have hcode := natBitLength_pair_right hpair
      rw [selectiveWireCode] at hcode
      exact natBitLength_pair_right hcode

private theorem selectiveClauseOrBits_input {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) :
    natBitLength
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or left right))) ≤
      selectiveClauseOrBits state left right :=
  Nat.le_max_left _ _

private theorem selectiveClauseOrBits_wire {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) :
    natBitLength
        (Nat.pair 0 (selectiveWireCode (selectiveOr state left right))) ≤
      selectiveClauseOrBits state left right :=
  Nat.le_max_right _ _

private theorem selectiveClauseOrBits_node {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) :
    natBitLength (rawCircuitNodeCode (n := n) (.or left right)) ≤
      selectiveClauseOrBits state left right :=
  natBitLength_pair_right (selectiveClauseOrBits_input state left right)

private theorem selectiveClauseOrBits_code {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) :
    natBitLength (selectiveWireCode (selectiveOr state left right)) ≤
      selectiveClauseOrBits state left right :=
  natBitLength_pair_right (selectiveClauseOrBits_wire state left right)

private theorem selectiveClauseOrBits_output {n : ℕ} (state : SelectiveState n)
    (left right : ℕ) :
    natBitLength (selectiveOr state left right).output ≤
      selectiveClauseOrBits state left right :=
  natBitLength_pair_right (selectiveClauseOrBits_code state left right)

/-- Register width of one whole clause compilation. -/
def selectiveClauseRunBits {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveClauseInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode clauseIndex)) <|
    max (natBitLength 4) <|
      max
        (selectiveClauseLiteralBits state values literalArity decisionCode
          clauseIndex 0
          (selectiveClauseOf literalArity harity decisionCode clauseIndex 0)) <|
        max
          (selectiveClauseLiteralBits
            (clauseWireOne harity state values decisionCode clauseIndex).state
            values literalArity decisionCode clauseIndex 1
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex 1)) <|
          max
            (selectiveClauseOrBits
              (clauseWireTwo harity state values decisionCode clauseIndex).state
              (clauseWireOne harity state values decisionCode clauseIndex).output
              (clauseWireTwo harity state values decisionCode
                clauseIndex).output) <|
            max
              (selectiveClauseLiteralBits
                (clauseWireOr harity state values decisionCode clauseIndex).state
                values literalArity decisionCode clauseIndex 2
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex 2))
              (selectiveClauseOrBits
                (clauseWireThree harity state values decisionCode
                  clauseIndex).state
                (clauseWireOr harity state values decisionCode
                  clauseIndex).output
                (clauseWireThree harity state values decisionCode
                  clauseIndex).output)

/-- Interpreter fuel of one whole clause compilation. -/
def selectiveClauseRunFuel {n literalArity : ℕ} (harity : 0 < literalArity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) : ℕ :=
  16 +
    (selectiveClauseLiteralFuel state literalArity decisionCode clauseIndex 0
        (selectiveClauseOf literalArity harity decisionCode clauseIndex 0) +
      (4 +
        (selectiveClauseLiteralFuel
            (clauseWireOne harity state values decisionCode clauseIndex).state
            literalArity decisionCode clauseIndex 1
            (selectiveClauseOf literalArity harity decisionCode clauseIndex 1) +
          (11 +
            (5 +
              (selectiveEmitFuel
                  ((clauseWireTwo harity state values decisionCode
                      clauseIndex).state.target -
                    (clauseWireTwo harity state values decisionCode
                      clauseIndex).state.next)
                  (selectiveSelectedCode
                    (clauseWireTwo harity state values decisionCode
                      clauseIndex).state.selected) +
                (7 +
                  (6 +
                    (selectiveClauseLiteralFuel
                        (clauseWireOr harity state values decisionCode
                          clauseIndex).state
                        literalArity decisionCode clauseIndex 2
                        (selectiveClauseOf literalArity harity decisionCode
                          clauseIndex 2) +
                      (11 +
                        (5 +
                          (selectiveEmitFuel
                              ((clauseWireThree harity state values decisionCode
                                  clauseIndex).state.target -
                                (clauseWireThree harity state values
                                  decisionCode clauseIndex).state.next)
                              (selectiveSelectedCode
                                (clauseWireThree harity state values
                                  decisionCode clauseIndex).state.selected) +
                            (7 + 4)))))))))))))

set_option maxHeartbeats 3200000 in
-- Three unrolled literal blocks, two relocated appends and five dispatchers,
-- with the whole width ledger re-derived from the level request.
/-- **Level 11's run.**  The `241`-instruction clause compiler started on its
own ABI frame, at any entry registers, returns exactly the source compiler's
wire for the decoded clause the request names. -/
theorem run_selectiveClauseProgram {n literalArity : ℕ}
    (harity : 0 < literalArity) (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex : ℕ) (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveClauseInput (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode clauseIndex) :
    runNPOracleProgram selectiveClauseProgram
        (selectiveClauseRunBits harity state values decisionCode clauseIndex)
        (selectiveClauseRunFuel harity state values decisionCode clauseIndex)
        entry =
      some
        (selectiveWireCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex))) := by
  have hbits := le_refl
    (selectiveClauseRunBits harity state values decisionCode clauseIndex)
  rw [selectiveClauseRunBits] at hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hfourBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hlitZeroBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hlitOneBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have horOneBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hlitTwoBits := (Nat.le_max_left _ _).trans hbitsFive
  have horTwoBits := (Nat.le_max_right _ _).trans hbitsFive
  have htwoBits :
      natBitLength 2 ≤
        selectiveClauseRunBits harity state values decisionCode clauseIndex :=
    (natBitLength_mono (by omega)).trans hfourBits
  have horderedOne :
      selectiveStateOrdered
        (clauseWireOne harity state values decisionCode clauseIndex).state :=
    selectiveCompileLiteral_ordered state values _ hordered
  have horderedTwo :
      selectiveStateOrdered
        (clauseWireTwo harity state values decisionCode clauseIndex).state :=
    selectiveCompileLiteral_ordered _ values _ horderedOne
  have horderedOr :
      selectiveStateOrdered
        (clauseWireOr harity state values decisionCode clauseIndex).state :=
    selectiveState_emit_ordered _ _ horderedTwo
  have horderedThree :
      selectiveStateOrdered
        (clauseWireThree harity state values decisionCode clauseIndex).state :=
    selectiveCompileLiteral_ordered _ values _ horderedOr
  have hlitZero :
      threeCNFLiteralOutput literalArity decisionCode clauseIndex 0 =
        encodeLiteral
          (selectiveClauseOf literalArity harity decisionCode clauseIndex 0) :=
    threeCNFLiteralOutput_eq_decodeThreeCNF literalArity decisionCode
      clauseIndex 0 harity
  have hlitOne :
      threeCNFLiteralOutput literalArity decisionCode clauseIndex 1 =
        encodeLiteral
          (selectiveClauseOf literalArity harity decisionCode clauseIndex 1) :=
    threeCNFLiteralOutput_eq_decodeThreeCNF literalArity decisionCode
      clauseIndex 1 harity
  have hlitTwo :
      threeCNFLiteralOutput literalArity decisionCode clauseIndex 2 =
        encodeLiteral
          (selectiveClauseOf literalArity harity decisionCode clauseIndex 2) :=
    threeCNFLiteralOutput_eq_decodeThreeCNF literalArity decisionCode
      clauseIndex 2 harity
  rw [selectiveCompileClause_eq_wires, selectiveClauseRunFuel]
  refine run_selectiveClauseParse state values decisionCode clauseIndex
    (entry.registers 21) (entry.registers 22) entry hrequestBits hentryPc
    hentryInput rfl rfl ?_
  intro parsed hparsedPc hp4 hp6 hp7 hp8 hp10 hp12 hp14 hp16 hp17 hp21 hp22 hp29
  refine run_selectiveClauseLiteralStep harity state values decisionCode
    clauseIndex 0
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 0) hlitZero
    hordered _ _ _ _ _ parsed hlitZeroBits htwoBits hparsedPc hp4 hp6 hp7 hp8
    hp10 hp12 hp14 hp16 hp17 hp21 hp22 hp29 ?_
  intro afterZero hZeroPc hz4 hz6 hz7 hz20 hz8 hz10 hz12 hz14 hz16 hz17 hz21
    hz22 hz29
  refine run_selectiveClauseJoinZero _ _ _ _ _ _ _ _ _ _ afterZero
    ((selectiveClauseLiteralBits_output state values literalArity decisionCode
      clauseIndex 0
      (selectiveClauseOf literalArity harity decisionCode
        clauseIndex 0)).trans hlitZeroBits)
    hfourBits hZeroPc hz17 hz4 hz6 hz7 hz8 hz10 hz12 hz14 hz16 hz20 hz22 hz29 ?_
  intro joinedZero hJoinZeroPc hj4 hj6 hj7 hj8 hj10 hj12 hj14 hj16 hj17 hj21
    hj22 hj29
  refine run_selectiveClauseLiteralStep harity
    (clauseWireOne harity state values decisionCode clauseIndex).state values
    decisionCode clauseIndex 1
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 1) hlitOne
    horderedOne _ _ _ _ _ joinedZero hlitOneBits htwoBits hJoinZeroPc hj4 hj6
    hj7 hj8 hj10 hj12 hj14 hj16 hj17 hj21 hj22 hj29 ?_
  intro afterOne hOnePc ho4 ho6 ho7 ho20 ho8 ho10 ho12 ho14 ho16 ho17 ho21 ho22
    ho29
  refine run_selectiveClauseJoinOne _ _ _ _ _ _ _ _ _ _ afterOne
    (selectiveClauseOrBits_node
      (clauseWireTwo harity state values decisionCode clauseIndex).state
      (clauseWireOne harity state values decisionCode clauseIndex).output
      (clauseWireTwo harity state values decisionCode clauseIndex).output |>.trans
      horOneBits)
    hfourBits hOnePc ho17 ho4 ho6 ho7 ho8 ho10 ho12 ho14 ho16 ho20 ho21 ho22
    ho29 ?_
  intro joinedOne hJoinOnePc hk4 hk6 hk7 hk8 hk10 hk12 hk14 hk16 hk17 hk21 hk22
    hk23 hk29 hk30
  refine run_selectiveClauseEmitCall
    (clauseWireTwo harity state values decisionCode clauseIndex).state
    (.or (clauseWireOne harity state values decisionCode clauseIndex).output
      (clauseWireTwo harity state values decisionCode clauseIndex).output)
    horderedTwo _ _ _ _ _ _ _ _ _ _ _ _ 1 joinedOne rfl
    ((selectiveClauseOrBits_input
      (clauseWireTwo harity state values decisionCode clauseIndex).state
      (clauseWireOne harity state values decisionCode clauseIndex).output
      (clauseWireTwo harity state values decisionCode
        clauseIndex).output).trans horOneBits)
    ((selectiveClauseOrBits_wire
      (clauseWireTwo harity state values decisionCode clauseIndex).state
      (clauseWireOne harity state values decisionCode clauseIndex).output
      (clauseWireTwo harity state values decisionCode
        clauseIndex).output).trans horOneBits)
    hJoinOnePc hk4 hk6 hk7 hk23 hk8 hk10 hk12 hk14 hk16 hk17 hk21 hk22 hk29
    hk30 ?_
  intro emittedOne hEmitOnePc _he0 _he2 he4 he6 he7 he20 he8 he10 he12 he14
    he16 he17 he21 he22 he29 he30
  refine run_selectiveClausePhaseOne _ _ _ _ _ _ _ _ _ _ emittedOne
    ((selectiveClauseOrBits_output
      (clauseWireTwo harity state values decisionCode clauseIndex).state
      (clauseWireOne harity state values decisionCode clauseIndex).output
      (clauseWireTwo harity state values decisionCode
        clauseIndex).output).trans horOneBits)
    hfourBits hEmitOnePc he30 he4 he6 he7 he8 he10 he12 he14 he16 he17 he21
    he20 he29 ?_
  intro phasedOne hPhaseOnePc hq4 hq6 hq7 hq8 hq10 hq12 hq14 hq16 hq17 hq21
    hq22 hq29
  refine run_selectiveClauseLiteralStep harity
    (clauseWireOr harity state values decisionCode clauseIndex).state values
    decisionCode clauseIndex 2
    (selectiveClauseOf literalArity harity decisionCode clauseIndex 2) hlitTwo
    horderedOr _ _ _ _ _ phasedOne hlitTwoBits htwoBits hPhaseOnePc hq4 hq6 hq7
    hq8 hq10 hq12 hq14 hq16 hq17 hq21 hq22 hq29 ?_
  intro afterTwo hTwoPc ht4 ht6 ht7 ht20 ht8 ht10 ht12 ht14 ht16 ht17 ht21 ht22
    ht29
  refine run_selectiveClauseJoinTwo _ _ _ _ _ _ _ _ _ _ afterTwo
    ((selectiveClauseOrBits_node
      (clauseWireThree harity state values decisionCode clauseIndex).state
      (clauseWireOr harity state values decisionCode clauseIndex).output
      (clauseWireThree harity state values decisionCode
        clauseIndex).output).trans horTwoBits)
    hfourBits hTwoPc ht17 ht4 ht6 ht7 ht8 ht10 ht12 ht14 ht16 ht20 ht21 ht22
    ht29 ?_
  intro joinedTwo hJoinTwoPc hm4 hm6 hm7 hm8 hm10 hm12 hm14 hm16 hm17 hm21 hm22
    hm23 hm29 hm30
  refine run_selectiveClauseEmitCall
    (clauseWireThree harity state values decisionCode clauseIndex).state
    (.or (clauseWireOr harity state values decisionCode clauseIndex).output
      (clauseWireThree harity state values decisionCode clauseIndex).output)
    horderedThree _ _ _ _ _ _ _ _ _ _ _ _ 2 joinedTwo rfl
    ((selectiveClauseOrBits_input
      (clauseWireThree harity state values decisionCode clauseIndex).state
      (clauseWireOr harity state values decisionCode clauseIndex).output
      (clauseWireThree harity state values decisionCode
        clauseIndex).output).trans horTwoBits)
    ((selectiveClauseOrBits_wire
      (clauseWireThree harity state values decisionCode clauseIndex).state
      (clauseWireOr harity state values decisionCode clauseIndex).output
      (clauseWireThree harity state values decisionCode
        clauseIndex).output).trans horTwoBits)
    hJoinTwoPc hm4 hm6 hm7 hm23 hm8 hm10 hm12 hm14 hm16 hm17 hm21 hm22 hm29
    hm30 ?_
  intro emittedTwo hEmitTwoPc hf0 _hf2 _hf4 _hf6 _hf7 _hf20 _hf8 _hf10 _hf12
    _hf14 _hf16 _hf17 _hf21 _hf22 _hf29 hf30
  exact run_selectiveClausePhaseTwo emittedTwo
    ((selectiveClauseOrBits_code
      (clauseWireThree harity state values decisionCode clauseIndex).state
      (clauseWireOr harity state values decisionCode clauseIndex).output
      (clauseWireThree harity state values decisionCode
        clauseIndex).output).trans horTwoBits)
    hfourBits hEmitTwoPc hf30 hf0

/-! ## 6. The level premise, discharged -/

/-- **`SelectiveClauseRunner`, discharged.**  Level 11 owes nothing: the whole
clause compiler runs at its own ABI frame for every ordered state, every live
wire list and every decoded clause, with no premise at all. -/
def selectiveClauseRunner (n literalArity : ℕ) (harity : 0 < literalArity) :
    SelectiveClauseRunner n literalArity harity where
  bits := fun state values decisionCode clauseIndex =>
    selectiveClauseRunBits harity state values decisionCode clauseIndex
  fuel := fun state values decisionCode clauseIndex =>
    selectiveClauseRunFuel harity state values decisionCode clauseIndex
  executes := by
    intro state values decisionCode clauseIndex hordered entry hentryPc
      hentryInput
    exact run_selectiveClauseProgram harity state values decisionCode
      clauseIndex hordered entry hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
