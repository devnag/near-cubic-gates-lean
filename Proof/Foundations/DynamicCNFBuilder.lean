import Proof.Foundations.CanonicalBinaryProgram

/-!
# Executable canonical CNF list builder

The SAT opcode accepts the canonical `Encodable` code of a list of clauses.
This module closes the low-level dynamic-list seam: one fixed oracle-free
register program consumes a zero-terminated stream of clause codes in reverse
order and constructs exactly that canonical outer-list code.  Tseitin clause
generation remains a separate stage; no semantic formula-builder callback is
hidden here.
-/

namespace NearCubicWires.DynamicCNFBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-- Register ABI: `r0` is the tagged cursor and `r2` the canonical list
accumulator.  Registers `r3`--`r4` are scratch. -/
def cnfListBuilderProgram : NPOracleProgram :=
  [ .branchZero 0 6 1,
    .unpairRight 0 3 2,
    .unpairLeft 3 4 3,
    .unpairRight 3 0 4,
    .pair 4 2 2 5,
    .increment 2 0,
    .halt 2 ]

theorem cnfListBuilder_oracleFree :
    OracleFree cnfListBuilderProgram := by
  rfl

def cnfListBuilderFuel (clauseCodes : List ℕ) : ℕ :=
  6 * clauseCodes.length + 2

theorem encodeCodeList_suffix_le (listPrefix suffix : List ℕ) :
    encodeCodeList suffix ≤ encodeCodeList (listPrefix ++ suffix) := by
  induction listPrefix with
  | nil => rfl
  | cons value restPrefix ih =>
      simp only [List.cons_append, encodeCodeList]
      exact ih.trans <| by
        have := Nat.right_le_pair value
          (encodeCodeList (restPrefix ++ suffix))
        omega

theorem encodeTaggedList_tail_le (value : ℕ) (rest : List ℕ) :
    encodeTaggedList rest ≤ encodeTaggedList (value :: rest) := by
  simp only [encodeTaggedList]
  exact
    (Nat.right_le_pair value (encodeTaggedList rest)).trans <|
      Nat.right_le_pair 1 (Nat.pair value (encodeTaggedList rest))

theorem encodeCodeList_map_encode
    {α : Type} [Encodable α] (values : List α) :
    encodeCodeList (values.map Encodable.encode) =
      Encodable.encode values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, encodeCodeList, Encodable.encode_list_cons]
      rw [ih]

private theorem boundedWrite_eq
    {maximumBits register value : ℕ} {state : NPOracleState}
    (hvalue : natBitLength value ≤ maximumBits) :
    state.boundedWrite maximumBits register value =
      some (state.write register value) := by
  simp [NPOracleState.boundedWrite, hvalue]

private theorem run_branchZero_step
    {maximumBits fuel : ℕ} {state : NPOracleState}
    (hpc : state.pc = 0) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        (state.jump (if state.registers 0 = 0 then 6 else 1)) := by
  have hat :
      cnfListBuilderProgram[0]? = some (.branchZero 0 6 1) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]

private theorem run_cursor_payload
    {maximumBits fuel value : ℕ} {state : NPOracleState}
    (hpc : state.pc = 1)
    (hvalue : (Nat.unpair (state.registers 0)).2 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        ((state.write 3 value).jump 2) := by
  have hat :
      cnfListBuilderProgram[1]? = some (.unpairRight 0 3 2) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

private theorem run_unpairLeft_payload
    {maximumBits fuel value : ℕ} {state : NPOracleState}
    (hpc : state.pc = 2)
    (hvalue : (Nat.unpair (state.registers 3)).1 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        ((state.write 4 value).jump 3) := by
  have hat :
      cnfListBuilderProgram[2]? = some (.unpairLeft 3 4 3) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

private theorem run_unpairRight_payload
    {maximumBits fuel value : ℕ} {state : NPOracleState}
    (hpc : state.pc = 3)
    (hvalue : (Nat.unpair (state.registers 3)).2 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        ((state.write 0 value).jump 4) := by
  have hat :
      cnfListBuilderProgram[3]? = some (.unpairRight 3 0 4) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

private theorem run_pair_step
    {maximumBits fuel value : ℕ} {state : NPOracleState}
    (hpc : state.pc = 4)
    (hvalue : Nat.pair (state.registers 4) (state.registers 2) = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        ((state.write 2 value).jump 5) := by
  have hat :
      cnfListBuilderProgram[4]? = some (.pair 4 2 2 5) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

private theorem run_increment_step
    {maximumBits fuel value : ℕ} {state : NPOracleState}
    (hpc : state.pc = 5)
    (hvalue : state.registers 2 + 1 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits (fuel + 1) state =
      runNPOracleProgram cnfListBuilderProgram maximumBits fuel
        ((state.write 2 value).jump 0) := by
  have hat :
      cnfListBuilderProgram[5]? = some (.increment 2 0) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp only
  rw [hvalue, boundedWrite_eq hbits]

private theorem run_halt_step
    {maximumBits : ℕ} {state : NPOracleState}
    (hpc : state.pc = 6)
    (hbits : natBitLength (state.registers 2) ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits 1 state =
      some (state.registers 2) := by
  have hat : cnfListBuilderProgram[6]? = some (.halt 2) := by
    rfl
  simp only [runNPOracleProgram]
  rw [hpc, hat]
  simp [hbits]

/-- Exact execution from a loop state.  `sourceBound` and `outputBound` are
numeric (not bit-length) bounds, which lets every unpair and partial list
accumulator reuse one stable register-width proof. -/
theorem run_cnfListBuilder_from
    (clauseCodes accumulator : List ℕ)
    {maximumBits sourceBound outputBound : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcursor : state.registers 0 = encodeTaggedList clauseCodes)
    (haccumulator : state.registers 2 = encodeCodeList accumulator)
    (hsource :
      encodeTaggedList clauseCodes ≤ sourceBound)
    (houtput :
      encodeCodeList (clauseCodes.reverse ++ accumulator) ≤ outputBound)
    (hbits :
      natBitLength (max sourceBound outputBound) ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits
        (cnfListBuilderFuel clauseCodes) state =
      some (encodeCodeList (clauseCodes.reverse ++ accumulator)) := by
  induction clauseCodes generalizing accumulator state with
  | nil =>
      rw [show cnfListBuilderFuel [] = 1 + 1 by rfl]
      rw [run_branchZero_step hpc]
      rw [hcursor]
      simp only [encodeTaggedList, if_pos]
      have houtputBits :
          natBitLength (encodeCodeList accumulator) ≤ maximumBits :=
        (natBitLength_mono
          (houtput.trans (Nat.le_max_right _ _))).trans hbits
      rw [run_halt_step (state := state.jump 6) (by rfl) (by
        simpa [NPOracleState.jump, haccumulator] using houtputBits)]
      simp [NPOracleState.jump, haccumulator]
  | cons clauseCode rest ih =>
      let payload := Nat.pair clauseCode (encodeTaggedList rest)
      let nextAccumulator := clauseCode :: accumulator
      have hcursorNonzero :
          encodeTaggedList (clauseCode :: rest) ≠ 0 := by
        have hpositive : 0 < Nat.pair 1 payload :=
          lt_of_lt_of_le (by omega) (Nat.left_le_pair 1 payload)
        simpa only [encodeTaggedList, payload] using hpositive.ne'
      have hpayload :
          payload ≤ sourceBound := by
        have houter :
            payload ≤ encodeTaggedList (clauseCode :: rest) := by
          simp only [encodeTaggedList, payload]
          exact Nat.right_le_pair 1 payload
        exact houter.trans hsource
      have hhead : clauseCode ≤ sourceBound := by
        exact (Nat.left_le_pair clauseCode
          (encodeTaggedList rest)).trans hpayload
      have htail : encodeTaggedList rest ≤ sourceBound := by
        exact (Nat.right_le_pair clauseCode
          (encodeTaggedList rest)).trans hpayload
      have hnextAccumulator :
          encodeCodeList nextAccumulator ≤ outputBound := by
        have hremaining :
            encodeCodeList (rest.reverse ++ nextAccumulator) ≤ outputBound := by
          simpa [nextAccumulator, List.reverse_cons,
            List.append_assoc] using houtput
        have hsuffix :
            encodeCodeList nextAccumulator ≤
              encodeCodeList (rest.reverse ++ nextAccumulator) :=
          encodeCodeList_suffix_le rest.reverse nextAccumulator
        exact hsuffix.trans hremaining
      have hpair :
          Nat.pair clauseCode (encodeCodeList accumulator) ≤ outputBound := by
        change
          Nat.pair clauseCode (encodeCodeList accumulator) + 1 ≤
              outputBound at hnextAccumulator
        omega
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
      rw [show cnfListBuilderFuel (clauseCode :: rest) =
        (cnfListBuilderFuel rest + 5) + 1 by
          simp [cnfListBuilderFuel]
          omega]
      rw [run_branchZero_step hpc]
      rw [hcursor, if_neg hcursorNonzero]
      let state1 := state.jump 1
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest + 5) state1 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      let state2 := (state1.write 3 payload).jump 2
      rw [show cnfListBuilderFuel rest + 5 =
        (cnfListBuilderFuel rest + 4) + 1 by omega]
      rw [run_cursor_payload (state := state1)
        (value := payload) (by rfl)
        (by simp [state1, hcursor, payload, encodeTaggedList])
        (hsourceBits payload hpayload)]
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest + 4) state2 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      let state3 := (state2.write 4 clauseCode).jump 3
      rw [show cnfListBuilderFuel rest + 4 =
        (cnfListBuilderFuel rest + 3) + 1 by omega]
      rw [run_unpairLeft_payload (state := state2)
        (value := clauseCode) (by rfl)
        (by simp [state2, state1, payload])
        (hsourceBits clauseCode hhead)]
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest + 3) state3 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      let state4 := (state3.write 0 (encodeTaggedList rest)).jump 4
      rw [show cnfListBuilderFuel rest + 3 =
        (cnfListBuilderFuel rest + 2) + 1 by omega]
      rw [run_unpairRight_payload (state := state3)
        (value := encodeTaggedList rest) (by rfl)
        (by simp [state3, state2, state1, payload])
        (hsourceBits (encodeTaggedList rest) htail)]
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest + 2) state4 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      let paired := Nat.pair clauseCode (encodeCodeList accumulator)
      let state5 := (state4.write 2 paired).jump 5
      rw [show cnfListBuilderFuel rest + 2 =
        (cnfListBuilderFuel rest + 1) + 1 by omega]
      rw [run_pair_step (state := state4) (value := paired) (by rfl)
        (by simp [state4, state3, state2, state1, haccumulator, paired])
        (houtputBits paired (by simpa [paired] using hpair))]
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest + 1) state5 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      let state6 :=
        (state5.write 2 (encodeCodeList nextAccumulator)).jump 0
      rw [show cnfListBuilderFuel rest + 1 =
        cnfListBuilderFuel rest + 1 by rfl]
      rw [run_increment_step (state := state5)
        (value := encodeCodeList nextAccumulator) (by rfl)
        (by simp [state5, paired, nextAccumulator, encodeCodeList])
        (houtputBits (encodeCodeList nextAccumulator) hnextAccumulator)]
      change
        runNPOracleProgram cnfListBuilderProgram maximumBits
            (cnfListBuilderFuel rest) state6 =
          some
            (encodeCodeList
              ((clauseCode :: rest).reverse ++ accumulator))
      rw [show
        (clauseCode :: rest).reverse ++ accumulator =
          rest.reverse ++ nextAccumulator by
            simp [nextAccumulator, List.reverse_cons, List.append_assoc]]
      apply ih nextAccumulator
      · rfl
      · simp [state6, state5, state4, state3, state2, state1,
          NPOracleState.jump, NPOracleState.write]
      · simp [state6, nextAccumulator, NPOracleState.jump,
          NPOracleState.write]
      · exact htail
      · simpa [nextAccumulator, List.reverse_cons, List.append_assoc] using
          houtput

/-- The concrete builder returns the exact `EncodedCNF` code. -/
theorem run_cnfListBuilder (formula : EncodedCNF)
    {maximumBits sourceBound outputBound : ℕ}
    (hsource :
      encodeTaggedList
          ((formula.map Encodable.encode).reverse) ≤ sourceBound)
    (houtput : Encodable.encode formula ≤ outputBound)
    (hbits :
      natBitLength (max sourceBound outputBound) ≤ maximumBits) :
    runNPOracleProgram cnfListBuilderProgram maximumBits
        (cnfListBuilderFuel ((formula.map Encodable.encode).reverse))
        (initialNPOracleState (cnfVariableCount formula)
          (encodeTaggedList
            ((formula.map Encodable.encode).reverse))) =
      some (Encodable.encode formula) := by
  have run := run_cnfListBuilder_from
    ((formula.map Encodable.encode).reverse) []
    (sourceBound := sourceBound) (outputBound := outputBound)
    (initialNPOracleState (cnfVariableCount formula)
      (encodeTaggedList ((formula.map Encodable.encode).reverse)))
    (by rfl) (by simp [initialNPOracleState])
    (by simp [initialNPOracleState, encodeCodeList])
    hsource (by
      simpa [encodeCodeList_map_encode] using houtput) hbits
  simpa [encodeCodeList_map_encode] using run

/-! ## Verified handoff to the actual SAT opcode -/

/-- The second linked stage queries exactly the formula code produced in
register zero and returns the oracle bit. -/
def canonicalSatProgram : NPOracleProgram :=
  [.sat 0 2 1, .halt 2]

theorem run_canonicalSatProgram (inputLength formulaCode maximumBits : ℕ)
    (hbitsPositive : 1 ≤ maximumBits)
    (hformulaBits : natBitLength formulaCode ≤ maximumBits) :
    runNPOracleProgram canonicalSatProgram maximumBits 2
        (initialNPOracleState inputLength formulaCode) =
      some (encodedSat formulaCode).toNat := by
  have hformulaLog : Nat.log 2 formulaCode < maximumBits := by
    unfold natBitLength at hformulaBits
    omega
  have hresultLog :
      Nat.log 2 (encodedSat formulaCode).toNat < maximumBits := by
    cases encodedSat formulaCode <;> simp
    all_goals omega
  simp [canonicalSatProgram, runNPOracleProgram, initialNPOracleState,
    NPOracleState.boundedWrite, natBitLength, hformulaLog, hresultLog]

def cnfSatProgram : NPOracleProgram :=
  linkPrograms cnfListBuilderProgram canonicalSatProgram

def cnfSatFuel (clauseCodes : List ℕ) : ℕ :=
  linkFuel canonicalSatProgram
    (cnfListBuilderFuel clauseCodes) 2

/-- End-to-end execution of the fixed list builder followed by the concrete SAT
instruction.  The input is the structural reverse stream, not a precomputed
answer or a semantic callback. -/
theorem run_cnfSatProgram (formula : EncodedCNF)
    {maximumBits sourceBound outputBound : ℕ}
    (hsource :
      encodeTaggedList
          ((formula.map Encodable.encode).reverse) ≤ sourceBound)
    (houtput : Encodable.encode formula ≤ outputBound)
    (hbits :
      natBitLength (max sourceBound outputBound) ≤ maximumBits)
    (hinputBits :
      natBitLength (cnfVariableCount formula) ≤ maximumBits)
    (hbitsPositive : 1 ≤ maximumBits) :
    runNPOracleProgram cnfSatProgram maximumBits
        (cnfSatFuel ((formula.map Encodable.encode).reverse))
        (initialNPOracleState (cnfVariableCount formula)
          (encodeTaggedList
            ((formula.map Encodable.encode).reverse))) =
      some (encodedSat (Encodable.encode formula)).toNat := by
  apply run_linkPrograms hbitsPositive hinputBits
  · exact run_cnfListBuilder formula hsource houtput hbits
  · exact run_canonicalSatProgram
      (cnfVariableCount formula) (Encodable.encode formula) maximumBits
      hbitsPositive
      ((natBitLength_mono
        (houtput.trans (Nat.le_max_right _ _))).trans hbits)

end NearCubicWires.DynamicCNFBuilder
