import Proof.Supplier.SelectiveCountCasesRun
import Proof.MachineModel.TotalSelectiveVerifierRowsProgram

/-!
# The fixed-count sub-compiler's run

`totalSelectiveFixedCountProgram` is the `2944`-instruction stream the outermost
controller calls once per candidate node count.  It is a straight-line
controller of `69` instructions with three relocated callees: the
`1095`-instruction fixed-count grammar compiler, the `1791`-instruction
verifier-row scheduler, and the `18`-instruction append transition.

This module executes that controller, discharging
`SelectiveFixedCountProgramRunner` from two named level
premises one level further down.
-/

namespace NearCubicWires.TotalSelectiveFixedCountProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveClausesGuardedProgram
open NearCubicWires.TotalSelectiveVerifierRowsProgram

set_option maxRecDepth 100000 in
@[simp] private theorem totalSelectiveVerifierRowsProgram_length :
    totalSelectiveVerifierRowsProgram.length = 1791 := by
  rfl

def totalSelectiveFixedCountProgram : NPOracleProgram :=
  selectiveFixedCountControllerProgram 69 1164 2955 ++
    selectiveFixedCountGrammarProgram.map
      (callableInstruction 69 1000 50 30) ++
    totalSelectiveVerifierRowsProgram.map
      (callableInstruction 1164 30000 50 50) ++
    selectiveEmitProgram.map
      (callableInstruction 2955 65000 50 67)

structure SelectiveFixedCountProgramRunner (program : NPOracleProgram)
    (outputs : List ℕ) (width count bound : ℕ) where
  bits : SelectiveState (descriptionWidth width bound) → Fin bound → ℕ
  fuel : SelectiveState (descriptionWidth width bound) → Fin bound → ℕ
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (candidate : Fin bound), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveFixedCountInput (selectiveStateCode state)
        (encodeTaggedList outputs) (structuralInputArity width bound)
        (structuralRowWidth width bound) (width + bound + 1) width count bound
        candidate.val →
    runNPOracleProgram program (bits state candidate)
        (fuel state candidate) entry =
      some
        (selectiveWireCode
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate))

/-! ## 1. Decoding the fixed 2944-instruction stream -/

private theorem totalSelectiveFixedCountProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveFixedCountControllerProgram 69 1164 2955)[pc]? =
        some instruction) :
    totalSelectiveFixedCountProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveFixedCountControllerProgram 69 1164 2955).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFixedCountControllerProgram_length] at hpc
  simp only [totalSelectiveFixedCountProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length,
      totalSelectiveVerifierRowsProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveFixedCountControllerProgram_length]
    omega)]
  exact hlookup

theorem totalSelectiveFixedCountProgram_grammarCallable :
    ProgramCallableAt totalSelectiveFixedCountProgram
      selectiveFixedCountGrammarProgram 69 1000 50 30 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveFixedCountGrammarProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFixedCountGrammarProgram_length] at hpc
  simp only [totalSelectiveFixedCountProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length,
      totalSelectiveVerifierRowsProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveFixedCountControllerProgram_length]
    omega)]
  simp only [selectiveFixedCountControllerProgram_length]
  rw [show 69 + pc - 69 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem totalSelectiveFixedCountProgram_rowsCallable :
    ProgramCallableAt totalSelectiveFixedCountProgram totalSelectiveVerifierRowsProgram
      1164 30000 50 50 := by
  intro pc instruction hlookup
  have hpc : pc < totalSelectiveVerifierRowsProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [totalSelectiveVerifierRowsProgram_length] at hpc
  simp only [totalSelectiveFixedCountProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length,
      totalSelectiveVerifierRowsProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveFixedCountControllerProgram_length,
    selectiveFixedCountGrammarProgram_length]
  rw [show 1164 + pc - (69 + 1095) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem totalSelectiveFixedCountProgram_emitCallable :
    ProgramCallableAt totalSelectiveFixedCountProgram selectiveEmitProgram
      2955 65000 50 67 := by
  intro pc instruction hlookup
  simp only [totalSelectiveFixedCountProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountControllerProgram_length,
      selectiveFixedCountGrammarProgram_length,
      totalSelectiveVerifierRowsProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveFixedCountControllerProgram_length,
    selectiveFixedCountGrammarProgram_length,
    totalSelectiveVerifierRowsProgram_length]
  rw [show 2955 + pc - (69 + 1095 + 1791) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 2. The controller's three stages, at the typed level -/

/-- The candidate's compiled grammar wire. -/
private def selectiveFixedCountGrammarWire (width bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileExpr state (fixedCountGrammarExpr (n := width) candidate)

/-- The candidate's compiled verifier-row wire. -/
private def selectiveFixedCountRowsWire (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileTableVerifierRows outputs width count bound
    (candidate.val + 1) candidate.isLt
    (selectiveFixedCountGrammarWire width bound state candidate).state
    (List.range (2 ^ width))

private theorem selectiveCompileTableFixedCount_eq (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) :
    selectiveCompileTableFixedCount outputs width count bound state candidate =
      selectiveAnd
        (selectiveFixedCountRowsWire outputs width count bound state
          candidate).state
        (selectiveFixedCountGrammarWire width bound state candidate).output
        (selectiveFixedCountRowsWire outputs width count bound state
          candidate).output := rfl

private theorem selectiveFixedCountRowsWire_ordered (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveFixedCountRowsWire outputs width count bound state
        candidate).state :=
  selectiveCompileTableVerifierRows_ordered outputs width count bound
    (candidate.val + 1) candidate.isLt (List.range (2 ^ width)) _
    (selectiveCompileExpr_ordered state _ hordered)

/-! ## 4. The controller's trace

Every relocated call below goes through the one shared call-frame lemma
`run_selectiveRelocatedCall`; only the straight-line register plumbing between
calls is specific to this level. -/

set_option maxRecDepth 300000 in
-- The relocated guarded rows stream has a deeper concrete program spine.
set_option maxHeartbeats 3200000 in
-- Sixty-nine straight-line controller steps around three relocated callees.
private theorem run_totalSelectiveFixedCountProgram_of_wires (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound)
    (grammar rows : SelectiveWire (descriptionWidth width bound))
    (maximumBits grammarFuel rowsFuel emitFuel : ℕ) (entry : NPOracleState)
    (hrowsOrdered : selectiveStateOrdered rows.state)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (rows.state.target - rows.state.next)
          (selectiveSelectedCode rows.state.selected))
    (hgrammarRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFixedCountGrammarInput (selectiveStateCode state)
          (structuralInputArity width bound) (structuralRowWidth width bound)
          (width + bound + 1) width bound candidate.val →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          grammarFuel frame =
        some (selectiveWireCode grammar))
    (hrowsRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveVerifierRowsInput (selectiveStateCode grammar.state)
          (encodeTaggedList outputs) (structuralInputArity width bound)
          (structuralRowWidth width bound) (width + bound + 1) width count
          (candidate.val + 1) →
      runNPOracleProgram totalSelectiveVerifierRowsProgram maximumBits rowsFuel
          frame =
        some (selectiveWireCode rows))
    (hrequestBits :
      natBitLength
          (selectiveFixedCountInput (selectiveStateCode state)
            (encodeTaggedList outputs) (structuralInputArity width bound)
            (structuralRowWidth width bound) (width + bound + 1) width count
            bound candidate.val) ≤
        maximumBits)
    (hgrammarRequestBits :
      natBitLength
          (selectiveFixedCountGrammarInput (selectiveStateCode state)
            (structuralInputArity width bound) (structuralRowWidth width bound)
            (width + bound + 1) width bound candidate.val) ≤
        maximumBits)
    (hgrammarWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode grammar)) ≤ maximumBits)
    (hrowsRequestBits :
      natBitLength
          (selectiveVerifierRowsInput (selectiveStateCode grammar.state)
            (encodeTaggedList outputs) (structuralInputArity width bound)
            (structuralRowWidth width bound) (width + bound + 1) width count
            (candidate.val + 1)) ≤
        maximumBits)
    (hrowsWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode rows)) ≤ maximumBits)
    (hemitInputBits :
      natBitLength
          (selectiveEmitInput (rows.state.target - rows.state.next)
            rows.state.next (selectiveSelectedCode rows.state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (.and grammar.output rows.output))) ≤
        maximumBits)
    (hemitWireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveAnd rows.state grammar.output rows.output))) ≤
        maximumBits)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveFixedCountInput (selectiveStateCode state)
          (encodeTaggedList outputs) (structuralInputArity width bound)
          (structuralRowWidth width bound) (width + bound + 1) width count
          bound candidate.val) :
    runNPOracleProgram totalSelectiveFixedCountProgram maximumBits
        (30 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) entry =
      some
        (selectiveWireCode
          (selectiveAnd rows.state grammar.output rows.output)) := by
  have hstateForm : ∀ candidateState : SelectiveState (descriptionWidth width bound),
      selectiveStateCode candidateState =
        Nat.pair (candidateState.target - candidateState.next)
          (Nat.pair candidateState.next
            (selectiveSelectedCode candidateState.selected)) := fun _ => rfl
  have hnodeForm :
      rawCircuitNodeCode (n := descriptionWidth width bound)
          (.and grammar.output rows.output) =
        Nat.pair 3
          (Nat.pair (descriptionWidth width bound + grammar.output)
            (descriptionWidth width bound + rows.output)) := rfl
  have hemitForm :
      selectiveEmitInput (rows.state.target - rows.state.next) rows.state.next
          (selectiveSelectedCode rows.state.selected)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output)) =
        Nat.pair (selectiveStateCode rows.state)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output)) := rfl
  -- request components
  have hrequestFlat := hrequestBits
  simp only [selectiveFixedCountInput] at hrequestFlat
  have hstateBits := natBitLength_pair_left hrequestFlat
  have hone := natBitLength_pair_right hrequestFlat
  have htableBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have harityBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hrowWidthBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hfieldLimitBits := natBitLength_pair_left hfour
  have hfive := natBitLength_pair_right hfour
  have hwidthBits := natBitLength_pair_left hfive
  have hsix := natBitLength_pair_right hfive
  have hcountBits := natBitLength_pair_left hsix
  have hseven := natBitLength_pair_right hsix
  have hboundBits := natBitLength_pair_left hseven
  have hcandidateBits := natBitLength_pair_right hseven
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left hnextSelectedBits
  have hselectedBits := natBitLength_pair_right hnextSelectedBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hboundBits
  -- grammar request components
  have hgrammarFlat := hgrammarRequestBits
  simp only [selectiveFixedCountGrammarInput] at hgrammarFlat
  have hgone := natBitLength_pair_right hgrammarFlat
  have hgtwo := natBitLength_pair_right hgone
  have hgthree := natBitLength_pair_right hgtwo
  have hgfour := natBitLength_pair_right hgthree
  have hgfive := natBitLength_pair_right hgfour
  -- grammar wire components
  have hgrammarWireFlat := natBitLength_pair_right hgrammarWireBits
  have hgrammarWireParts := hgrammarWireFlat
  simp only [selectiveWireCode] at hgrammarWireParts
  have hgrammarStateBits := natBitLength_pair_left hgrammarWireParts
  have hgrammarOutputBits := natBitLength_pair_right hgrammarWireParts
  have hgrammarStateFlat := hgrammarStateBits
  rw [hstateForm grammar.state] at hgrammarStateFlat
  have hgrammarRemainingBits := natBitLength_pair_left hgrammarStateFlat
  have hgrammarNextSelectedBits := natBitLength_pair_right hgrammarStateFlat
  have hgrammarNextBits := natBitLength_pair_left hgrammarNextSelectedBits
  have hgrammarSelectedBits := natBitLength_pair_right hgrammarNextSelectedBits
  -- rows request components
  have hrowsFlat := hrowsRequestBits
  simp only [selectiveVerifierRowsInput] at hrowsFlat
  have hrone := natBitLength_pair_right hrowsFlat
  have hrtwo := natBitLength_pair_right hrone
  have hrthree := natBitLength_pair_right hrtwo
  have hrfour := natBitLength_pair_right hrthree
  have hrfive := natBitLength_pair_right hrfour
  have hrsix := natBitLength_pair_right hrfive
  have hnodeCountBits := natBitLength_pair_right hrsix
  -- rows wire components
  have hrowsWireFlat := natBitLength_pair_right hrowsWireBits
  have hrowsWireParts := hrowsWireFlat
  simp only [selectiveWireCode] at hrowsWireParts
  have hrowsStateBits := natBitLength_pair_left hrowsWireParts
  have hrowsOutputBits := natBitLength_pair_right hrowsWireParts
  have hrowsStateFlat := hrowsStateBits
  rw [hstateForm rows.state] at hrowsStateFlat
  have hrowsRemainingBits := natBitLength_pair_left hrowsStateFlat
  have hrowsNextSelectedBits := natBitLength_pair_right hrowsStateFlat
  have hrowsNextBits := natBitLength_pair_left hrowsNextSelectedBits
  have hrowsSelectedBits := natBitLength_pair_right hrowsNextSelectedBits
  -- emit components
  have hemitFlat := hemitInputBits
  rw [hemitForm] at hemitFlat
  have hnodeBits := natBitLength_pair_right hemitFlat
  have hnodeFlat := hnodeBits
  rw [hnodeForm] at hnodeFlat
  have hthreeBits := natBitLength_pair_left hnodeFlat
  have hchildrenBits := natBitLength_pair_right hnodeFlat
  have hleftChildBits := natBitLength_pair_left hchildrenBits
  have hrightChildBits := natBitLength_pair_right hchildrenBits
  have hemitWireFlat := natBitLength_pair_right hemitWireBits
  -- the emit callee's own width envelope
  have hemitOutput :
      selectiveEmitOutput (rows.state.target - rows.state.next) rows.state.next
          (selectiveSelectedCode rows.state.selected)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output)) =
        selectiveWireCode
          (selectiveAnd rows.state grammar.output rows.output) :=
    selectiveEmitOutput_eq_wireCode rows.state
      (.and grammar.output rows.output) hrowsOrdered
  have hemitCalleeBits :
      selectiveEmitBits (rows.state.target - rows.state.next) rows.state.next
          (selectiveSelectedCode rows.state.selected)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output)) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (rows.state.target - rows.state.next)
          rows.state.next (selectiveSelectedCode rows.state.selected)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output)))
        (selectiveEmitOutput (rows.state.target - rows.state.next)
          rows.state.next (selectiveSelectedCode rows.state.selected)
          (rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output))) with hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact hemitWireFlat
    · rw [max_eq_left hle]
      exact hemitInputBits
  -- stage one: parse the request
  rw [show 30 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (29 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveFixedCountInput]) hstateBits]
  rw [show 29 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (28 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs) <|
        Nat.pair (structuralInputArity width bound) <|
          Nat.pair (structuralRowWidth width bound) <|
            Nat.pair (width + bound + 1) <|
              Nat.pair width <|
                Nat.pair count (Nat.pair bound candidate.val))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveFixedCountInput])
    hone]
  rw [show 28 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (27 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm state])
    hremainingBits]
  rw [show 27 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (26 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair state.next (selectiveSelectedCode state.selected))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm state])
    hnextSelectedBits]
  rw [show 26 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (25 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 25 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (24 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 24 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (23 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := encodeTaggedList outputs)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits]
  rw [show 23 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (22 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (structuralInputArity width bound) <|
        Nat.pair (structuralRowWidth width bound) <|
          Nat.pair (width + bound + 1) <|
            Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 22 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (21 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := structuralInputArity width bound)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 21 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (20 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (structuralRowWidth width bound) <|
        Nat.pair (width + bound + 1) <|
          Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 20 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (19 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := structuralRowWidth width bound)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [show 19 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (18 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (width + bound + 1) <|
        Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 18 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (17 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := width + bound + 1)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [show 17 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (16 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [show 16 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (15 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := width)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 15 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (14 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair count (Nat.pair bound candidate.val))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsix]
  rw [show 14 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (13 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := count)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 16) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [show 13 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (12 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction (value := Nat.pair bound candidate.val)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hseven]
  rw [show 12 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (11 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := bound)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hboundBits]
  rw [show 11 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (10 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_unpairRight_instruction (value := candidate.val)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcandidateBits]
  -- stage two: the grammar callee's request
  rw [show 10 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (9 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction (value := Nat.pair bound candidate.val)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 20) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgfive]
  rw [show 9 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (8 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value := Nat.pair width (Nat.pair bound candidate.val))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 21) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgfour]
  rw [show 8 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (7 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (width + bound + 1)
        (Nat.pair width (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgthree]
  rw [show 7 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (6 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (structuralRowWidth width bound) <|
        Nat.pair (width + bound + 1)
          (Nat.pair width (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgtwo]
  rw [show 6 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (5 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (structuralInputArity width bound) <|
        Nat.pair (structuralRowWidth width bound) <|
          Nat.pair (width + bound + 1)
            (Nat.pair width (Nat.pair bound candidate.val)))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hgone]
  rw [show 5 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (4 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (totalSelectiveFixedCountProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextSelectedBits]
  rw [show 4 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (3 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 26) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm state])
    hstateBits]
  rw [show 3 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (2 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      selectiveFixedCountGrammarInput (selectiveStateCode state)
        (structuralInputArity width bound) (structuralRowWidth width bound)
        (width + bound + 1) width bound candidate.val)
    (totalSelectiveFixedCountProgram_controllerAt (pc := 27) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        selectiveFixedCountGrammarInput])
    hgrammarRequestBits]
  rw [show 2 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (1 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2)))))) + 1 by
    omega]
  rw [run_set_instruction
    (totalSelectiveFixedCountProgram_controllerAt (pc := 28) rfl) rfl hzeroBits]
  rw [show 1 + (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) =
    (grammarFuel + (20 + (rowsFuel + (17 + (emitFuel + 2))))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveFixedCountProgram_controllerAt (pc := 29) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveFixedCountGrammarProgram)
    (calleeOutput := selectiveWireCode grammar)
    totalSelectiveFixedCountProgram_grammarCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hgrammarRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hgrammarWireBits
  · intro grammarHalt
    -- stage three: the verifier-row callee's request
    rw [show 20 + (rowsFuel + (17 + (emitFuel + 2))) =
      (19 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode grammar)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hgrammarWireFlat]
    rw [show 19 + (rowsFuel + (17 + (emitFuel + 2))) =
      (18 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode grammar.state)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 31) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hgrammarStateBits]
    rw [show 18 + (rowsFuel + (17 + (emitFuel + 2))) =
      (17 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairRight_instruction (value := grammar.output)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 32) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hgrammarOutputBits]
    rw [show 17 + (rowsFuel + (17 + (emitFuel + 2))) =
      (16 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := grammar.state.target - grammar.state.next)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 33) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm grammar.state])
      hgrammarRemainingBits]
    rw [show 16 + (rowsFuel + (17 + (emitFuel + 2))) =
      (15 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair grammar.state.next
          (selectiveSelectedCode grammar.state.selected))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 34) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm grammar.state])
      hgrammarNextSelectedBits]
    rw [show 15 + (rowsFuel + (17 + (emitFuel + 2))) =
      (14 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairLeft_instruction (value := grammar.state.next)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 35) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hgrammarNextBits]
    rw [show 14 + (rowsFuel + (17 + (emitFuel + 2))) =
      (13 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode grammar.state.selected)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 36) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hgrammarSelectedBits]
    rw [show 13 + (rowsFuel + (17 + (emitFuel + 2))) =
      (12 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_copy_instruction (value := candidate.val)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 37) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState])
      hcandidateBits]
    rw [show 12 + (rowsFuel + (17 + (emitFuel + 2))) =
      (11 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_increment_instruction (value := candidate.val + 1)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 38) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hnodeCountBits]
    rw [show 11 + (rowsFuel + (17 + (emitFuel + 2))) =
      (10 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction (value := Nat.pair count (candidate.val + 1))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 39) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState]) hrsix]
    rw [show 10 + (rowsFuel + (17 + (emitFuel + 2))) =
      (9 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair width (Nat.pair count (candidate.val + 1)))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 40) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState]) hrfive]
    rw [show 9 + (rowsFuel + (17 + (emitFuel + 2))) =
      (8 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (width + bound + 1)
          (Nat.pair width (Nat.pair count (candidate.val + 1))))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 41) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState]) hrfour]
    rw [show 8 + (rowsFuel + (17 + (emitFuel + 2))) =
      (7 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (structuralRowWidth width bound) <|
          Nat.pair (width + bound + 1)
            (Nat.pair width (Nat.pair count (candidate.val + 1))))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 42) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState])
      hrthree]
    rw [show 7 + (rowsFuel + (17 + (emitFuel + 2))) =
      (6 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (structuralInputArity width bound) <|
          Nat.pair (structuralRowWidth width bound) <|
            Nat.pair (width + bound + 1)
              (Nat.pair width (Nat.pair count (candidate.val + 1))))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 43) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState]) hrtwo]
    rw [show 6 + (rowsFuel + (17 + (emitFuel + 2))) =
      (5 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (encodeTaggedList outputs) <|
          Nat.pair (structuralInputArity width bound) <|
            Nat.pair (structuralRowWidth width bound) <|
              Nat.pair (width + bound + 1)
                (Nat.pair width (Nat.pair count (candidate.val + 1))))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 44) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState]) hrone]
    rw [show 5 + (rowsFuel + (17 + (emitFuel + 2))) =
      (4 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair grammar.state.next
          (selectiveSelectedCode grammar.state.selected))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 45) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hgrammarNextSelectedBits]
    rw [show 4 + (rowsFuel + (17 + (emitFuel + 2))) =
      (3 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction (value := selectiveStateCode grammar.state)
      (totalSelectiveFixedCountProgram_controllerAt (pc := 46) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm grammar.state])
      hgrammarStateBits]
    rw [show 3 + (rowsFuel + (17 + (emitFuel + 2))) =
      (2 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        selectiveVerifierRowsInput (selectiveStateCode grammar.state)
          (encodeTaggedList outputs) (structuralInputArity width bound)
          (structuralRowWidth width bound) (width + bound + 1) width count
          (candidate.val + 1))
      (totalSelectiveFixedCountProgram_controllerAt (pc := 47) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          selectiveVerifierRowsInput])
      hrowsRequestBits]
    rw [show 2 + (rowsFuel + (17 + (emitFuel + 2))) =
      (1 + (rowsFuel + (17 + (emitFuel + 2)))) + 1 by omega]
    rw [run_set_instruction
      (totalSelectiveFixedCountProgram_controllerAt (pc := 48) rfl) rfl hzeroBits]
    rw [show 1 + (rowsFuel + (17 + (emitFuel + 2))) =
      (rowsFuel + (17 + (emitFuel + 2))) + 1 by omega]
    rw [run_branchZero_instruction
      (totalSelectiveFixedCountProgram_controllerAt (pc := 49) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveRelocatedCall
      (source := totalSelectiveVerifierRowsProgram)
      (calleeOutput := selectiveWireCode rows)
      totalSelectiveFixedCountProgram_rowsCallable (by omega) ?_ ?_ ?_ ?_ ?_
    · rfl
    · intro frame hframePc hframeInput
      refine hrowsRun frame hframePc ?_
      rw [hframeInput]
      simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · exact hrowsWireBits
    · intro rowsHalt
      -- stage four: the single conjunction joining both outputs
      rw [show 17 + (emitFuel + 2) = (16 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairRight_instruction (value := selectiveWireCode rows)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 50) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hrowsWireFlat]
      rw [show 16 + (emitFuel + 2) = (15 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairLeft_instruction (value := selectiveStateCode rows.state)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 51) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
        hrowsStateBits]
      rw [show 15 + (emitFuel + 2) = (14 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairRight_instruction (value := rows.output)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 52) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
        hrowsOutputBits]
      rw [show 14 + (emitFuel + 2) = (13 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairLeft_instruction
        (value := rows.state.target - rows.state.next)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 53) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump,
            hstateForm rows.state])
        hrowsRemainingBits]
      rw [show 13 + (emitFuel + 2) = (12 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairRight_instruction
        (value :=
          Nat.pair rows.state.next
            (selectiveSelectedCode rows.state.selected))
        (totalSelectiveFixedCountProgram_controllerAt (pc := 54) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump,
            hstateForm rows.state])
        hrowsNextSelectedBits]
      rw [show 12 + (emitFuel + 2) = (11 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairLeft_instruction (value := rows.state.next)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 55) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hrowsNextBits]
      rw [show 11 + (emitFuel + 2) = (10 + (emitFuel + 2)) + 1 by omega]
      rw [run_unpairRight_instruction
        (value := selectiveSelectedCode rows.state.selected)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 56) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hrowsSelectedBits]
      rw [show 10 + (emitFuel + 2) = (9 + (emitFuel + 2)) + 1 by omega]
      rw [run_add_instruction
        (value := descriptionWidth width bound + grammar.output)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 57) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, relocateState,
            structuralInputArity])
        hleftChildBits]
      rw [show 9 + (emitFuel + 2) = (8 + (emitFuel + 2)) + 1 by omega]
      rw [run_add_instruction
        (value := descriptionWidth width bound + rows.output)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 58) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, relocateState,
            structuralInputArity])
        hrightChildBits]
      rw [show 8 + (emitFuel + 2) = (7 + (emitFuel + 2)) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          Nat.pair (descriptionWidth width bound + grammar.output)
            (descriptionWidth width bound + rows.output))
        (totalSelectiveFixedCountProgram_controllerAt (pc := 59) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
      rw [show 7 + (emitFuel + 2) = (6 + (emitFuel + 2)) + 1 by omega]
      rw [run_set_instruction
        (totalSelectiveFixedCountProgram_controllerAt (pc := 60) rfl) rfl
        hthreeBits]
      rw [show 6 + (emitFuel + 2) = (5 + (emitFuel + 2)) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and grammar.output rows.output))
        (totalSelectiveFixedCountProgram_controllerAt (pc := 61) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
        hnodeBits]
      rw [show 5 + (emitFuel + 2) = (4 + (emitFuel + 2)) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          Nat.pair rows.state.next
            (selectiveSelectedCode rows.state.selected))
        (totalSelectiveFixedCountProgram_controllerAt (pc := 62) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        hrowsNextSelectedBits]
      rw [show 4 + (emitFuel + 2) = (3 + (emitFuel + 2)) + 1 by omega]
      rw [run_pair_instruction (value := selectiveStateCode rows.state)
        (totalSelectiveFixedCountProgram_controllerAt (pc := 63) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump,
            hstateForm rows.state])
        hrowsStateBits]
      rw [show 3 + (emitFuel + 2) = (2 + (emitFuel + 2)) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          selectiveEmitInput (rows.state.target - rows.state.next)
            rows.state.next (selectiveSelectedCode rows.state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (.and grammar.output rows.output)))
        (totalSelectiveFixedCountProgram_controllerAt (pc := 64) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hemitForm])
        hemitInputBits]
      rw [show 2 + (emitFuel + 2) = (1 + (emitFuel + 2)) + 1 by omega]
      rw [run_set_instruction
        (totalSelectiveFixedCountProgram_controllerAt (pc := 65) rfl) rfl hzeroBits]
      rw [show 1 + (emitFuel + 2) = (emitFuel + 2) + 1 by omega]
      rw [run_branchZero_instruction
        (totalSelectiveFixedCountProgram_controllerAt (pc := 66) rfl) rfl]
      simp only [ite_self]
      rw [hemitFuel]
      refine run_selectiveRelocatedCall
        (source := selectiveEmitProgram)
        (calleeOutput :=
          selectiveWireCode (selectiveAnd rows.state grammar.output rows.output))
        totalSelectiveFixedCountProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
      · rfl
      · intro frame hframePc hframeInput
        refine run_bits_mono
          (run_selectiveEmitProgram_eq_emit rows.state
            (.and grammar.output rows.output) hrowsOrdered frame hframePc ?_)
          hemitCalleeBits
        rw [hframeInput]
        simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · exact hemitWireBits
      · intro emitHalt
        rw [show (2 : ℕ) = (0 + 1) + 1 by omega]
        rw [run_unpairRight_instruction
          (value :=
            selectiveWireCode
              (selectiveAnd rows.state grammar.output rows.output))
          (totalSelectiveFixedCountProgram_controllerAt (pc := 67) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hemitWireFlat]
        exact run_halt_instruction (fuel := 0)
          (totalSelectiveFixedCountProgram_controllerAt (pc := 68) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hemitWireFlat

/-! ## 5. The level runner -/

/-- Register width of one fixed-count sub-compiler run. -/
def selectiveFixedCountLevelBits (outputs : List ℕ) (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : ℕ :=
  max
    (natBitLength
      (selectiveFixedCountInput (selectiveStateCode state)
        (encodeTaggedList outputs) (structuralInputArity width bound)
        (structuralRowWidth width bound) (width + bound + 1) width count bound
        candidate.val)) <|
    max
      (natBitLength
        (selectiveFixedCountGrammarInput (selectiveStateCode state)
          (structuralInputArity width bound) (structuralRowWidth width bound)
          (width + bound + 1) width bound candidate.val)) <|
      max
        (natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveFixedCountGrammarWire width bound state candidate)))) <|
        max
          (natBitLength
            (selectiveVerifierRowsInput
              (selectiveStateCode
                (selectiveFixedCountGrammarWire width bound state
                  candidate).state)
              (encodeTaggedList outputs) (structuralInputArity width bound)
              (structuralRowWidth width bound) (width + bound + 1) width count
              (candidate.val + 1))) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate)))) <|
            max
              (natBitLength
                (selectiveEmitInput
                  ((selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.target -
                    (selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.next)
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate).state.next
                  (selectiveSelectedCode
                    (selectiveFixedCountRowsWire outputs width count bound state
                      candidate).state.selected)
                  (rawCircuitNodeCode (n := descriptionWidth width bound)
                    (.and
                      (selectiveFixedCountGrammarWire width bound state
                        candidate).output
                      (selectiveFixedCountRowsWire outputs width count bound
                        state candidate).output)))) <|
              max
                (natBitLength
                  (Nat.pair 0
                    (selectiveWireCode
                      (selectiveCompileTableFixedCount outputs width count bound
                        state candidate)))) <|
                max (grammarRunner.bits state candidate)
                  (rowsRunner.bits
                    (selectiveFixedCountGrammarWire width bound state
                      candidate).state (candidate.val + 1))

/-- Interpreter fuel of one fixed-count sub-compiler run. -/
def selectiveFixedCountLevelFuel (outputs : List ℕ) (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) : ℕ :=
  30 +
    (grammarRunner.fuel state candidate +
      (20 +
        (rowsRunner.fuel
            (selectiveFixedCountGrammarWire width bound state candidate).state
            (candidate.val + 1) +
          (17 +
            (selectiveEmitFuel
                ((selectiveFixedCountRowsWire outputs width count bound state
                    candidate).state.target -
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate).state.next)
                (selectiveSelectedCode
                  (selectiveFixedCountRowsWire outputs width count bound state
                    candidate).state.selected) +
              2)))))

set_option maxHeartbeats 800000 in
-- Discharging one level premise from the two below it.
/-- **The fixed-count level, from the two levels below it.**  A grammar runner
and a verifier-row runner build the fixed-count runner the outermost controller
consumes, so `run_selectiveCountCasesProgram` holds from those two premises. -/
def selectiveFixedCountRunnerOfLevels (outputs : List ℕ)
    (width count bound : ℕ)
    (grammarRunner : SelectiveFixedCountGrammarRunner width bound)
    (rowsRunner :
      SelectiveVerifierRowsProgramRunner totalSelectiveVerifierRowsProgram
        outputs width count bound) :
    SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram outputs width count bound where
  bits :=
    selectiveFixedCountLevelBits outputs width count bound grammarRunner
      rowsRunner
  fuel :=
    selectiveFixedCountLevelFuel outputs width count bound grammarRunner
      rowsRunner
  executes := by
    intro state candidate hordered entry hentryPc hentryInput
    have hbits :
        selectiveFixedCountLevelBits outputs width count bound grammarRunner
            rowsRunner state candidate ≤
          selectiveFixedCountLevelBits outputs width count bound grammarRunner
            rowsRunner state candidate := le_refl _
    unfold selectiveFixedCountLevelBits at hbits
    have hrequestBits := (Nat.le_max_left _ _).trans hbits
    have htailOne := (Nat.le_max_right _ _).trans hbits
    have hgrammarRequestBits := (Nat.le_max_left _ _).trans htailOne
    have htailTwo := (Nat.le_max_right _ _).trans htailOne
    have hgrammarWireBits := (Nat.le_max_left _ _).trans htailTwo
    have htailThree := (Nat.le_max_right _ _).trans htailTwo
    have hrowsRequestBits := (Nat.le_max_left _ _).trans htailThree
    have htailFour := (Nat.le_max_right _ _).trans htailThree
    have hrowsWireBits := (Nat.le_max_left _ _).trans htailFour
    have htailFive := (Nat.le_max_right _ _).trans htailFour
    have hemitInputBits := (Nat.le_max_left _ _).trans htailFive
    have htailSix := (Nat.le_max_right _ _).trans htailFive
    have hemitWireBits := (Nat.le_max_left _ _).trans htailSix
    have htailSeven := (Nat.le_max_right _ _).trans htailSix
    have hgrammarCalleeBits := (Nat.le_max_left _ _).trans htailSeven
    have hrowsCalleeBits := (Nat.le_max_right _ _).trans htailSeven
    have hgrammarOrdered :
        selectiveStateOrdered
          (selectiveFixedCountGrammarWire width bound state candidate).state :=
      selectiveCompileExpr_ordered state _ hordered
    rw [selectiveCompileTableFixedCount_eq]
    refine run_totalSelectiveFixedCountProgram_of_wires outputs width count bound
      state candidate
      (selectiveFixedCountGrammarWire width bound state candidate)
      (selectiveFixedCountRowsWire outputs width count bound state candidate)
      _ _ _ _ entry
      (selectiveFixedCountRowsWire_ordered outputs width count bound state
        candidate hordered)
      rfl ?_ ?_ hrequestBits hgrammarRequestBits hgrammarWireBits
      hrowsRequestBits hrowsWireBits hemitInputBits ?_ hentryPc hentryInput
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (grammarRunner.executes state candidate hordered frame hframePc
          hframeInput) hgrammarCalleeBits
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (rowsRunner.executes
          (selectiveFixedCountGrammarWire width bound state candidate).state
          (candidate.val + 1) candidate.isLt hgrammarOrdered frame hframePc
          hframeInput) hrowsCalleeBits
    · rw [← selectiveCompileTableFixedCount_eq]
      exact hemitWireBits

end NearCubicWires.TotalSelectiveFixedCountProgram
