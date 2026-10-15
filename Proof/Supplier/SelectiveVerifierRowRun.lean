import Proof.Supplier.SelectiveUniversalOutputsRun

/-!
# One verifier row's run

`selectiveVerifierRowProgram` is the `1657`-instruction stream that compiles one
randomness row of the projection table: a straight-line controller of `56`
instructions with three relocated callees, the `1256`-instruction projected
query compiler, the `10`-instruction tagged lookup and the `335`-instruction
clause-list compiler.

The controller never loops.  It parses its request, asks the query compiler for
the row's whole query list, reads the row's decision code out of the published
table with one tagged lookup, and hands both to the clause compiler; the clause
compiler's wire is the row's wire.

This module executes that controller from two named level premises, the
projected query compiler's run and the clause-list compiler's run.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveCompileUniversalOutputs_ordered from
  Proof.Supplier.SelectiveCountCasesRun

open private selectiveUniversalOutputsInput selectiveUniversalOutputsProgram
  selectiveUniversalOutputsProgram_length structuralTaggedLookupInput
  structuralTaggedLookupProgram structuralTaggedLookupBits
  structuralTaggedLookupFuel selectiveClausesInput selectiveClausesProgram
  selectiveClausesProgram_length selectiveVerifierRowInput
  selectiveVerifierRowControllerProgram
  selectiveVerifierRowControllerProgram_length selectiveVerifierRowProgram
  selectiveVerifierRowProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. Decoding the fixed 1657-instruction stream -/

private theorem selectiveVerifierRowProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveVerifierRowControllerProgram 56 1312 1322)[pc]? =
        some instruction) :
    selectiveVerifierRowProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveVerifierRowControllerProgram 56 1312 1322).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveVerifierRowControllerProgram_length] at hpc
  simp only [selectiveVerifierRowProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveVerifierRowControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveVerifierRowProgram_outputsCallable :
    ProgramCallableAt selectiveVerifierRowProgram
      selectiveUniversalOutputsProgram 56 1000 50 34 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUniversalOutputsProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalOutputsProgram_length] at hpc
  simp only [selectiveVerifierRowProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveVerifierRowControllerProgram_length]
    omega)]
  simp only [selectiveVerifierRowControllerProgram_length]
  rw [show 56 + pc - 56 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveVerifierRowProgram_lookupCallable :
    ProgramCallableAt selectiveVerifierRowProgram structuralTaggedLookupProgram
      1312 24000 50 44 := by
  intro pc instruction hlookup
  have hpc : pc < structuralTaggedLookupProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralTaggedLookupProgram_length] at hpc
  simp only [selectiveVerifierRowProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveVerifierRowControllerProgram_length,
    selectiveUniversalOutputsProgram_length]
  rw [show 1312 + pc - (56 + 1256) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveVerifierRowProgram_clausesCallable :
    ProgramCallableAt selectiveVerifierRowProgram selectiveClausesProgram
      1322 25000 50 54 := by
  intro pc instruction hlookup
  simp only [selectiveVerifierRowProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowControllerProgram_length,
      selectiveUniversalOutputsProgram_length,
      structuralTaggedLookupProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveVerifierRowControllerProgram_length,
    selectiveUniversalOutputsProgram_length,
    structuralTaggedLookupProgram_length]
  rw [show 1322 + pc - (56 + 1256 + 10) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 2. The controller's live frame

The whole controller reads one live frame: the compiler state and the nine
request constants.  Every call block rewrites the state registers in place, so
the frame is stated at whichever compiler state is current. -/

private def VerifierRowFrame {q : ℕ} (state : SelectiveState q)
    (table inputArity rowWidthValue fieldLimit width count nodeCount
      randomnessCode decisionOffset : ℕ) (machine : NPOracleState) : Prop :=
  machine.registers 4 = state.target - state.next ∧
    machine.registers 6 = state.next ∧
      machine.registers 7 = selectiveSelectedCode state.selected ∧
        machine.registers 8 = table ∧
          machine.registers 10 = inputArity ∧
            machine.registers 12 = rowWidthValue ∧
              machine.registers 14 = fieldLimit ∧
                machine.registers 16 = width ∧
                  machine.registers 18 = count ∧
                    machine.registers 20 = nodeCount ∧
                      machine.registers 22 = randomnessCode ∧
                        machine.registers 24 = decisionOffset

set_option maxHeartbeats 1600000 in
-- Twenty-two straight-line steps parse the ten-component request.
private theorem run_verifierRowPrologue {q : ℕ} (state : SelectiveState q)
    (table inputArity rowWidthValue fieldLimit width count nodeCount
      randomnessCode decisionOffset : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (entry : NPOracleState)
    (hrequestBits :
      natBitLength
          (selectiveVerifierRowInput (selectiveStateCode state) table
            inputArity rowWidthValue fieldLimit width count nodeCount
            randomnessCode decisionOffset) ≤
        maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveVerifierRowInput (selectiveStateCode state) table inputArity
          rowWidthValue fieldLimit width count nodeCount randomnessCode
          decisionOffset)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 22 →
      VerifierRowFrame state table inputArity rowWidthValue fieldLimit width
        count nodeCount randomnessCode decisionOffset resumed →
      runNPOracleProgram selectiveVerifierRowProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowProgram maximumBits
        (22 + extraFuel) entry =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveVerifierRowInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
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
  have hnodeCountBits := natBitLength_pair_left hseven
  have height := natBitLength_pair_right hseven
  have hrandomnessBits := natBitLength_pair_left height
  have hdecisionBits := natBitLength_pair_right height
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show (22 : ℕ) + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveVerifierRowInput]) hstateBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair table <|
        Nat.pair inputArity <|
          Nat.pair rowWidthValue <|
            Nat.pair fieldLimit <|
              Nat.pair width <|
                Nat.pair count <|
                  Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveVerifierRowInput])
    hone]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveVerifierRowProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveVerifierRowProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveVerifierRowProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveVerifierRowProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairLeft_instruction (value := table)
    (selectiveVerifierRowProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair inputArity <|
        Nat.pair rowWidthValue <|
          Nat.pair fieldLimit <|
            Nat.pair width <|
              Nat.pair count <|
                Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [run_unpairLeft_instruction (value := inputArity)
    (selectiveVerifierRowProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair rowWidthValue <|
        Nat.pair fieldLimit <|
          Nat.pair width <|
            Nat.pair count <|
              Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [run_unpairLeft_instruction (value := rowWidthValue)
    (selectiveVerifierRowProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair fieldLimit <|
        Nat.pair width <|
          Nat.pair count <|
            Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [run_unpairLeft_instruction (value := fieldLimit)
    (selectiveVerifierRowProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair width <|
        Nat.pair count <|
          Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [run_unpairLeft_instruction (value := width)
    (selectiveVerifierRowProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair count <|
        Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsix]
  rw [run_unpairLeft_instruction (value := count)
    (selectiveVerifierRowProgram_controllerAt (pc := 16) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodeCount (Nat.pair randomnessCode decisionOffset))
    (selectiveVerifierRowProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hseven]
  rw [run_unpairLeft_instruction (value := nodeCount)
    (selectiveVerifierRowProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodeCountBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair randomnessCode decisionOffset)
    (selectiveVerifierRowProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) height]
  rw [run_unpairLeft_instruction (value := randomnessCode)
    (selectiveVerifierRowProgram_controllerAt (pc := 20) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrandomnessBits]
  rw [run_unpairRight_instruction (value := decisionOffset)
    (selectiveVerifierRowProgram_controllerAt (pc := 21) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdecisionBits]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump]

/-! ## 3. The three call blocks -/

set_option maxHeartbeats 1600000 in
-- Twelve request steps around the relocated query compiler, then seven
-- unpacking steps.
private theorem run_verifierRowOutputsCall {width bound : ℕ}
    (outputs : List ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCode decisionOffset : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeFuel :
      calleeFuel =
        outputsRunner.fuel state count nodeCount hnodeCount randomnessCode)
    (hcalleeBits :
      outputsRunner.bits state count nodeCount hnodeCount randomnessCode ≤
        maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalOutputsInput (selectiveStateCode state)
            (encodeTaggedList outputs) (descriptionWidth width bound)
            (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
            count nodeCount randomnessCode) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireListCode
              (selectiveCompileUniversalOutputs state nodeCount hnodeCount
                (selectiveProjectedAddresses outputs width count
                  randomnessCode)))) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 22)
    (hframe :
      VerifierRowFrame state (encodeTaggedList outputs)
        (descriptionWidth width bound) (rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width count nodeCount
        randomnessCode decisionOffset machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 41 →
      resumed.registers 26 =
        encodeTaggedList
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).values →
      VerifierRowFrame
        (selectiveCompileUniversalOutputs state nodeCount hnodeCount
          (selectiveProjectedAddresses outputs width count
            randomnessCode)).state (encodeTaggedList outputs)
        (descriptionWidth width bound) (rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width count nodeCount
        randomnessCode decisionOffset resumed →
      runNPOracleProgram selectiveVerifierRowProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowProgram maximumBits
        (12 + (calleeFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, htable, harity, hrowWidth, hfieldLimit,
    hwidth, hcount, hnodeCountReg, hrandomness, hdecision⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth width bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveUniversalOutputsInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount randomnessCode =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (encodeTaggedList outputs)
            (Nat.pair (descriptionWidth width bound)
              (Nat.pair (rowWidth width bound)
                (Nat.pair (boundedCircuitFieldLimit width bound)
                  (Nat.pair width
                    (Nat.pair count
                      (Nat.pair nodeCount randomnessCode))))))) := rfl
  have hflat := hrequestBits
  rw [hrequestForm] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hfive := natBitLength_pair_right hfour
  have hsix := natBitLength_pair_right hfive
  have hseven := natBitLength_pair_right hsix
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  simp only [selectiveWireListCode] at hwireParts
  have hcompiledStateBits := natBitLength_pair_left hwireParts
  have hcompiledValuesBits := natBitLength_pair_right hwireParts
  have hcompiledStateFlat := hcompiledStateBits
  rw [hstateForm] at hcompiledStateFlat
  have hcompiledRemainingBits := natBitLength_pair_left hcompiledStateFlat
  have hcompiledTailBits := natBitLength_pair_right hcompiledStateFlat
  have hcompiledNextBits := natBitLength_pair_left hcompiledTailBits
  have hcompiledSelectedBits := natBitLength_pair_right hcompiledTailBits
  rw [show 12 + (calleeFuel + (7 + extraFuel)) =
    (calleeFuel + (7 + extraFuel)) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair nodeCount randomnessCode)
    (selectiveVerifierRowProgram_controllerAt (pc := 22) rfl) hpc
    (by rw [hnodeCountReg, hrandomness]) hseven]
  rw [run_pair_instruction
    (value := Nat.pair count (Nat.pair nodeCount randomnessCode))
    (selectiveVerifierRowProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcount]) hsix]
  rw [run_pair_instruction
    (value :=
      Nat.pair width (Nat.pair count (Nat.pair nodeCount randomnessCode)))
    (selectiveVerifierRowProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfive]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound)
        (Nat.pair width (Nat.pair count (Nat.pair nodeCount randomnessCode))))
    (selectiveVerifierRowProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hfour]
  rw [run_pair_instruction
    (value :=
      Nat.pair (rowWidth width bound)
        (Nat.pair (boundedCircuitFieldLimit width bound)
          (Nat.pair width
            (Nat.pair count (Nat.pair nodeCount randomnessCode)))))
    (selectiveVerifierRowProgram_controllerAt (pc := 26) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowWidth]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair (rowWidth width bound)
          (Nat.pair (boundedCircuitFieldLimit width bound)
            (Nat.pair width
              (Nat.pair count (Nat.pair nodeCount randomnessCode))))))
    (selectiveVerifierRowProgram_controllerAt (pc := 27) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs)
        (Nat.pair (descriptionWidth width bound)
          (Nat.pair (rowWidth width bound)
            (Nat.pair (boundedCircuitFieldLimit width bound)
              (Nat.pair width
                (Nat.pair count (Nat.pair nodeCount randomnessCode)))))))
    (selectiveVerifierRowProgram_controllerAt (pc := 28) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, htable]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveVerifierRowProgram_controllerAt (pc := 29) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowProgram_controllerAt (pc := 30) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveUniversalOutputsInput (selectiveStateCode state)
        (encodeTaggedList outputs) (descriptionWidth width bound)
        (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
        count nodeCount randomnessCode)
    (selectiveVerifierRowProgram_controllerAt (pc := 31) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 32) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 33) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveUniversalOutputsProgram)
    (calleeOutput :=
      selectiveWireListCode
        (selectiveCompileUniversalOutputs state nodeCount hnodeCount
          (selectiveProjectedAddresses outputs width count randomnessCode)))
    selectiveVerifierRowProgram_outputsCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (outputsRunner.executes state count nodeCount hnodeCount randomnessCode
        hordered frame hframePc ?_) hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _outputsHalt
    rw [show 7 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireListCode
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count randomnessCode)))
      (selectiveVerifierRowProgram_controllerAt (pc := 34) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).state)
      (selectiveVerifierRowProgram_controllerAt (pc := 35) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireListCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction
      (value :=
        encodeTaggedList
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).values)
      (selectiveVerifierRowProgram_controllerAt (pc := 36) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireListCode])
      hcompiledValuesBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).state.target -
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).state.next)
      (selectiveVerifierRowProgram_controllerAt (pc := 37) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).state.next
          (selectiveSelectedCode
            (selectiveCompileUniversalOutputs state nodeCount hnodeCount
              (selectiveProjectedAddresses outputs width count
                randomnessCode)).state.selected))
      (selectiveVerifierRowProgram_controllerAt (pc := 38) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileUniversalOutputs state nodeCount hnodeCount
          (selectiveProjectedAddresses outputs width count
            randomnessCode)).state.next)
      (selectiveVerifierRowProgram_controllerAt (pc := 39) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count
              randomnessCode)).state.selected)
      (selectiveVerifierRowProgram_controllerAt (pc := 40) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, htable,
        harity, hrowWidth, hfieldLimit, hwidth, hcount, hnodeCountReg,
        hrandomness, hdecision]

set_option maxHeartbeats 1600000 in
-- Three request steps around the relocated tagged lookup, then two unpacking
-- steps.
private theorem run_verifierRowLookupCall {q : ℕ} (state : SelectiveState q)
    (outputs : List ℕ)
    (inputArity rowWidthValue fieldLimit width count nodeCount randomnessCode
      decisionOffset : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hrequestBits :
      natBitLength
          (structuralTaggedLookupInput (encodeTaggedList outputs)
            decisionOffset) ≤
        maximumBits)
    (hcalleeBits : structuralTaggedLookupBits outputs decisionOffset ≤
      maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (outputs.getD decisionOffset 0)) ≤ maximumBits)
    (hleftBits :
      natBitLength (projectionRawOutput (outputs.getD decisionOffset 0)) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 41)
    (hframe :
      VerifierRowFrame state (encodeTaggedList outputs) inputArity
        rowWidthValue fieldLimit width count nodeCount randomnessCode
        decisionOffset machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 46 →
      resumed.registers 26 = machine.registers 26 →
      resumed.registers 28 =
        projectionRawOutput (outputs.getD decisionOffset 0) →
      VerifierRowFrame state (encodeTaggedList outputs) inputArity
        rowWidthValue fieldLimit width count nodeCount randomnessCode
        decisionOffset resumed →
      runNPOracleProgram selectiveVerifierRowProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowProgram maximumBits
        (3 + (structuralTaggedLookupFuel decisionOffset + (2 + extraFuel)))
        machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, htable, harity, hrowWidth, hfieldLimit,
    hwidth, hcount, hnodeCountReg, hrandomness, hdecision⟩ := hframe
  have hrequestForm :
      structuralTaggedLookupInput (encodeTaggedList outputs) decisionOffset =
        Nat.pair (encodeTaggedList outputs) decisionOffset := rfl
  have hwireFlat := natBitLength_pair_right hwireBits
  rw [show 3 + (structuralTaggedLookupFuel decisionOffset + (2 + extraFuel)) =
    (structuralTaggedLookupFuel decisionOffset + (2 + extraFuel)) + 1 + 1 + 1 by
    omega]
  rw [run_pair_instruction
    (value :=
      structuralTaggedLookupInput (encodeTaggedList outputs) decisionOffset)
    (selectiveVerifierRowProgram_controllerAt (pc := 41) rfl) hpc
    (by rw [htable, hdecision, hrequestForm]) hrequestBits]
  rw [run_set_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 42) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 43) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := structuralTaggedLookupProgram)
    (calleeOutput := outputs.getD decisionOffset 0)
    selectiveVerifierRowProgram_lookupCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_structuralTaggedLookupProgram_anyEntry outputs decisionOffset frame
        hframePc ?_) hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _lookupHalt
    rw [show 2 + extraFuel = extraFuel + 1 + 1 by omega]
    rw [run_unpairRight_instruction (value := outputs.getD decisionOffset 0)
      (selectiveVerifierRowProgram_controllerAt (pc := 44) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value := projectionRawOutput (outputs.getD decisionOffset 0))
      (selectiveVerifierRowProgram_controllerAt (pc := 45) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, projectionRawOutput])
      hleftBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump,
        relocateState])
      (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, hremaining,
        hnext, hselected, htable, harity, hrowWidth, hfieldLimit, hwidth,
        hcount, hnodeCountReg, hrandomness, hdecision]

set_option maxHeartbeats 1600000 in
-- Eight request steps around the relocated clause compiler, then the halt.
private theorem run_verifierRowClausesCall {q : ℕ} (state : SelectiveState q)
    (values : List ℕ) (count : ℕ)
    (clausesRunner : SelectiveClausesRunner q count)
    (table rowWidthValue fieldLimit width nodeCount randomnessCode
      decisionOffset decisionCode : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeBits :
      clausesRunner.bits state values decisionCode ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveClausesInput (selectiveStateCode state) q
            (encodeTaggedList values) count decisionCode) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileClauses state values
                (decodeThreeCNF count decisionCode).clauses))) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 46)
    (hvaluesReg : machine.registers 26 = encodeTaggedList values)
    (hdecisionCode : machine.registers 28 = decisionCode)
    (hframe :
      VerifierRowFrame state table q rowWidthValue fieldLimit width
        count nodeCount randomnessCode decisionOffset machine)
    (hfinal :
      finalOutput =
        selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF count decisionCode).clauses)) :
    runNPOracleProgram selectiveVerifierRowProgram maximumBits
        (8 + (clausesRunner.fuel state values decisionCode + 2)) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, htable, harity, hrowWidth, hfieldLimit,
    hwidth, hcount, hnodeCountReg, hrandomness, hdecision⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState q,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveClausesInput (selectiveStateCode state) q
          (encodeTaggedList values) count decisionCode =
        Nat.pair (selectiveStateCode state)
          (Nat.pair q
            (Nat.pair (encodeTaggedList values)
              (Nat.pair count decisionCode))) := rfl
  have hflat := hrequestBits
  rw [hrequestForm] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hwireFlat := natBitLength_pair_right hwireBits
  rw [show 8 + (clausesRunner.fuel state values decisionCode + 2) =
    (clausesRunner.fuel state values decisionCode + 2) + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair count decisionCode)
    (selectiveVerifierRowProgram_controllerAt (pc := 46) rfl) hpc
    (by rw [hcount, hdecisionCode]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList values) (Nat.pair count decisionCode))
    (selectiveVerifierRowProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hvaluesReg]) htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair q
        (Nat.pair (encodeTaggedList values) (Nat.pair count decisionCode)))
    (selectiveVerifierRowProgram_controllerAt (pc := 48) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveVerifierRowProgram_controllerAt (pc := 49) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowProgram_controllerAt (pc := 50) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveClausesInput (selectiveStateCode state) q
        (encodeTaggedList values) count decisionCode)
    (selectiveVerifierRowProgram_controllerAt (pc := 51) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 52) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveVerifierRowProgram_controllerAt (pc := 53) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveClausesProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileClauses state values
          (decodeThreeCNF count decisionCode).clauses))
    selectiveVerifierRowProgram_clausesCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (clausesRunner.executes state values decisionCode hordered frame hframePc
        ?_) hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _clausesHalt
    rw [show (2 : ℕ) = 0 + 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF count decisionCode).clauses))
      (selectiveVerifierRowProgram_controllerAt (pc := 54) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [hfinal]
    exact run_halt_instruction (fuel := 0)
      (selectiveVerifierRowProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat

/-! ## 4. The whole verifier row -/

/-- The compiled query list of one verifier row. -/
private def verifierRowQueries {width bound : ℕ} (outputs : List ℕ)
    (state : SelectiveState (descriptionWidth width bound)) (count : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    SelectiveWireList (descriptionWidth width bound) :=
  selectiveCompileUniversalOutputs state nodeCount hnodeCount
    (selectiveProjectedAddresses outputs width count randomnessCode)

/-- Interpreter fuel of one verifier row. -/
def selectiveVerifierRowRunFuel {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    ℕ :=
  22 +
    (12 +
      (outputsRunner.fuel state count nodeCount hnodeCount randomnessCode +
        (7 +
          (3 +
            (structuralTaggedLookupFuel
                (projectionDecisionOffset width count randomnessCode) +
              (2 +
                (8 +
                  (clausesRunner.fuel
                      (verifierRowQueries outputs state count nodeCount
                        hnodeCount randomnessCode).state
                      (verifierRowQueries outputs state count nodeCount
                        hnodeCount randomnessCode).values
                      (projectionRawOutput
                        (outputs.getD
                          (projectionDecisionOffset width count randomnessCode)
                          0)) +
                    2))))))))

/-- Register width of one verifier row. -/
def selectiveVerifierRowRunBits {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveVerifierRowInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount randomnessCode
          (projectionDecisionOffset width count randomnessCode))) <|
      max
        (natBitLength
          (selectiveUniversalOutputsInput (selectiveStateCode state)
            (encodeTaggedList outputs) (descriptionWidth width bound)
            (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
            count nodeCount randomnessCode)) <|
        max
          (outputsRunner.bits state count nodeCount hnodeCount
            randomnessCode) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireListCode
                  (verifierRowQueries outputs state count nodeCount hnodeCount
                    randomnessCode)))) <|
            max
              (structuralTaggedLookupBits outputs
                (projectionDecisionOffset width count randomnessCode)) <|
              max
                (natBitLength
                  (Nat.pair 0
                    (outputs.getD
                      (projectionDecisionOffset width count randomnessCode)
                      0))) <|
                max
                  (natBitLength
                    (selectiveClausesInput
                      (selectiveStateCode
                        (verifierRowQueries outputs state count nodeCount
                          hnodeCount randomnessCode).state)
                      (descriptionWidth width bound)
                      (encodeTaggedList
                        (verifierRowQueries outputs state count nodeCount
                          hnodeCount randomnessCode).values)
                      count
                      (projectionRawOutput
                        (outputs.getD
                          (projectionDecisionOffset width count randomnessCode)
                          0)))) <|
                  max
                    (clausesRunner.bits
                      (verifierRowQueries outputs state count nodeCount
                        hnodeCount randomnessCode).state
                      (verifierRowQueries outputs state count nodeCount
                        hnodeCount randomnessCode).values
                      (projectionRawOutput
                        (outputs.getD
                          (projectionDecisionOffset width count randomnessCode)
                          0))) <|
                    natBitLength
                      (Nat.pair 0
                        (selectiveWireCode
                          (selectiveCompileTableVerifierRow outputs width count
                            bound state nodeCount hnodeCount randomnessCode)))

set_option maxHeartbeats 1600000 in
-- The parser, the three call blocks and the halt.
/-- **One verifier row's run.**  The `1657`-instruction stream started on its
own ABI frame, at any entry registers, returns exactly the compiler wire the
source compiler produces for that randomness row. -/
theorem run_selectiveVerifierRowProgram {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveVerifierRowInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount randomnessCode
          (projectionDecisionOffset width count randomnessCode)) :
    runNPOracleProgram selectiveVerifierRowProgram
        (selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode)
        (selectiveVerifierRowRunFuel outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode) entry =
      some
        (selectiveWireCode
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode)) := by
  have hbits :
      selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode ≤
        selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode := le_refl _
  unfold selectiveVerifierRowRunBits at hbits
  have hsevenBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have houtputsRequestBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have houtputsCalleeBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have houtputsWireBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hlookupCalleeBits := (Nat.le_max_left _ _).trans hbitsFive
  have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
  have hlookupWireBits := (Nat.le_max_left _ _).trans hbitsSix
  have hbitsSeven := (Nat.le_max_right _ _).trans hbitsSix
  have hclausesRequestBits := (Nat.le_max_left _ _).trans hbitsSeven
  have hbitsEight := (Nat.le_max_right _ _).trans hbitsSeven
  have hclausesCalleeBits := (Nat.le_max_left _ _).trans hbitsEight
  have hclausesWireBits := (Nat.le_max_right _ _).trans hbitsEight
  have hsmall : ∀ value : ℕ, value ≤ 7 →
      natBitLength value ≤
        selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hlookupRequestBits :
      natBitLength
          (structuralTaggedLookupInput (encodeTaggedList outputs)
            (projectionDecisionOffset width count randomnessCode)) ≤
        selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode :=
    hlookupCalleeBits
  have hlookupLeftBits :
      natBitLength
          (projectionRawOutput
            (outputs.getD
              (projectionDecisionOffset width count randomnessCode) 0)) ≤
        selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode := by
    refine (natBitLength_mono ?_).trans
      ((natBitLength_mono (Nat.right_le_pair 0 _)).trans hlookupWireBits)
    exact Nat.unpair_left_le _
  have hrowEq :
      selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount randomnessCode =
        selectiveCompileClauses
          (verifierRowQueries outputs state count nodeCount hnodeCount
            randomnessCode).state
          (verifierRowQueries outputs state count nodeCount hnodeCount
            randomnessCode).values
          (decodeThreeCNF count
            (projectionRawOutput
              (outputs.getD
                (projectionDecisionOffset width count randomnessCode)
                0))).clauses := rfl
  unfold selectiveVerifierRowRunFuel
  refine run_verifierRowPrologue state (encodeTaggedList outputs)
    (descriptionWidth width bound) (rowWidth width bound)
    (boundedCircuitFieldLimit width bound) width count nodeCount randomnessCode
    (projectionDecisionOffset width count randomnessCode) _ _ _ entry
    hrequestBits hentryPc hentryInput ?_
  intro afterPrologue hprologuePc hprologueFrame
  refine run_verifierRowOutputsCall outputs outputsRunner state count nodeCount
    hnodeCount randomnessCode
    (projectionDecisionOffset width count randomnessCode) hordered _ _ _ _
    afterPrologue rfl houtputsCalleeBits houtputsRequestBits houtputsWireBits
    (hsmall 0 (by omega)) hprologuePc hprologueFrame ?_
  intro afterOutputs houtputsPc houtputsValues houtputsFrame
  refine run_verifierRowLookupCall
    (verifierRowQueries outputs state count nodeCount hnodeCount
      randomnessCode).state outputs (descriptionWidth width bound)
    (rowWidth width bound) (boundedCircuitFieldLimit width bound) width count
    nodeCount randomnessCode
    (projectionDecisionOffset width count randomnessCode) _ _ _ afterOutputs
    hlookupRequestBits hlookupCalleeBits hlookupWireBits hlookupLeftBits
    (hsmall 0 (by omega)) houtputsPc houtputsFrame ?_
  intro afterLookup hlookupPc hlookupValues hlookupDecision hlookupFrame
  rw [hrowEq]
  refine run_verifierRowClausesCall
    (verifierRowQueries outputs state count nodeCount hnodeCount
      randomnessCode).state
    (verifierRowQueries outputs state count nodeCount hnodeCount
      randomnessCode).values count clausesRunner (encodeTaggedList outputs)
    (rowWidth width bound)
    (boundedCircuitFieldLimit width bound) width nodeCount randomnessCode
    (projectionDecisionOffset width count randomnessCode)
    (projectionRawOutput
      (outputs.getD (projectionDecisionOffset width count randomnessCode) 0))
    (selectiveCompileUniversalOutputs_ordered nodeCount hnodeCount _ state
      hordered)
    _ _ afterLookup hclausesCalleeBits hclausesRequestBits ?_
    (hsmall 0 (by omega)) hlookupPc ?_ hlookupDecision hlookupFrame rfl
  · rw [← hrowEq]
    exact hclausesWireBits
  · rw [hlookupValues]
    exact houtputsValues

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
