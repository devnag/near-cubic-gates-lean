import Proof.Circuits.InverseCompilerTowerClosure
import Proof.MachineModel.RuntimeCaseTwoDescriptionFrameAdapter

/-!
# The description pool's atom stream, from the closed compiler tower

`RuntimeCaseTwoDescriptionFrameAdapter.inverseScheduledOccurrenceEncoding_ofAtomStream`
leaves the whole Case-2 encoder standing on one premise,
`InverseDescriptionAtomStreamRuns`: from the requested public length alone, one
fixed stream must emit

> `pair atoms (pair nativeWidth sizeBound)`

where `atoms` is `CaseTwoDescriptionBitPoolProgram.descriptionAtomContext`, i.e.
the **balanced** encoding of the schedule's canonical structural atom list.

This module builds that stream and discharges the premise.

## Balanced, not tagged

The published emitter `StructuralAtomEmitterLoopProgram.structuralAtomEmitterProgram`
returns `encodeTaggedList` of the same atom list, and converting a tagged list
back to a balanced one costs `taggedToBalancedRegisterBitsFor`, whose register
width is bounded below by `2 ^ (list length)`.  The route taken here is the
emitter's *first half*, `structuralAtomRangeProgram`, before the two
point-preserving wrappers and before `balancedToTaggedProgram`: its output is
`encodeBalancedList` of the same list, at the loop's own width.  §1 instantiates
it at an executable projection PCP, exactly as
`StructuralAtomCalleeProgram` instantiates the tagged emitter.

## Where the two numerals come from

They are bank registers.  `inverseFrameWidth` is definitionally
`RecoveryScheduleEnvelope.scheduledWidth` at the chain's own source index and
`inverseFrameBound` is definitionally `BankEmittedAtomLoop.inverseScheduleBound`,
so on the schedule's diagonal both are read off
`BankAtomContextRegisters.bankShapeNumerals`, which
`run_bankShapeNumeralProgram` already computes from the numeral bank's frame with
no premise.  §2 is the three-numeral projection that keeps the width and the size
cap and drops the query count.

## Why the whole cluster reduces here

Every stage between the bank's frame and the atom loop is already published, but
each is stated at a request `⟨target, input⟩`, hence at the point code
`encodeBitInput input`.  The atom stream is entered at the point code `target`
itself.  Every underlying run theorem is already code generic; only
`BankProjectionTableStage.inverseAdapterFrame_ofRegisters` names the request's
code, so §3 restates that join fact and the three stages above it at an arbitrary
retained code.  §4 links the numeral bank in front of the result, discharges the
atom loop's six width budgets against the closed tower of
`SelectiveCountCasesInverse.inverseCompilerRuns_closed`, and closes the bank
cluster at the presentation, the schedule diagonal and the scheduled query
counts.
-/

namespace NearCubicWires.InverseDescriptionAtomStream

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
open NearCubicWires.RuntimeCaseTwoDescriptionFrameAdapter
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectiveCountCasesInverse
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

open private frameDuplicateBits run_frameDuplicateProgram from
  Proof.MachineModel.BankFrameLoweringAdapter

open private contextDuplicateBits run_contextDuplicateProgram contextSwapProgram
  contextSwapBits run_contextSwapProgram from Proof.MachineModel.BankAtomContextRegisters

open private structuralAtomRequests_map_at from
  Proof.MachineModel.StructuralAtomCalleeProgram

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbound : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbound

/-! ## 1. The balanced atom loop at an executable projection PCP -/

set_option maxHeartbeats 800000 in
-- The loop's fuel is a nested link term over the balanced caller, so the
-- statement alone exceeds the default budget.
/-- **The balanced index loop at an executable projection PCP and any public
length.**  This is `StructuralAtomCalleeProgram.run_structuralAtomEmitterProgram_table_at`
with both point-preserving wrappers and the tagged converter removed: the loop
itself returns the *balanced* encoding of the canonical atom schedule. -/
theorem run_structuralAtomRangeProgram_table_at
    (callee : NPOracleProgram) {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ)
    (calleeFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength machineInputLength ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms machineInputLength
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms machineInputLength
            (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcallee : ∀ index, index < structuralAtomCount pcp input bound →
      runNPOracleProgram callee rangeBits
          (calleeFuel
            (balancedRangeRequestAtom machineInputLength index
              (structuralAtomContext pcp input bound)))
          (initialNPOracleState machineInputLength
            (Nat.pair index (structuralAtomContext pcp input bound))) =
        some (structuralAtomValue pcp input bound index)) :
    runNPOracleProgram (structuralAtomRangeProgram callee) rangeBits
        (structuralAtomRangeFuel callee machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) calleeFuel)
        (initialNPOracleState machineInputLength
          (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound))) =
      some
        (encodeBalancedList
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)) := by
  have hmap := structuralAtomRequests_map_at pcp input machineInputLength bound
  rw [← hmap]
  refine run_structuralAtomRangeProgram callee machineInputLength
    (structuralAtomCount pcp input bound)
    (structuralAtomContext pcp input bound) calleeFuel
    (fun request =>
      structuralAtomValue pcp input bound (structuralAtomRequestIndex request))
    hpositive hlengthBits hrangeBits hlistBits hcallBits ?_
  intro request hrequest
  rw [balancedRangeRequestAtoms_eq_map_range, List.mem_map] at hrequest
  obtain ⟨index, hindex, hrequestEq⟩ := hrequest
  rw [Nat.zero_add] at hrequestEq
  subst hrequestEq
  rw [structuralAtomRequestIndex_atom]
  have hleft :
      (Nat.unpair
        (balancedRangeRequestAtom machineInputLength index
          (structuralAtomContext pcp input bound))).1 = machineInputLength := by
    simp [balancedRangeRequestAtom]
  have hright :
      (Nat.unpair
        (balancedRangeRequestAtom machineInputLength index
          (structuralAtomContext pcp input bound))).2 =
        Nat.pair index (structuralAtomContext pcp input bound) := by
    simp [balancedRangeRequestAtom]
  rw [hleft, hright]
  exact hcallee index (List.mem_range.mp hindex)

set_option maxHeartbeats 800000 in
-- The callee's request fuel is itself a link term, so the statement alone
-- exceeds the default budget.
/-- **The balanced atom loop from the compiler's run alone.**  The balanced twin
of `StructuralAtomCalleeProgram.run_structuralAtomEmitterProgram_ofCompiler`:
the only per-index premise left is the nested compiler's own run. -/
theorem run_structuralAtomRangeProgram_ofCompiler
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ)
    (compilerBits compilerFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength machineInputLength ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms machineInputLength
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms machineInputLength
            (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcalleeBits : ∀ index, index < structuralAtomCount pcp input bound →
      structuralAtomCalleeBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound index (compilerBits index) ≤
        rangeBits)
    (hcompiler : ∀ index, index < structuralAtomCount pcp input bound →
      StructuralCompilerRunsAt pcp input machineInputLength bound index
        (compilerBits index) (compilerFuel index)) :
    runNPOracleProgram (structuralAtomRangeProgram structuralAtomCalleeProgram)
        rangeBits
        (structuralAtomRangeFuel structuralAtomCalleeProgram machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound)
          (structuralAtomCalleeRequestFuel
            (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
            (pcp.queryCount n) bound compilerFuel))
        (initialNPOracleState machineInputLength
          (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound))) =
      some
        (encodeBalancedList
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)) := by
  refine run_structuralAtomRangeProgram_table_at structuralAtomCalleeProgram pcp
    input machineInputLength bound _ hpositive hlengthBits hrangeBits hlistBits
    hcallBits ?_
  intro index hindex
  exact run_bits_mono
    (run_structuralAtomCalleeProgram_index pcp input machineInputLength bound
      index (compilerBits index) compilerFuel (hcompiler index hindex))
    (hcalleeBits index hindex)

/-! ## 2. The width and the size cap, projected out of the shape numerals -/

/-- The frame the tail projection starts from: the bank's three shape numerals
beside the retained balanced atom stream. -/
def descriptionAtomTailInput (atoms width queryCount bound : ℕ) : ℕ :=
  Nat.pair (Nat.pair width (Nat.pair queryCount bound)) atoms

/-- The tail's input is literally the shape numerals beside the atoms. -/
theorem descriptionAtomTailInput_eq (atoms width queryCount bound : ℕ) :
    Nat.pair (bankShapeNumerals bound width queryCount) atoms =
      descriptionAtomTailInput atoms width queryCount bound :=
  rfl

/-- **The tail projection.**  Drop the query count and put the atom stream in
front: `pair (pair width (pair queryCount bound)) atoms` becomes
`pair atoms (pair width bound)`, the description frame's own source word. -/
def descriptionAtomTailProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 5 5 5
  , .pair 4 5 4 6
  , .pair 3 4 0 7
  , .halt 0
  ]

@[simp] theorem descriptionAtomTailProgram_oracleFree :
    OracleFree descriptionAtomTailProgram := by
  rfl

def descriptionAtomTailFuel : ℕ := 8

def descriptionAtomTailBits (atoms width queryCount bound : ℕ) : ℕ :=
  natBitLength
    (max (descriptionAtomTailInput atoms width queryCount bound)
      (Nat.pair atoms (Nat.pair width bound)))

/-- **The tail projection, executed.**  No premise: the whole stage is four
unpairs and two pairs over the numerals the bank already emits. -/
theorem run_descriptionAtomTailProgram
    (inputLength atoms width queryCount bound : ℕ) :
    runNPOracleProgram descriptionAtomTailProgram
        (descriptionAtomTailBits atoms width queryCount bound)
        descriptionAtomTailFuel
        (initialNPOracleState inputLength
          (descriptionAtomTailInput atoms width queryCount bound)) =
      some (Nat.pair atoms (Nat.pair width bound)) := by
  have hinput :
      natBitLength (descriptionAtomTailInput atoms width queryCount bound) ≤
        descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.le_max_left _ _) (Nat.le_refl _)
  have houtput :
      natBitLength (Nat.pair atoms (Nat.pair width bound)) ≤
        descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.le_max_right _ _) (Nat.le_refl _)
  have hshape :
      natBitLength (Nat.pair width (Nat.pair queryCount bound)) ≤
        descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.left_le_pair _ _) hinput
  have hatoms : natBitLength atoms ≤
      descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.right_le_pair _ _) hinput
  have hwidth : natBitLength width ≤
      descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.left_le_pair _ _) hshape
  have htail : natBitLength (Nat.pair queryCount bound) ≤
      descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.right_le_pair _ _) hshape
  have hbound : natBitLength bound ≤
      descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.right_le_pair _ _) htail
  have hpair : natBitLength (Nat.pair width bound) ≤
      descriptionAtomTailBits atoms width queryCount bound :=
    bits_of_le (Nat.right_le_pair _ _) houtput
  rw [show descriptionAtomTailFuel = 7 + 1 by rfl]
  rw [run_unpairLeft_instruction
    (value := Nat.pair width (Nat.pair queryCount bound)) (by rfl) rfl
    (by simp [initialNPOracleState, descriptionAtomTailInput]) hshape]
  rw [show (7 : ℕ) = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := atoms) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      descriptionAtomTailInput])
    hatoms]
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidth]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair queryCount bound) (by rfl)
    rfl (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hbound]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair width bound) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair atoms (Nat.pair width bound))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The bank cluster's stages at an arbitrary retained code -/

/-- **The join fact, at an arbitrary retained code.**  This is
`BankProjectionTableStage.inverseAdapterFrame_ofRegisters` with the request's own
point code `encodeBitInput input` released: nothing in the proof reads it. -/
theorem publishedBankFrame_ofRegisters (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target code : ℕ)
    (hdiagonal :
      target =
        sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target))) :
    publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code =
      scheduleNumeralBankOutput
        (sourceLength (inverseSourceIndex
          (inverseSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth)
            (inverseCoreAdvantagePower advantageExponent) target)))
        (pcp.nativeWidth
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))))
        (pcp.queryCount
          (sourceLength (inverseSourceIndex
            (inverseSelectedSource contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              (inverseCoreAdvantagePower advantageExponent) target))))
        (inverseBankTableCopies contracts clockDepth advantageExponent target)
        code := by
  have hwidth :=
    presentsPaddedOuterPCP_scheduledWidth hpresentation
      (inverseSourceIndex
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target))
  have hquery :=
    congrFun (presentsPaddedOuterPCP_queryCount hpresentation)
      (sourceLength (inverseSourceIndex
        (inverseSelectedSource contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          (inverseCoreAdvantagePower advantageExponent) target)))
  simp only [inverseBankTableCopies]
  rw [hwidth, hquery]
  exact publishedBankFrame_at_inverseDiagonal contracts clockDepth
    advantageExponent target code hdiagonal

/-- Width of the projection-runner table stage at one target and one retained
code. -/
noncomputable def inverseCodeTableBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target code : ℕ) : ℕ :=
  bankProjectionTableBits pcp
    (publishedRefuterSource contracts clockDepth).refuter machine target
    (inverseScheduleLength contracts clockDepth advantageExponent target)
    (inverseBankTableCopies contracts clockDepth advantageExponent target) code

/-- Clock of the projection-runner table stage at one target. -/
noncomputable def inverseCodeTableFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  bankProjectionTableFuel pcp
    (publishedRefuterSource contracts clockDepth).refuter machine
    (inverseScheduleLength contracts clockDepth advantageExponent target)

/-- **The table stage at an arbitrary retained code.**  The code-generic form of
`BankProjectionTableStage.inverseAtomTableRuns_ofDiagonal`. -/
theorem run_inverseCodeTableProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target code : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    runNPOracleProgram (inverseBankTableProgram contracts clockDepth machine pcp)
        (inverseCodeTableBits contracts clockDepth machine advantageExponent pcp
          target code)
        (inverseCodeTableFuel contracts clockDepth machine advantageExponent pcp
          target)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)) =
      some
        (encodeBalancedList
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))) := by
  rw [publishedBankFrame_ofRegisters contracts clockDepth advantageExponent pcp
    hpresentation target code hdiagonal]
  exact run_bankProjectionTableProgram pcp
    (publishedRefuterSource contracts clockDepth).refuter machine target
    (inverseScheduleLength contracts clockDepth advantageExponent target)
    (inverseBankTableCopies contracts clockDepth advantageExponent target) code
    hdiagonal

/-- Width of the context stage at one target and one retained code. -/
noncomputable def inverseCodeAtomContextBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target code : ℕ) : ℕ :=
  occurrenceStageBits target
    (contextDuplicateBits
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code))
    (occurrenceStageBits target
      (preserveRightBits
        (bankShapeNumeralBits
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target (bankSourceLength target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (sourceIndexOfLength target))
          code)
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target code)
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target code)
        (bankShapeNumerals
          (oracleSizeBound
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseBankWidth contracts clockDepth target))
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)))
      (occurrenceStageBits target
        (contextSwapBits
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseBankWidth contracts clockDepth target))
            (inverseBankWidth contracts clockDepth target)
            (inverseBankQueryCount contracts clockDepth target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code))
        (preserveRightBits
          (inverseCodeTableBits contracts clockDepth machine advantageExponent
            pcp target code)
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)
          (bankShapeNumerals
            (oracleSizeBound
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseBankWidth contracts clockDepth target))
            (inverseBankWidth contracts clockDepth target)
            (inverseBankQueryCount contracts clockDepth target))
          (encodeBalancedList
            (projectionRunnerCallOutputs pcp
              (inverseScheduleInput contracts clockDepth machine
                advantageExponent target))))))

/-- Clock of the context stage at one target. -/
noncomputable def inverseCodeAtomContextFuel (contracts : PublishedContracts)
    (advantageExponent : ℝ) (table : NPOracleProgram) (tableFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      (linkPrograms contextSwapProgram (preserveRightProgram table)))
    2
    (linkFuel
      (linkPrograms contextSwapProgram (preserveRightProgram table))
      (preserveRightFuel
        (bankShapeNumeralFuel
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      (linkFuel (preserveRightProgram table) 4 (preserveRightFuel tableFuel)))

set_option maxHeartbeats 800000 in
-- The statement carries the whole register half of the context at one retained
-- code, so elaborating it alone exceeds the default budget.
/-- **The context stage at an arbitrary retained code.**  The code-generic form
of `BankAtomContextRegisters.inverseAtomContextRuns_ofTable`. -/
theorem run_inverseCodeAtomContextProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (target code : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    runNPOracleProgram
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseBankTableProgram contracts clockDepth machine pcp))
        (inverseCodeAtomContextBits contracts clockDepth machine
          advantageExponent pcp target code)
        (inverseCodeAtomContextFuel contracts advantageExponent
          (inverseBankTableProgram contracts clockDepth machine pcp)
          (inverseCodeTableFuel contracts clockDepth machine advantageExponent
            pcp target))
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)) =
      some
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target) := by
  refine Eq.trans ?_
    (congrArg some
      (inverseAtomContext_ofRegisters contracts clockDepth machine
        advantageExponent pcp hpresentation target hdiagonal))
  exact run_occurrenceStage
    (run_contextDuplicateProgram target
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code))
    (run_occurrenceStage
      (run_preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent)))
        target _ _
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target code)
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target code)
        _
        (run_bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target (bankSourceLength target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (sourceIndexOfLength target))
          code))
      (run_occurrenceStage
        (run_contextSwapProgram target _
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code))
        (run_preserveRightProgram
          (inverseBankTableProgram contracts clockDepth machine pcp) target
          (inverseCodeTableBits contracts clockDepth machine advantageExponent
            pcp target code)
          (inverseCodeTableFuel contracts clockDepth machine advantageExponent
            pcp target)
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)
          _ _
          (run_inverseCodeTableProgram contracts clockDepth machine
            advantageExponent pcp hpresentation target code hdiagonal))))

/-- Width of the atom-shape stage at one target and one retained code. -/
noncomputable def inverseCodeAtomShapeBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target code : ℕ) : ℕ :=
  occurrenceStageBits target
    (inverseCodeAtomContextBits contracts clockDepth machine advantageExponent
      pcp target code)
    (atomShapeCountBits target
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target)
      (structuralAtomCountBits target
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target) 0
        (compilerBits target 0))
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target))

/-- Clock of the atom-shape stage at one target. -/
noncomputable def inverseCodeAtomShapeFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel atomShapeCountProgram
    (inverseCodeAtomContextFuel contracts advantageExponent
      (inverseBankTableProgram contracts clockDepth machine pcp)
      (inverseCodeTableFuel contracts clockDepth machine advantageExponent pcp
        target))
    (atomShapeCountFuel
      (structuralAtomCountFuel
        (projectionRunnerCallOutputs pcp
          (inverseScheduleInput contracts clockDepth machine advantageExponent
            target))
        (pcp.nativeWidth
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (inverseScheduleBound contracts clockDepth advantageExponent target) 0
        (compilerFuel target 0)))

set_option maxHeartbeats 800000 in

-- elaborating it alone exceeds the default budget.
/-- **The atom-shape stage at an arbitrary retained code.**  The code-generic
form of `BankAtomShapeCountStage.inverseAtomShapeRuns_ofContext`. -/
theorem run_inverseCodeAtomShapeProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel)
    (target code : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    runNPOracleProgram
        (inverseAtomShapeProgram
          (inverseAtomContextProgram
            (inverseRequiredDegree contracts
              (inverseCoreAdvantagePower advantageExponent))
            (inverseBankTableProgram contracts clockDepth machine pcp)))
        (inverseCodeAtomShapeBits contracts clockDepth machine advantageExponent
          pcp compilerBits target code)
        (inverseCodeAtomShapeFuel contracts clockDepth machine advantageExponent
          pcp compilerFuel target)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)) =
      some
        (generatedBalancedRangeInput
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)) :=
  run_occurrenceStage
    (run_inverseCodeAtomContextProgram contracts clockDepth machine
      advantageExponent pcp hpresentation target code hdiagonal)
    (run_atomShapeCountProgram target
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        target)
      _ _
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        target)
      (run_structuralAtomCountProgram_index pcp
        (inverseScheduleInput contracts clockDepth machine advantageExponent
          target)
        target
        (inverseScheduleBound contracts clockDepth advantageExponent target)
        (compilerBits target 0) (compilerFuel target 0)
        (hcompiler target 0
          (inverseAtomCount_pos contracts clockDepth machine advantageExponent
            pcp target))))

/-- Width of the frame-lowering adapter at one target and one retained code. -/
noncomputable def inverseCodeFrameAdapterBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target code : ℕ) : ℕ :=
  occurrenceStageBits target
    (frameDuplicateBits
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code))
    (preserveRightBits
      (inverseCodeAtomShapeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target code)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code)
      (generatedBalancedRangeInput
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)))

/-- Clock of the frame-lowering adapter at one target. -/
noncomputable def inverseCodeFrameAdapterFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel
    (preserveRightProgram
      (inverseAtomShapeProgram
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseBankTableProgram contracts clockDepth machine pcp))))
    2
    (preserveRightFuel
      (inverseCodeAtomShapeFuel contracts clockDepth machine advantageExponent
        pcp compilerFuel target))

set_option maxHeartbeats 800000 in
-- The statement carries the whole lowering chain at one retained code, so
-- elaborating it alone exceeds the default budget.
/-- **The frame-lowering adapter at an arbitrary retained code.**  The
code-generic form of `BankFrameLoweringAdapter.inverseFrameAdapterRuns_ofShape`:
the loop's input frame beside the bank's frame, retained verbatim. -/
theorem run_inverseCodeFrameAdapterProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel)
    (target code : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    runNPOracleProgram
        (inverseFrameAdapterProgram
          (inverseAtomShapeProgram
            (inverseAtomContextProgram
              (inverseRequiredDegree contracts
                (inverseCoreAdvantagePower advantageExponent))
              (inverseBankTableProgram contracts clockDepth machine pcp))))
        (inverseCodeFrameAdapterBits contracts clockDepth machine
          advantageExponent pcp compilerBits target code)
        (inverseCodeFrameAdapterFuel contracts clockDepth machine
          advantageExponent pcp compilerFuel target)
        (initialNPOracleState target
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)) =
      some
        (Nat.pair
          (generatedBalancedRangeInput
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target code)) :=
  run_occurrenceStage
    (run_frameDuplicateProgram target
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code))
    (run_preserveRightProgram
      (inverseAtomShapeProgram
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseBankTableProgram contracts clockDepth machine pcp)))
      target
      (inverseCodeAtomShapeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target code)
      (inverseCodeAtomShapeFuel contracts clockDepth machine advantageExponent
        pcp compilerFuel target)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target code)
      (generatedBalancedRangeInput
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target))
      (run_inverseCodeAtomShapeProgram contracts clockDepth machine
        advantageExponent pcp hpresentation compilerBits compilerFuel hcompiler
        target code hdiagonal))

/-! ## 4. The atom loop's six width budgets -/

/-- The pointwise callee's width at one target and one global formula index. -/
noncomputable def inverseAtomStreamCalleeBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target index : ℕ) : ℕ :=
  structuralAtomCalleeBits target
    (projectionRunnerCallOutputs pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target))
    (pcp.nativeWidth
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (pcp.queryCount
      (inverseScheduleLength contracts clockDepth advantageExponent target))
    (inverseScheduleBound contracts clockDepth advantageExponent target) index
    (compilerBits target index)

/-- **The atom loop's shared width at one target.**  All six budgets of
`run_structuralAtomRangeProgram_ofCompiler` are charged here at once: the five
scalar ones as a max chain, the per-index one as the finite supremum over the
loop's own index range. -/
noncomputable def inverseAtomStreamRangeBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  max
    (max (max 1 (natBitLength target))
      (max
        (generatedBalancedRangeRequiredBits target
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target))
        (natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms target
              (inverseAtomContext contracts clockDepth machine advantageExponent
                pcp target)
              0
              (inverseAtomCount contracts clockDepth machine advantageExponent
                pcp target))))))
    (max
      (balancedCallRequiredBits
        (fun request =>
          structuralAtomValue pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)
            (inverseScheduleBound contracts clockDepth advantageExponent target)
            (structuralAtomRequestIndex request))
        (balancedRangeRequestAtoms target
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)
          0
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)))
      ((Finset.range
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)).sup
        (inverseAtomStreamCalleeBits contracts clockDepth machine
          advantageExponent pcp compilerBits target)))

private theorem rangeBits_positive (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) :
    1 ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  unfold inverseAtomStreamRangeBits
  omega

private theorem rangeBits_length (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) :
    natBitLength target ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  unfold inverseAtomStreamRangeBits
  omega

private theorem rangeBits_range (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) :
    generatedBalancedRangeRequiredBits target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target) ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  unfold inverseAtomStreamRangeBits
  omega

private theorem rangeBits_list (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) :
    natBitLength
        (encodeBalancedList
          (balancedRangeRequestAtoms target
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target)
            0
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target))) ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  unfold inverseAtomStreamRangeBits
  omega

private theorem rangeBits_call (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) :
    balancedCallRequiredBits
        (fun request =>
          structuralAtomValue pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target)
            (inverseScheduleBound contracts clockDepth advantageExponent target)
            (structuralAtomRequestIndex request))
        (balancedRangeRequestAtoms target
          (inverseAtomContext contracts clockDepth machine advantageExponent pcp
            target)
          0
          (inverseAtomCount contracts clockDepth machine advantageExponent pcp
            target)) ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  unfold inverseAtomStreamRangeBits
  omega

private theorem rangeBits_callee (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target index : ℕ)
    (hindex :
      index <
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target) :
    inverseAtomStreamCalleeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target index ≤
      inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target := by
  refine le_trans
    (Finset.le_sup
      (f :=
        inverseAtomStreamCalleeBits contracts clockDepth machine
          advantageExponent pcp compilerBits target)
      (Finset.mem_range.mpr hindex)) ?_
  unfold inverseAtomStreamRangeBits
  omega

/-! ## 5. The atom stream -/

/-- The size cap the bank's own width register produces. -/
noncomputable def inverseBankBound (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  oracleSizeBound
    (inverseRequiredDegree contracts
      (inverseCoreAdvantagePower advantageExponent))
    (inverseBankWidth contracts clockDepth target)

/-- **The join fact of the tail.**  On the schedule's diagonal the bank's width
register and the size cap computed from it are the two numerals the description
frame asks for. -/
theorem descriptionAtomTailOutput_ofRegisters (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ)
    (hdiagonal :
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target) :
    Nat.pair
        (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
        (Nat.pair (inverseBankWidth contracts clockDepth target)
          (inverseBankBound contracts clockDepth advantageExponent target)) =
      descriptionFrameSource
        (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
        (inverseFrameWidth contracts clockDepth advantageExponent target)
        (inverseFrameBound contracts clockDepth advantageExponent target) := by
  have hindex :
      sourceIndexOfLength target =
        inverseChainSourceIndex contracts clockDepth advantageExponent target :=
    sourceIndexOfLength_of_eq_sourceLength hdiagonal
  have hwidth :
      inverseBankWidth contracts clockDepth target =
        inverseFrameWidth contracts clockDepth advantageExponent target := by
    rw [inverseBankWidth, hindex]
    rfl
  rw [inverseBankBound, hwidth]
  rfl

/-- The tail of the atom-stream body: the retained frame swapped in front of the
atom stream, the shape numerals computed on it, then the tail projection. -/
noncomputable def inverseAtomStreamTailProgram (contracts : PublishedContracts)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms contextSwapProgram
    (linkPrograms
      (preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      descriptionAtomTailProgram)

/-- The balanced atom loop under the frame-preserving wrapper, then the tail. -/
noncomputable def inverseAtomStreamLoopProgram (contracts : PublishedContracts)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms
    (preserveRightProgram
      (structuralAtomRangeProgram structuralAtomCalleeProgram))
    (inverseAtomStreamTailProgram contracts advantageExponent)

/-- The atom-stream body, entered at the numeral bank's frame. -/
noncomputable def inverseAtomStreamBodyProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  linkPrograms
    (inverseFrameAdapterProgram
      (inverseAtomShapeProgram
        (inverseAtomContextProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          (inverseBankTableProgram contracts clockDepth machine pcp))))
    (inverseAtomStreamLoopProgram contracts advantageExponent)

/-- **The description pool's atom stream.**  One fixed instruction stream: the
published numeral bank, then the body of §5. -/
noncomputable def inverseAtomStreamProgram (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  linkPrograms
    (publishedBankProgram (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent))
    (inverseAtomStreamBodyProgram contracts clockDepth machine advantageExponent
      pcp)

noncomputable def inverseAtomStreamTailBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (contextSwapBits
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target target))
    (occurrenceStageBits target
      (preserveRightBits
        (bankShapeNumeralBits
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))
          target (bankSourceLength target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)
          (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (sourceIndexOfLength target))
          target)
        (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent) target target)
        (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
        (bankShapeNumerals
          (inverseBankBound contracts clockDepth advantageExponent target)
          (inverseBankWidth contracts clockDepth target)
          (inverseBankQueryCount contracts clockDepth target)))
      (descriptionAtomTailBits
        (inverseFrameAtoms contracts clockDepth machine advantageExponent target)
        (inverseBankWidth contracts clockDepth target)
        (inverseBankQueryCount contracts clockDepth target)
        (inverseBankBound contracts clockDepth advantageExponent target)))

noncomputable def inverseAtomStreamLoopBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (preserveRightBits
      (inverseAtomStreamRangeBits contracts clockDepth machine advantageExponent
        pcp compilerBits target)
      (generatedBalancedRangeInput
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target))
      (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
        (publishedPointwisePCPP contracts)
        (inverseBankRate contracts advantageExponent) target target)
      (inverseFrameAtoms contracts clockDepth machine advantageExponent target))
    (inverseAtomStreamTailBits contracts clockDepth machine advantageExponent
      target)

noncomputable def inverseAtomStreamBodyBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (inverseCodeFrameAdapterBits contracts clockDepth machine advantageExponent
      pcp compilerBits target target)
    (inverseAtomStreamLoopBits contracts clockDepth machine advantageExponent pcp
      compilerBits target)

/-- Register width of the atom stream at one target. -/
noncomputable def inverseAtomStreamBits (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (publishedBankBits (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target target)
    (inverseAtomStreamBodyBits contracts clockDepth machine advantageExponent pcp
      compilerBits target)

noncomputable def inverseAtomStreamTailFuel (contracts : PublishedContracts)
    (advantageExponent : ℝ) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (bankShapeNumeralProgram
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      descriptionAtomTailProgram)
    4
    (linkFuel descriptionAtomTailProgram
      (preserveRightFuel
        (bankShapeNumeralFuel
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))))
      descriptionAtomTailFuel)

noncomputable def inverseAtomStreamLoopFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel (inverseAtomStreamTailProgram contracts advantageExponent)
    (preserveRightFuel
      (structuralAtomRangeFuel structuralAtomCalleeProgram target
        (inverseAtomCount contracts clockDepth machine advantageExponent pcp
          target)
        (inverseAtomContext contracts clockDepth machine advantageExponent pcp
          target)
        (structuralAtomCalleeRequestFuel
          (projectionRunnerCallOutputs pcp
            (inverseScheduleInput contracts clockDepth machine advantageExponent
              target))
          (pcp.nativeWidth
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (pcp.queryCount
            (inverseScheduleLength contracts clockDepth advantageExponent
              target))
          (inverseScheduleBound contracts clockDepth advantageExponent target)
          (compilerFuel target))))
    (inverseAtomStreamTailFuel contracts advantageExponent)

noncomputable def inverseAtomStreamBodyFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel (inverseAtomStreamLoopProgram contracts advantageExponent)
    (inverseCodeFrameAdapterFuel contracts clockDepth machine advantageExponent
      pcp compilerFuel target)
    (inverseAtomStreamLoopFuel contracts clockDepth machine advantageExponent pcp
      compilerFuel target)

/-- Interpreter clock of the atom stream at one target. -/
noncomputable def inverseAtomStreamFuel (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) (target : ℕ) : ℕ :=
  linkFuel
    (inverseAtomStreamBodyProgram contracts clockDepth machine advantageExponent
      pcp)
    (publishedBankFuel (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target)
    (inverseAtomStreamBodyFuel contracts clockDepth machine advantageExponent pcp
      compilerFuel target)

set_option maxHeartbeats 1600000 in
-- The statement is the whole atom-stream premise at the linked stream, so
-- elaborating it alone exceeds the default budget.
/-- **The atom-stream premise, from the nested compiler's run.**  Started on the
requested public length alone, the stream returns the emitter's *balanced* atom
stream beside the padded native width and the scheduled size cap.  The only
premises are the executable presentation, the schedule diagonal and the nested
structural compiler's own run — no runner, no callback, no immediate. -/
theorem inverseDescriptionAtomStreamRuns_ofCompiler
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      InverseCompilerRuns contracts clockDepth machine advantageExponent pcp
        compilerBits compilerFuel) :
    InverseDescriptionAtomStreamRuns contracts clockDepth machine
      advantageExponent
      (inverseAtomStreamProgram contracts clockDepth machine advantageExponent
        pcp)
      (inverseAtomStreamBits contracts clockDepth machine advantageExponent pcp
        compilerBits)
      (inverseAtomStreamFuel contracts clockDepth machine advantageExponent pcp
        compilerFuel) := by
  intro target hlarge
  have hdiag := hdiagonal target hlarge
  have hatoms :=
    inverseScheduleAtoms_of_presentation contracts clockDepth machine
      advantageExponent pcp hpresentation target
  have hrange :=
    run_structuralAtomRangeProgram_ofCompiler pcp
      (inverseScheduleInput contracts clockDepth machine advantageExponent
        target)
      target (inverseScheduleBound contracts clockDepth advantageExponent target)
      (compilerBits target) (compilerFuel target)
      (rangeBits_positive contracts clockDepth machine advantageExponent pcp
        compilerBits target)
      (rangeBits_length contracts clockDepth machine advantageExponent pcp
        compilerBits target)
      (rangeBits_range contracts clockDepth machine advantageExponent pcp
        compilerBits target)
      (rangeBits_list contracts clockDepth machine advantageExponent pcp
        compilerBits target)
      (rangeBits_call contracts clockDepth machine advantageExponent pcp
        compilerBits target)
      (fun index hindex =>
        rangeBits_callee contracts clockDepth machine advantageExponent pcp
          compilerBits target index hindex)
      (hcompiler target)
  rw [hatoms] at hrange
  refine Eq.trans ?_
    (congrArg some
      (descriptionAtomTailOutput_ofRegisters contracts clockDepth machine
        advantageExponent target hdiag))
  exact run_occurrenceStage
    (run_publishedScheduleNumeralBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target target)
    (run_occurrenceStage
      (run_inverseCodeFrameAdapterProgram contracts clockDepth machine
        advantageExponent pcp hpresentation compilerBits compilerFuel hcompiler
        target target hdiag)
      (run_occurrenceStage
        (run_preserveRightProgram
          (structuralAtomRangeProgram structuralAtomCalleeProgram) target _ _
          (generatedBalancedRangeInput
            (inverseAtomCount contracts clockDepth machine advantageExponent pcp
              target)
            (inverseAtomContext contracts clockDepth machine advantageExponent
              pcp target))
          (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target target)
          (inverseFrameAtoms contracts clockDepth machine advantageExponent
            target)
          hrange)
        (run_occurrenceStage
          (run_contextSwapProgram target
            (inverseFrameAtoms contracts clockDepth machine advantageExponent
              target)
            (publishedBankFrame (publishedHierarchyOuterPCP contracts clockDepth)
              (publishedPointwisePCPP contracts)
              (inverseBankRate contracts advantageExponent) target target))
          (run_occurrenceStage
            (run_preserveRightProgram
              (bankShapeNumeralProgram
                (inverseRequiredDegree contracts
                  (inverseCoreAdvantagePower advantageExponent)))
              target _ _
              (publishedBankFrame
                (publishedHierarchyOuterPCP contracts clockDepth)
                (publishedPointwisePCPP contracts)
                (inverseBankRate contracts advantageExponent) target target)
              (inverseFrameAtoms contracts clockDepth machine advantageExponent
                target)
              _
              (run_bankShapeNumeralProgram
                (inverseRequiredDegree contracts
                  (inverseCoreAdvantagePower advantageExponent))
                target (bankSourceLength target)
                (inverseBankWidth contracts clockDepth target)
                (inverseBankQueryCount contracts clockDepth target)
                (inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
                  (publishedPointwisePCPP contracts)
                  (inverseBankRate contracts advantageExponent)
                  (sourceIndexOfLength target))
                target))
            (run_descriptionAtomTailProgram target
              (inverseFrameAtoms contracts clockDepth machine advantageExponent
                target)
              (inverseBankWidth contracts clockDepth target)
              (inverseBankQueryCount contracts clockDepth target)
              (inverseBankBound contracts clockDepth advantageExponent
                target))))))

/-! ## 6. The bank cluster at presentation, diagonal and query counts -/

/-- **The tower's side condition is the cluster's own named condition.**
`SelectiveCountCasesInverse.inverseCompilerRuns_closed` asks for positive
scheduled query counts *at the presented PCP*; a presentation makes those the
published outer PCP's own, which is exactly
`BankScheduledRowStageClosure.InverseScheduledQueryCounts`. -/
theorem presentedQueryCount_pos (contracts : PublishedContracts)
    (clockDepth : ℕ) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hcounts : InverseScheduledQueryCounts contracts clockDepth
      advantageExponent) :
    ∀ target : ℕ,
      0 <
        pcp.queryCount
          (inverseScheduleLength contracts clockDepth advantageExponent
            target) := by
  intro target
  rw [presentsPaddedOuterPCP_queryCount hpresentation]
  exact hcounts target

set_option maxHeartbeats 1600000 in
-- The statement carries the atom stream's own envelopes at the closed tower, so
-- elaborating it alone exceeds the default budget.
/-- **The atom-stream premise, unconditional below the cluster.**  The nested
compiler's run is supplied by the closed sixteen-level tower of
`SelectiveCountCasesInverse.inverseCompilerRuns_closed`, so nothing constructive
is left: the premises are the executable presentation, the schedule diagonal and
the scheduled query counts. -/
theorem inverseDescriptionAtomStreamRuns_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (hcounts : InverseScheduledQueryCounts contracts clockDepth
      advantageExponent) :
    InverseDescriptionAtomStreamRuns contracts clockDepth machine
      advantageExponent
      (inverseAtomStreamProgram contracts clockDepth machine advantageExponent
        pcp)
      (inverseAtomStreamBits contracts clockDepth machine advantageExponent pcp
        (inverseClosedCompilerBits contracts clockDepth machine advantageExponent
          pcp
          (presentedQueryCount_pos contracts clockDepth advantageExponent pcp
            hpresentation hcounts)))
      (inverseAtomStreamFuel contracts clockDepth machine advantageExponent pcp
        (inverseClosedCompilerFuel contracts clockDepth machine advantageExponent
          pcp
          (presentedQueryCount_pos contracts clockDepth advantageExponent pcp
            hpresentation hcounts))) :=
  inverseDescriptionAtomStreamRuns_ofCompiler contracts clockDepth machine
    advantageExponent pcp hpresentation hdiagonal _ _
    (inverseCompilerRuns_closed contracts clockDepth machine advantageExponent
      pcp
      (presentedQueryCount_pos contracts clockDepth advantageExponent pcp
        hpresentation hcounts))

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's encoder premise at the whole closed stream, so
-- elaborating it alone exceeds the default budget.
/-- **The Case-2 occurrence encoder, discharged.**  The last constructive
premise of the bank cluster is gone: one fixed program emits the substituted
circuit's encoding at every scheduled target, given only the executable
presentation, the schedule diagonal and the scheduled query counts. -/
theorem inverseScheduledOccurrenceEncoding_ofPresentation
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (hcounts : InverseScheduledQueryCounts contracts clockDepth
      advantageExponent) :
    InverseScheduledOccurrenceEncoding contracts clockDepth machine
      advantageExponent
      (inverseClosedEncodingProgram contracts clockDepth machine
        advantageExponent
        (inverseAtomStreamProgram contracts clockDepth machine advantageExponent
          pcp))
      (inverseClosedEncodingBits contracts clockDepth machine advantageExponent
        (inverseAtomStreamBits contracts clockDepth machine advantageExponent pcp
          (inverseClosedCompilerBits contracts clockDepth machine
            advantageExponent pcp
            (presentedQueryCount_pos contracts clockDepth advantageExponent pcp
              hpresentation hcounts))))
      (inverseClosedEncodingFuel contracts clockDepth machine advantageExponent
        (inverseAtomStreamProgram contracts clockDepth machine advantageExponent
          pcp)
        (inverseAtomStreamFuel contracts clockDepth machine advantageExponent pcp
          (inverseClosedCompilerFuel contracts clockDepth machine
            advantageExponent pcp
            (presentedQueryCount_pos contracts clockDepth advantageExponent pcp
              hpresentation hcounts)))) :=
  inverseScheduledOccurrenceEncoding_ofAtomStream contracts clockDepth machine
    advantageExponent hdiagonal
    (inverseAtomStreamProgram contracts clockDepth machine advantageExponent pcp)
    _ _
    (inverseDescriptionAtomStreamRuns_ofPresentation contracts clockDepth machine
      advantageExponent pcp hpresentation hdiagonal hcounts)

set_option maxHeartbeats 1600000 in
-- The statement is the cluster's whole three-way conjunction, so elaborating it
-- alone exceeds the default budget.
/-- **The bank cluster, closed.**  The four-premise
`RuntimeCaseTwoOccurrenceEncodingClosure.inverse_clusterResiduals_ofEncoding`
had one constructive premise, and it is now a theorem.  What remains of the
whole projection-table, Case-1 and Case-2 residual cluster is the executable
presentation of the padded outer PCP, the onset-restricted schedule diagonal and
the scheduled query counts — and nothing else.  The concrete chain witnesses are
recovered by applying `inverse_clusterResiduals_ofEncoding` directly to the
encoder of §6. -/
theorem inverse_clusterResiduals_ofPresentation (contracts : PublishedContracts)
    (clockDepth : ℕ) (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (hdiagonal : ∀ target : ℕ,
      inverseCaseOneTargetOnset contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        advantageExponent ≤ target →
      target = inverseScheduleLength contracts clockDepth advantageExponent
        target)
    (hcounts : InverseScheduledQueryCounts contracts clockDepth
      advantageExponent) :
    ∃ (caseOne caseTwo : NPOracleProgram)
      (chainBits chainFuel : LanguageEvaluationRequest → ℕ),
      InverseAtomTableRuns contracts clockDepth machine advantageExponent pcp
          (inverseBankTableProgram contracts clockDepth machine pcp)
          (inverseBankTableBits contracts clockDepth machine advantageExponent
            pcp)
          (inverseBankTableFuel contracts clockDepth machine advantageExponent
            pcp) ∧
        InverseCaseOnePointRuns contracts clockDepth machine advantageExponent
          caseOne chainBits chainFuel ∧
        InverseCaseTwoPointRuns contracts clockDepth machine advantageExponent
          caseTwo chainBits chainFuel :=
  ⟨_, _, _, _,
    inverse_clusterResiduals_ofEncoding contracts clockDepth machine
      advantageExponent pcp hpresentation hdiagonal _ _ _ hcounts
      (inverseScheduledOccurrenceEncoding_ofPresentation contracts clockDepth
        machine advantageExponent pcp hpresentation hdiagonal hcounts)⟩

end NearCubicWires.InverseDescriptionAtomStream
