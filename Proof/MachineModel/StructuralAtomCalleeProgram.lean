import Proof.MachineModel.BoundedOracleStructuralSelectiveProgram
import Proof.MachineModel.StructuralAtomEmitterLoopProgram

namespace NearCubicWires.StructuralAtomCalleeProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The response projection -/

/-- The pointwise runner returns `pair length atom`; the loop's callee returns
the atom. -/
def structuralAtomTakeRightProgram : NPOracleProgram :=
  [ .unpairRight 0 0 1
  , .halt 0
  ]

@[simp] theorem structuralAtomTakeRightProgram_oracleFree :
    OracleFree structuralAtomTakeRightProgram := by
  rfl

theorem run_structuralAtomTakeRightProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hright : natBitLength right ≤ maximumBits) :
    runNPOracleProgram structuralAtomTakeRightProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some right := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := right) (by rfl) rfl
    (by simp [initialNPOracleState]) hright]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hright

/-! ## 2. The callee, executed from the compiler's run -/

def structuralAtomCalleeProgram : NPOracleProgram :=
  linkPrograms structuralFormulaProgram structuralAtomTakeRightProgram

theorem structuralAtomCalleeProgram_oracleFree :
    OracleFree structuralAtomCalleeProgram :=
  oracleFree_linkPrograms structuralFormulaProgram_oracleFree
    structuralAtomTakeRightProgram_oracleFree

def structuralAtomCalleeBits (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits : ℕ) : ℕ :=
  occurrenceStageBits machineInputLength
    (structuralFormulaPipelineBits machineInputLength outputs width count bound
      index compilerBits)
    (natBitLength
      (structuralFormulaResponseCode outputs width count bound index))

def structuralAtomCalleeFuel (outputs : List ℕ)
    (width count bound index compilerFuel : ℕ) : ℕ :=
  linkFuel structuralAtomTakeRightProgram
    (structuralFormulaPipelineFuel outputs width count bound index compilerFuel)
    2

/-- **The callee, executed.**  From the generated request body the fixed stream
returns exactly the canonical structural atom at that global index, modulo one
run of the nested compiler on its own frame. -/
theorem run_structuralAtomCalleeProgram
    (machineInputLength : ℕ) (outputs : List ℕ)
    (width count bound index compilerBits compilerFuel : ℕ)
    (hcompiler :
      runNPOracleProgram selectiveCountCasesProgram compilerBits compilerFuel
          (initialNPOracleState machineInputLength <|
            structuralCompilerCoreInput outputs width count bound index) =
        some
          (selectiveWireCode
            (selectiveCompileTableBoundedOracleVerifier outputs width count
              bound (index - descriptionWidth width bound)))) :
    runNPOracleProgram structuralAtomCalleeProgram
        (structuralAtomCalleeBits machineInputLength outputs width count bound
          index compilerBits)
        (structuralAtomCalleeFuel outputs width count bound index compilerFuel)
        (initialNPOracleState machineInputLength
          (structuralFormulaRequestCode outputs width count bound index)) =
      some
        (tableBoundedOracleStructuralFormulaAtomAt outputs width count bound
          index) := by
  refine run_occurrenceStage
    (run_structuralFormulaProgram_of_compiler_run machineInputLength outputs
      width count bound index compilerBits compilerFuel hcompiler) ?_
  exact run_structuralAtomTakeRightProgram machineInputLength
    (tableBoundedOracleStructuralFormulaLength outputs width count bound)
    (tableBoundedOracleStructuralFormulaAtomAt outputs width count bound index)
    (natBitLength_mono (Nat.right_le_pair _ _))

/-! ## 3. The loop's per-index hypothesis -/

/-- The callee's fuel as a function of the generated request, the shape the
balanced caller of `StructuralAtomEmitterLoopProgram` consumes. -/
def structuralAtomCalleeRequestFuel (outputs : List ℕ) (width count bound : ℕ)
    (compilerFuel : ℕ → ℕ) (request : ℕ) : ℕ :=
  structuralAtomCalleeFuel outputs width count bound
    (structuralAtomRequestIndex request)
    (compilerFuel (structuralAtomRequestIndex request))

/-- The compiler-execution premise at one executable projection PCP, one public
input length, and one global formula index: the only statement about
`selectiveCountCasesProgram` this fleet still owes. -/
def StructuralCompilerRunsAt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound index compilerBits compilerFuel : ℕ) : Prop :=
  runNPOracleProgram selectiveCountCasesProgram compilerBits compilerFuel
      (initialNPOracleState machineInputLength <|
        structuralCompilerCoreInput (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound index) =
    some
      (selectiveWireCode
        (selectiveCompileTableBoundedOracleVerifier
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound
          (index - descriptionWidth (pcp.nativeWidth n) bound)))

/-- **The loop's per-index hypothesis, from the compiler's run.**  The callee
started on the request body generated for one global index returns exactly the
atom the loop expects there. -/
theorem run_structuralAtomCalleeProgram_index
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (machineInputLength bound index compilerBits : ℕ)
    (compilerFuel : ℕ → ℕ)
    (hcompiler :
      StructuralCompilerRunsAt pcp input machineInputLength bound index
        compilerBits (compilerFuel index)) :
    runNPOracleProgram structuralAtomCalleeProgram
        (structuralAtomCalleeBits machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound index compilerBits)
        (structuralAtomCalleeRequestFuel (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound compilerFuel
          (balancedRangeRequestAtom machineInputLength index
            (structuralAtomContext pcp input bound)))
        (initialNPOracleState machineInputLength
          (Nat.pair index (structuralAtomContext pcp input bound))) =
      some (structuralAtomValue pcp input bound index) := by
  have hindex :
      structuralAtomRequestIndex
          (balancedRangeRequestAtom machineInputLength index
            (structuralAtomContext pcp input bound)) =
        index :=
    structuralAtomRequestIndex_atom machineInputLength index
      (structuralAtomContext pcp input bound)
  rw [structuralAtomCalleeRequestFuel, hindex]
  exact run_structuralAtomCalleeProgram machineInputLength
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound index compilerBits (compilerFuel index) hcompiler

/-! ## 4. The structural atom emitter at any public length -/

/-- The generated request list of the loop enumerates the canonical atom
schedule at *every* public input length, not only the PCP input's own. -/
private theorem structuralAtomRequests_map_at
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound : ℕ) :
    (balancedRangeRequestAtoms machineInputLength
          (structuralAtomContext pcp input bound) 0
          (structuralAtomCount pcp input bound)).map
        (fun request =>
          structuralAtomValue pcp input bound
            (structuralAtomRequestIndex request)) =
      boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound := by
  have hrequests :
      balancedRangeRequestAtoms machineInputLength
          (structuralAtomContext pcp input bound) 0
          (structuralAtomCount pcp input bound) =
        tableBoundedOracleStructuralFormulaRequests machineInputLength
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound :=
    rfl
  have houtput :
      (fun request =>
          structuralAtomValue pcp input bound
            (structuralAtomRequestIndex request)) =
        tableBoundedOracleStructuralFormulaRequestOutput
          (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
          (pcp.queryCount n) bound :=
    rfl
  rw [hrequests, houtput, tableBoundedOracleStructuralFormulaRequests_outputs,
    tableBoundedOracleStructuralFormulaLength_runnerOutputs,
    map_range_tableBoundedOracleStructuralFormulaAtomAt]

/-- **The structural atom emitter at an executable projection PCP and any
public length.**  This is `StructuralAtomEmitterLoopProgram`'s §4 with the
public input length freed: modulo one run of one pointwise callee per global
formula index, the fixed stream returns the tagged canonical atom schedule
beside the retained point code. -/
theorem run_structuralAtomEmitterProgram_table_at
    (callee : NPOracleProgram) {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound pointCode : ℕ)
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
    runNPOracleProgram (structuralAtomEmitterProgram callee)
        (structuralAtomEmitterBits rangeBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (structuralAtomEmitterFuel callee machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) calleeFuel
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (initialNPOracleState machineInputLength
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  have hmap := structuralAtomRequests_map_at pcp input machineInputLength bound
  rw [← hmap]
  refine run_structuralAtomEmitterProgram callee machineInputLength
    (structuralAtomCount pcp input bound)
    (structuralAtomContext pcp input bound) pointCode calleeFuel
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

/-- **The structural atom emitter from the compiler's run alone.**  The fixed
stream returns the tagged canonical atom schedule beside the retained point
code; the only per-index premise left is the nested compiler's own run. -/
theorem run_structuralAtomEmitterProgram_ofCompiler
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound pointCode : ℕ)
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
    runNPOracleProgram (structuralAtomEmitterProgram structuralAtomCalleeProgram)
        (structuralAtomEmitterBits rangeBits machineInputLength
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (structuralAtomEmitterFuel structuralAtomCalleeProgram
          machineInputLength (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound)
          (structuralAtomCalleeRequestFuel (projectionRunnerCallOutputs pcp input)
            (pcp.nativeWidth n) (pcp.queryCount n) bound compilerFuel)
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (initialNPOracleState machineInputLength
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  refine run_structuralAtomEmitterProgram_table_at structuralAtomCalleeProgram
    pcp input machineInputLength bound pointCode _ hpositive hlengthBits
    hrangeBits hlistBits hcallBits ?_
  intro index hindex
  exact run_bits_mono
    (run_structuralAtomCalleeProgram_index pcp input machineInputLength bound
      index (compilerBits index) compilerFuel (hcompiler index hindex))
    (hcalleeBits index hindex)

/-! ## 5. The branch query, decided from the compiler's run -/

/-- **The branch query from the compiler's run alone.**  The branch selector of
`CanonicalBranchSelectorProgram` is executed with no query immediate, no
list-valued emitter premise, and no per-index callee premise: only the nested
structural compiler's own run, once per global formula index. -/
theorem run_emittedBranchSelectorProgram_ofCompiler
    {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (machineInputLength bound pointCode : ℕ)
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
    runNPOracleProgram
        (emittedBranchSelectorProgram
          (structuralAtomEmitterProgram structuralAtomCalleeProgram))
        (emittedBranchSelectorBits pcp.toSemantic input bound machineInputLength
          pointCode
          (structuralAtomEmitterBits rangeBits machineInputLength
            (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound) pointCode
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)))
        (emittedBranchSelectorFuel pcp.toSemantic input bound
          (structuralAtomEmitterFuel structuralAtomCalleeProgram
            machineInputLength (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound)
            (structuralAtomCalleeRequestFuel
              (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
              (pcp.queryCount n) bound compilerFuel)
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)))
        (initialNPOracleState machineInputLength
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodedSat
            (boundedOracleRecoveryCode pcp.toSemantic input bound)).toNat
          pointCode) :=
  run_emittedBranchSelectorProgram pcp.toSemantic input bound machineInputLength
    (Nat.pair
      (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
        (structuralAtomContext pcp input bound))
      pointCode)
    pointCode
    (structuralAtomEmitterBits rangeBits machineInputLength
      (structuralAtomCount pcp input bound)
      (structuralAtomContext pcp input bound) pointCode
      (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
    (structuralAtomEmitterFuel structuralAtomCalleeProgram machineInputLength
      (structuralAtomCount pcp input bound)
      (structuralAtomContext pcp input bound)
      (structuralAtomCalleeRequestFuel (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound compilerFuel)
      (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
    (structuralAtomEmitterProgram structuralAtomCalleeProgram)
    (run_structuralAtomEmitterProgram_ofCompiler pcp input machineInputLength
      bound pointCode compilerBits compilerFuel hpositive hlengthBits hrangeBits
      hlistBits hcallBits hcalleeBits hcompiler)

end NearCubicWires.StructuralAtomCalleeProgram
