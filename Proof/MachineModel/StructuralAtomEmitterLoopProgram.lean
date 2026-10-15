import Proof.MachineModel.BankRecoveryCodeProgram
import Proof.Circuits.BoundedOracleStructuralFormulaTable
import Proof.MachineModel.CanonicalBalancedFlattenProgram

namespace NearCubicWires.StructuralAtomEmitterLoopProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralFormulaTable
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedFlattenProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Dropping the context the range generator retains -/

/-- The generated range returns `pair requestTree context`; the balanced caller
consumes the tree alone. -/
def structuralAtomTakeLeftProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem structuralAtomTakeLeftProgram_oracleFree :
    OracleFree structuralAtomTakeLeftProgram := by
  rfl

theorem run_structuralAtomTakeLeftProgram
    {maximumBits : ℕ} (inputLength left right : ℕ)
    (hleft : natBitLength left ≤ maximumBits) :
    runNPOracleProgram structuralAtomTakeLeftProgram maximumBits 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left) (by rfl) rfl
    (by simp [initialNPOracleState]) hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hleft

/-! ## 2. The generated index loop -/

/-- **The index loop.**  Generate the balanced request tree for
`0, …, count - 1` at one retained context, then run one callee per request. -/
def structuralAtomRangeProgram (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram
    (linkPrograms structuralAtomTakeLeftProgram (balancedCallProgram callee))

theorem structuralAtomRangeProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (structuralAtomRangeProgram callee) :=
  oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
    (oracleFree_linkPrograms structuralAtomTakeLeftProgram_oracleFree
      (balancedCallProgram_oracleFree hcallee))

def structuralAtomRangeFuel (callee : NPOracleProgram)
    (inputLength count context : ℕ) (calleeFuel : ℕ → ℕ) : ℕ :=
  linkFuel
    (linkPrograms structuralAtomTakeLeftProgram (balancedCallProgram callee))
    (generatedBalancedRangeFuel inputLength count context) <|
    linkFuel (balancedCallProgram callee) 2
      (balancedCallFuel callee calleeFuel
        (balancedRangeRequestAtoms inputLength context 0 count))

/-- **The index loop, executed.**  Every hypothesis is charged at one shared
width, so the loop composes with `run_bits_mono` at any wider stage. -/
theorem run_structuralAtomRangeProgram
    (callee : NPOracleProgram) {maximumBits : ℕ}
    (inputLength count context : ℕ) (calleeFuel output : ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hlengthBits : natBitLength inputLength ≤ maximumBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count context ≤
        maximumBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms inputLength context 0 count)) ≤
        maximumBits)
    (hcallBits :
      balancedCallRequiredBits output
          (balancedRangeRequestAtoms inputLength context 0 count) ≤
        maximumBits)
    (hcallee : ∀ request,
      request ∈ balancedRangeRequestAtoms inputLength context 0 count →
      runNPOracleProgram callee maximumBits (calleeFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (output request)) :
    runNPOracleProgram (structuralAtomRangeProgram callee) maximumBits
        (structuralAtomRangeFuel callee inputLength count context calleeFuel)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count context)) =
      some
        (encodeBalancedList
          ((balancedRangeRequestAtoms inputLength context 0 count).map
            output)) := by
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength count context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some
          (Nat.pair
            (encodeBalancedList
              (balancedRangeRequestAtoms inputLength context 0 count))
            context) :=
    run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count context) hrangeBits
  have htake :
      runNPOracleProgram structuralAtomTakeLeftProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair
              (encodeBalancedList
                (balancedRangeRequestAtoms inputLength context 0 count))
              context)) =
        some
          (encodeBalancedList
            (balancedRangeRequestAtoms inputLength context 0 count)) :=
    run_structuralAtomTakeLeftProgram inputLength _ context hlistBits
  have hcall :
      runNPOracleProgram (balancedCallProgram callee) maximumBits
          (balancedCallFuel callee calleeFuel
            (balancedRangeRequestAtoms inputLength context 0 count))
          (initialNPOracleState inputLength
            (encodeBalancedList
              (balancedRangeRequestAtoms inputLength context 0 count))) =
        some
          (encodeBalancedList
            ((balancedRangeRequestAtoms inputLength context 0 count).map
              output)) :=
    run_balancedCallProgram_from inputLength
      (balancedRangeRequestAtoms inputLength context 0 count) calleeFuel output
      hcallBits hcallee
  exact run_linkPrograms hpositive hlengthBits hrange
    (run_linkPrograms hpositive hlengthBits htake hcall)

/-! ## 3. The emitter: the loop's list, retagged, beside the point code -/

/-- **The structural atom emitter.**  One fixed instruction stream carrying no
index and no schedule immediate: the generated index loop under a
point-preserving wrapper, then the balanced-to-tagged converter under a second
one. -/
def structuralAtomEmitterProgram (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (preserveRightProgram (structuralAtomRangeProgram callee))
    (preserveRightProgram balancedToTaggedProgram)

theorem structuralAtomEmitterProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (structuralAtomEmitterProgram callee) :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree _
      (structuralAtomRangeProgram_oracleFree hcallee))
    (preserveRightProgram_oracleFree _ balancedToTaggedProgram_oracleFree)

def structuralAtomEmitterFuel (callee : NPOracleProgram)
    (inputLength count context : ℕ) (calleeFuel : ℕ → ℕ) (atoms : List ℕ) :
    ℕ :=
  linkFuel (preserveRightProgram balancedToTaggedProgram)
    (preserveRightFuel
      (structuralAtomRangeFuel callee inputLength count context calleeFuel))
    (preserveRightFuel (balancedToTaggedFuel inputLength atoms))

def structuralAtomEmitterBits
    (rangeBits inputLength count context pointCode : ℕ) (atoms : List ℕ) :
    ℕ :=
  occurrenceStageBits inputLength
    (preserveRightBits rangeBits
      (generatedBalancedRangeInput count context) pointCode
      (encodeBalancedList atoms))
    (preserveRightBits (balancedToTaggedBits inputLength atoms)
      (encodeBalancedList atoms) pointCode (encodeTaggedList atoms))

set_option maxHeartbeats 800000 in
-- The two nested preserving wrappers force elaboration of the loop's fuel.
/-- **The emitter, executed.**  From the loop's input frame the stream returns
exactly the tagged atom stream beside the retained point code — the shape
`BankRecoveryCodeProgram.run_emittedBranchSelectorProgram` consumes. -/
theorem run_structuralAtomEmitterProgram
    (callee : NPOracleProgram) {rangeBits : ℕ}
    (inputLength count context pointCode : ℕ) (calleeFuel output : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength inputLength ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count context ≤ rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms inputLength context 0 count)) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits output
          (balancedRangeRequestAtoms inputLength context 0 count) ≤
        rangeBits)
    (hcallee : ∀ request,
      request ∈ balancedRangeRequestAtoms inputLength context 0 count →
      runNPOracleProgram callee rangeBits (calleeFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (output request)) :
    runNPOracleProgram (structuralAtomEmitterProgram callee)
        (structuralAtomEmitterBits rangeBits inputLength count context pointCode
          ((balancedRangeRequestAtoms inputLength context 0 count).map output))
        (structuralAtomEmitterFuel callee inputLength count context calleeFuel
          ((balancedRangeRequestAtoms inputLength context 0 count).map output))
        (initialNPOracleState inputLength
          (Nat.pair (generatedBalancedRangeInput count context) pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            ((balancedRangeRequestAtoms inputLength context 0 count).map
              output))
          pointCode) := by
  set atoms :=
    (balancedRangeRequestAtoms inputLength context 0 count).map output
    with hatoms
  exact run_occurrenceStage
    (run_preserveRightProgram (structuralAtomRangeProgram callee) inputLength
      rangeBits
      (structuralAtomRangeFuel callee inputLength count context calleeFuel)
      (generatedBalancedRangeInput count context) pointCode
      (encodeBalancedList atoms)
      (run_structuralAtomRangeProgram callee inputLength count context
        calleeFuel output hpositive hlengthBits hrangeBits hlistBits hcallBits
        hcallee))
    (run_preserveRightProgram balancedToTaggedProgram inputLength
      (balancedToTaggedBits inputLength atoms)
      (balancedToTaggedFuel inputLength atoms) (encodeBalancedList atoms)
      pointCode (encodeTaggedList atoms)
      (run_balancedToTaggedProgram inputLength
        (balancedToTaggedBits inputLength atoms) atoms (Nat.le_refl _)))

/-! ## 4. The structural formula atoms of an executable projection PCP -/

/-- Global formula index recovered from one generated request. -/
def structuralAtomRequestIndex (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

@[simp] theorem structuralAtomRequestIndex_atom
    (inputLength index context : ℕ) :
    structuralAtomRequestIndex
        (balancedRangeRequestAtom inputLength index context) = index := by
  simp [structuralAtomRequestIndex, balancedRangeRequestAtom]

/-- The shared public context of every generated formula-atom request. -/
def structuralAtomContext
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  tableBoundedOracleStructuralFormulaContext
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound

/-- The exact number of global formula indices. -/
def structuralAtomCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  tableBoundedOracleStructuralFormulaLength
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound

/-- The atom the pointwise callee must return at one global index. -/
def structuralAtomValue
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound index : ℕ) : ℕ :=
  tableBoundedOracleStructuralFormulaAtomAt
    (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
    (pcp.queryCount n) bound index

private theorem structuralAtomRequests_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    balancedRangeRequestAtoms n (structuralAtomContext pcp input bound) 0
        (structuralAtomCount pcp input bound) =
      tableBoundedOracleStructuralFormulaRequests n
        (projectionRunnerCallOutputs pcp input) (pcp.nativeWidth n)
        (pcp.queryCount n) bound :=
  rfl

/-- **The loop's list is the canonical structural atom schedule.** -/
theorem structuralAtomRequests_map
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (balancedRangeRequestAtoms n (structuralAtomContext pcp input bound) 0
          (structuralAtomCount pcp input bound)).map
        (fun request =>
          structuralAtomValue pcp input bound
            (structuralAtomRequestIndex request)) =
      boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound := by
  rw [structuralAtomRequests_eq]
  exact tableBoundedOracleStructuralFormulaRequests_runnerOutputs pcp input
    bound

set_option maxHeartbeats 800000 in
-- The emitter's width and fuel are nested preserving-link terms.
/-- **The structural atom emitter at an executable projection PCP.**  Modulo
one run of one pointwise callee per global formula index, the fixed stream
returns exactly the tagged canonical atom schedule beside the retained point
code. -/
theorem run_structuralAtomEmitterProgram_table
    (callee : NPOracleProgram) {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound pointCode : ℕ) (calleeFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength n ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits n (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms n
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms n (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcallee : ∀ index, index < structuralAtomCount pcp input bound →
      runNPOracleProgram callee rangeBits
          (calleeFuel
            (balancedRangeRequestAtom n index
              (structuralAtomContext pcp input bound)))
          (initialNPOracleState n
            (Nat.pair index (structuralAtomContext pcp input bound))) =
        some (structuralAtomValue pcp input bound index)) :
    runNPOracleProgram (structuralAtomEmitterProgram callee)
        (structuralAtomEmitterBits rangeBits n
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) pointCode
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (structuralAtomEmitterFuel callee n
          (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) calleeFuel
          (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
        (initialNPOracleState n
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodeTaggedList
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
          pointCode) := by
  have hmap := structuralAtomRequests_map pcp input bound
  rw [← hmap]
  refine run_structuralAtomEmitterProgram callee n
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
        (balancedRangeRequestAtom n index
          (structuralAtomContext pcp input bound))).1 = n := by
    simp [balancedRangeRequestAtom]
  have hright :
      (Nat.unpair
        (balancedRangeRequestAtom n index
          (structuralAtomContext pcp input bound))).2 =
        Nat.pair index (structuralAtomContext pcp input bound) := by
    simp [balancedRangeRequestAtom]
  rw [hleft, hright]
  exact hcallee index (List.mem_range.mp hindex)

/-! ## 5. The branch query, decided from the pointwise callee -/

set_option maxHeartbeats 1600000 in
-- The selector's width and fuel nest the emitter's own link terms.
/-- **The branch query from one pointwise premise.**  Composing §4 with
`BankRecoveryCodeProgram.run_emittedBranchSelectorProgram`, the branch selector
of `CanonicalBranchSelectorProgram` is executed with *no* query immediate and
with a single per-index hypothesis on the pointwise structural callee. -/
theorem run_emittedBranchSelectorProgram_ofLoop
    (callee : NPOracleProgram) {rangeBits : ℕ}
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound pointCode : ℕ) (calleeFuel : ℕ → ℕ)
    (hpositive : 1 ≤ rangeBits)
    (hlengthBits : natBitLength n ≤ rangeBits)
    (hrangeBits :
      generatedBalancedRangeRequiredBits n (structuralAtomCount pcp input bound)
          (structuralAtomContext pcp input bound) ≤
        rangeBits)
    (hlistBits :
      natBitLength
          (encodeBalancedList
            (balancedRangeRequestAtoms n
              (structuralAtomContext pcp input bound) 0
              (structuralAtomCount pcp input bound))) ≤
        rangeBits)
    (hcallBits :
      balancedCallRequiredBits
          (fun request =>
            structuralAtomValue pcp input bound
              (structuralAtomRequestIndex request))
          (balancedRangeRequestAtoms n (structuralAtomContext pcp input bound) 0
            (structuralAtomCount pcp input bound)) ≤
        rangeBits)
    (hcallee : ∀ index, index < structuralAtomCount pcp input bound →
      runNPOracleProgram callee rangeBits
          (calleeFuel
            (balancedRangeRequestAtom n index
              (structuralAtomContext pcp input bound)))
          (initialNPOracleState n
            (Nat.pair index (structuralAtomContext pcp input bound))) =
        some (structuralAtomValue pcp input bound index)) :
    runNPOracleProgram
        (emittedBranchSelectorProgram (structuralAtomEmitterProgram callee))
        (emittedBranchSelectorBits pcp.toSemantic input bound n pointCode
          (structuralAtomEmitterBits rangeBits n
            (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound) pointCode
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)))
        (emittedBranchSelectorFuel pcp.toSemantic input bound
          (structuralAtomEmitterFuel callee n
            (structuralAtomCount pcp input bound)
            (structuralAtomContext pcp input bound) calleeFuel
            (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound)))
        (initialNPOracleState n
          (Nat.pair
            (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
              (structuralAtomContext pcp input bound))
            pointCode)) =
      some
        (Nat.pair
          (encodedSat
            (boundedOracleRecoveryCode pcp.toSemantic input bound)).toNat
          pointCode) :=
  run_emittedBranchSelectorProgram pcp.toSemantic input bound n
    (Nat.pair
      (generatedBalancedRangeInput (structuralAtomCount pcp input bound)
        (structuralAtomContext pcp input bound))
      pointCode)
    pointCode
    (structuralAtomEmitterBits rangeBits n (structuralAtomCount pcp input bound)
      (structuralAtomContext pcp input bound) pointCode
      (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
    (structuralAtomEmitterFuel callee n (structuralAtomCount pcp input bound)
      (structuralAtomContext pcp input bound) calleeFuel
      (boundedOracleStructuralFormulaAtoms pcp.toSemantic input bound))
    (structuralAtomEmitterProgram callee)
    (run_structuralAtomEmitterProgram_table callee pcp input bound pointCode
      calleeFuel hpositive hlengthBits hrangeBits hlistBits hcallBits hcallee)

end NearCubicWires.StructuralAtomEmitterLoopProgram
