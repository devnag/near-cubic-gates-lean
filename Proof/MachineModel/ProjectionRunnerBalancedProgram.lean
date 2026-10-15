import Proof.Circuits.BoundedOracleStructuralCircuit
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.ProjectionRunnerAtomProgram

/-!
# Canonical balanced projection-runner pipeline

The projection verifier has one public row-major schedule.  This module
identifies that typed schedule with the atoms reconstructed by the fixed range
callee, then composes the two canonical balanced calls.  No host-built call
list, linked spine, or compatibility codec exists at the executable boundary.
-/

namespace NearCubicWires.ProjectionRunnerBalancedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerAtomProgram
open NearCubicWires.ProjectionRunnerCallProgram
open NearCubicWires.VerifiedLinker

/-- Canonical row-major query schedule: query coordinate first, bit coordinate
second. -/
def projectionQueryCalls
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ProjectionRunnerCall :=
  (List.ofFn fun query : Fin (pcp.queryCount n) =>
    List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
      .query (pcp.queryRequest input query bit)).flatten

/-- Decision rows use the increasing binary order of `allRandomness`. -/
def projectionDecisionCalls
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ProjectionRunnerCall :=
  (allRandomness (pcp.nativeWidth n)).map fun randomness =>
    .decision (pcp.decisionRequest input randomness)

def projectionRunnerCalls
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ProjectionRunnerCall :=
  projectionQueryCalls pcp input ++ projectionDecisionCalls pcp input

def projectionRunnerOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (call : ProjectionRunnerCall) : ℕ :=
  call.output pcp

def projectionQueryTableOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ℕ :=
  (List.ofFn fun query : Fin (pcp.queryCount n) =>
    List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
      ProjectionRunnerCall.output pcp <|
        .query (pcp.queryRequest input query bit)).flatten

def projectionDecisionTableOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ℕ :=
  (allRandomness (pcp.nativeWidth n)).map fun randomness =>
    ProjectionRunnerCall.output pcp <|
      .decision (pcp.decisionRequest input randomness)

@[simp] theorem projectionQueryCalls_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionQueryCalls pcp input).length =
      pcp.queryCount n * pcp.nativeWidth n := by
  rw [projectionQueryCalls, List.length_flatten]
  have hlengths :
      (List.ofFn fun query : Fin (pcp.queryCount n) =>
        List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
          ProjectionRunnerCall.query
            (pcp.queryRequest input query bit)).map List.length =
        List.replicate (pcp.queryCount n) (pcp.nativeWidth n) := by
    rw [List.map_ofFn, ← List.ofFn_const]
    apply congrArg List.ofFn
    funext query
    simp
  rw [hlengths]
  simp

@[simp] theorem projectionDecisionCalls_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionDecisionCalls pcp input).length =
      2 ^ pcp.nativeWidth n := by
  simp [projectionDecisionCalls]

@[simp] theorem projectionRunnerCalls_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionRunnerCalls pcp input).length =
      pcp.queryCount n * pcp.nativeWidth n +
        2 ^ pcp.nativeWidth n := by
  simp [projectionRunnerCalls]

@[simp] theorem projectionQueryCalls_outputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionQueryCalls pcp input).map
        (projectionRunnerOutput pcp) =
      projectionQueryTableOutputs pcp input := by
  unfold projectionQueryCalls projectionQueryTableOutputs
  rw [List.map_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext query
  change
    (List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
      ProjectionRunnerCall.query
        (pcp.queryRequest input query bit)).map
          (projectionRunnerOutput pcp) =
      List.ofFn fun bit : Fin (pcp.nativeWidth n) =>
        ProjectionRunnerCall.output pcp
          (.query (pcp.queryRequest input query bit))
  rw [List.map_ofFn]
  rfl

@[simp] theorem projectionDecisionCalls_outputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionDecisionCalls pcp input).map
        (projectionRunnerOutput pcp) =
      projectionDecisionTableOutputs pcp input := by
  simp [projectionDecisionCalls, projectionDecisionTableOutputs,
    projectionRunnerOutput]

@[simp] theorem projectionRunnerCalls_outputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionRunnerCalls pcp input).map
        (projectionRunnerOutput pcp) =
      projectionQueryTableOutputs pcp input ++
        projectionDecisionTableOutputs pcp input := by
  simp [projectionRunnerCalls]

private theorem map_range_eq_ofFn
    {α : Type} (count : ℕ) (function : ℕ → α) :
    (List.range count).map function =
      List.ofFn fun index : Fin count => function index.val := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp

/-- Raw atoms in the exact typed query order. -/
def projectionRawQueryAtoms
    (inputArity inputCode width count : ℕ) : List ℕ :=
  ((List.range count).map fun query =>
    (List.range width).map fun bit =>
      projectionQueryAtomCode inputArity inputCode width count query bit).flatten

def projectionRawDecisionAtoms
    (inputArity inputCode width count : ℕ) : List ℕ :=
  (List.range (2 ^ width)).map fun randomnessCode =>
    projectionDecisionAtomCode inputArity inputCode width count randomnessCode

def projectionRawRunnerAtoms
    (inputArity inputCode width count : ℕ) : List ℕ :=
  projectionRawQueryAtoms inputArity inputCode width count ++
    projectionRawDecisionAtoms inputArity inputCode width count

private theorem projectionRawQueryAtomsPrefix_eq
    (inputArity inputCode width originalCount rows : ℕ)
    (hrows : rows ≤ originalCount) :
    (List.range (rows * width)).map
        (projectionRunnerAtomOutput inputArity inputCode width originalCount) =
      ((List.range rows).map fun query =>
        (List.range width).map fun bit =>
          projectionQueryAtomCode inputArity inputCode width originalCount
            query bit).flatten := by
  induction rows with
  | zero =>
      simp
  | succ rows inductionHypothesis =>
      have hrowsPrevious : rows ≤ originalCount := by omega
      rw [Nat.add_mul, List.range_add, List.map_append,
        inductionHypothesis hrowsPrevious, List.map_map, List.range_succ,
        List.map_append]
      simp only [List.map, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, one_mul]
      apply congrArg₂ (· ++ ·) rfl
      by_cases hwidthZero : width = 0
      · simp [hwidthZero]
      · apply List.map_congr_left
        intro bit hbit
        simp only [Function.comp_apply]
        exact projectionRunnerAtomOutput_query inputArity inputCode width
          originalCount rows bit (Nat.pos_of_ne_zero hwidthZero)
          (by omega) (List.mem_range.mp hbit)

/-- The range callee emits exactly the query rows followed by decision rows. -/
theorem projectionRunnerAtomOutputs_eq_raw
    (inputArity inputCode width count : ℕ) :
    (List.range (count * width + 2 ^ width)).map
        (projectionRunnerAtomOutput inputArity inputCode width count) =
      projectionRawRunnerAtoms inputArity inputCode width count := by
  rw [List.range_add, List.map_append,
    projectionRawRunnerAtoms,
    projectionRawQueryAtomsPrefix_eq inputArity inputCode width count count
      (le_refl count),
    List.map_map]
  apply congrArg₂ (· ++ ·) rfl
  apply List.map_congr_left
  intro randomnessCode _
  simp only [Function.comp_apply]
  exact projectionRunnerAtomOutput_decision inputArity inputCode width count
    randomnessCode

theorem projectionQueryCallAtoms_eq_raw
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionQueryCalls pcp input).map ProjectionRunnerCall.atom =
      projectionRawQueryAtoms n (encodeBitInput input)
        (pcp.nativeWidth n) (pcp.queryCount n) := by
  unfold projectionQueryCalls projectionRawQueryAtoms
  rw [List.map_flatten, List.map_ofFn,
    map_range_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext query
  simp only [Function.comp_apply]
  rw [List.map_ofFn, map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext bit
  exact (projectionQueryAtomCode_eq_callAtom pcp input query bit).symm

theorem projectionDecisionCallAtoms_eq_raw
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionDecisionCalls pcp input).map ProjectionRunnerCall.atom =
      projectionRawDecisionAtoms n (encodeBitInput input)
        (pcp.nativeWidth n) (pcp.queryCount n) := by
  unfold projectionDecisionCalls projectionRawDecisionAtoms allRandomness
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro randomnessCode hrandomnessCode
  simp only [Function.comp_apply]
  rw [← projectionDecisionAtomCode_eq_callAtom]
  congr 1
  exact encodeBitInput_testBit (List.mem_range.mp hrandomnessCode)

/-- Typed and raw atom schedules coincide at the sole balanced-call ABI. -/
theorem projectionRunnerCallAtoms_eq_raw
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionRunnerCalls pcp input).map ProjectionRunnerCall.atom =
      projectionRawRunnerAtoms n (encodeBitInput input)
        (pcp.nativeWidth n) (pcp.queryCount n) := by
  rw [projectionRunnerCalls, List.map_append,
    projectionQueryCallAtoms_eq_raw, projectionDecisionCallAtoms_eq_raw]
  rfl

def projectionRunnerCallAtoms
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ℕ :=
  (projectionRunnerCalls pcp input).map ProjectionRunnerCall.atom

def projectionRunnerCallOutputs
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ℕ :=
  (projectionRunnerCalls pcp input).map (projectionRunnerOutput pcp)

/-! ## Public range to typed call atoms -/

def projectionRunnerRangeCount
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (inputArity : ℕ) : ℕ :=
  pcp.queryCount inputArity * pcp.nativeWidth inputArity +
    2 ^ pcp.nativeWidth inputArity

def projectionRunnerRangeContext
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  projectionRunnerAtomContext input (pcp.nativeWidth n) (pcp.queryCount n)

def projectionRunnerRangeRequests
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : List ℕ :=
  balancedRangeRequestAtoms n (projectionRunnerRangeContext pcp input) 0
    (projectionRunnerRangeCount pcp n)

def projectionRunnerGeneratedAtomIndex (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

def projectionRunnerGeneratedAtomOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (request : ℕ) : ℕ :=
  projectionRunnerAtomOutput n (encodeBitInput input) (pcp.nativeWidth n)
    (pcp.queryCount n) (projectionRunnerGeneratedAtomIndex request)

def projectionRunnerGeneratedAtomFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (_input : BitInput n) (request : ℕ) : ℕ :=
  projectionRunnerAtomFuel (pcp.nativeWidth n) (pcp.queryCount n)
    (projectionRunnerGeneratedAtomIndex request)

def projectionRunnerGeneratedAtomBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (request : ℕ) : ℕ :=
  projectionRunnerAtomMaximumBits n (encodeBitInput input)
    (pcp.nativeWidth n) (pcp.queryCount n)
    (projectionRunnerGeneratedAtomIndex request)

@[simp] theorem projectionRunnerRangeCount_eq_calls_length
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    projectionRunnerRangeCount pcp n =
      (projectionRunnerCalls pcp input).length := by
  simp [projectionRunnerRangeCount]

/-- Applying the fixed atom constructor to the public range yields precisely
the typed heterogeneous call schedule. -/
theorem projectionRunnerRangeOutputs_eq_callAtoms
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    (projectionRunnerRangeRequests pcp input).map
        (projectionRunnerGeneratedAtomOutput pcp input) =
      projectionRunnerCallAtoms pcp input := by
  calc
    _ = (List.range (projectionRunnerRangeCount pcp n)).map
          (projectionRunnerAtomOutput n (encodeBitInput input)
            (pcp.nativeWidth n) (pcp.queryCount n)) := by
      unfold projectionRunnerRangeRequests
      rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro index _
      simp [projectionRunnerGeneratedAtomOutput,
        projectionRunnerGeneratedAtomIndex, balancedRangeRequestAtom]
    _ = projectionRawRunnerAtoms n (encodeBitInput input)
          (pcp.nativeWidth n) (pcp.queryCount n) := by
      simpa only [projectionRunnerRangeCount] using
        projectionRunnerAtomOutputs_eq_raw n (encodeBitInput input)
          (pcp.nativeWidth n) (pcp.queryCount n)
    _ = projectionRunnerCallAtoms pcp input := by
      exact (projectionRunnerCallAtoms_eq_raw pcp input).symm

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

/-! ## Canonical atom-construction balanced call -/

def projectionRunnerAtomCalleeBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  ((projectionRunnerRangeRequests pcp input).map
    (projectionRunnerGeneratedAtomBits pcp input)).foldr max 0

theorem run_projectionRunnerGeneratedAtom
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (index maximumBits : ℕ)
    (hbits :
      projectionRunnerGeneratedAtomBits pcp input
          (balancedRangeRequestAtom n index
            (projectionRunnerRangeContext pcp input)) ≤ maximumBits) :
    runNPOracleProgram projectionRunnerAtomProgram maximumBits
        (projectionRunnerGeneratedAtomFuel pcp input
          (balancedRangeRequestAtom n index
            (projectionRunnerRangeContext pcp input)))
        (initialNPOracleState
          (Nat.unpair (balancedRangeRequestAtom n index
            (projectionRunnerRangeContext pcp input))).1
          (Nat.unpair (balancedRangeRequestAtom n index
            (projectionRunnerRangeContext pcp input))).2) =
      some
        (projectionRunnerGeneratedAtomOutput pcp input
          (balancedRangeRequestAtom n index
            (projectionRunnerRangeContext pcp input))) := by
  have hmaximum :
      projectionRunnerAtomMaximumBits n (encodeBitInput input)
          (pcp.nativeWidth n) (pcp.queryCount n) index ≤ maximumBits := by
    simpa only [projectionRunnerGeneratedAtomBits,
      projectionRunnerGeneratedAtomIndex, balancedRangeRequestAtom,
      Nat.unpair_pair] using hbits
  have hrun :=
    run_bits_mono
      (run_projectionRunnerAtomProgram n (encodeBitInput input)
        (pcp.nativeWidth n) (pcp.queryCount n) index) hmaximum
  simpa only [projectionRunnerGeneratedAtomFuel,
    projectionRunnerGeneratedAtomOutput, projectionRunnerGeneratedAtomIndex,
    projectionRunnerRangeContext, projectionRunnerAtomContext,
    balancedRangeRequestAtom, Nat.unpair_pair] using hrun

def projectionRunnerAtomBalancedBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  max (projectionRunnerAtomCalleeBits pcp input) <|
    balancedCallRequiredBits
      (projectionRunnerGeneratedAtomOutput pcp input)
      (projectionRunnerRangeRequests pcp input)

def projectionRunnerAtomBalancedFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  balancedCallFuel projectionRunnerAtomProgram
    (projectionRunnerGeneratedAtomFuel pcp input)
    (projectionRunnerRangeRequests pcp input)

theorem run_projectionRunnerAtomBalancedProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    runNPOracleProgram (balancedCallProgram projectionRunnerAtomProgram)
        (projectionRunnerAtomBalancedBits pcp input)
        (projectionRunnerAtomBalancedFuel pcp input)
        (initialNPOracleState n
          (encodeBalancedList (projectionRunnerRangeRequests pcp input))) =
      some
        (encodeBalancedList (projectionRunnerCallAtoms pcp input)) := by
  let requests := projectionRunnerRangeRequests pcp input
  let output := projectionRunnerGeneratedAtomOutput pcp input
  change
    runNPOracleProgram (balancedCallProgram projectionRunnerAtomProgram)
        (max (projectionRunnerAtomCalleeBits pcp input)
          (balancedCallRequiredBits output requests))
        (balancedCallFuel projectionRunnerAtomProgram
          (projectionRunnerGeneratedAtomFuel pcp input) requests)
        (initialNPOracleState n (encodeBalancedList requests)) =
      some (encodeBalancedList (projectionRunnerCallAtoms pcp input))
  rw [← projectionRunnerRangeOutputs_eq_callAtoms pcp input]
  apply run_balancedCallProgram_from n requests
    (projectionRunnerGeneratedAtomFuel pcp input) output
  · exact Nat.le_max_right _ _
  · intro request hrequest
    have hcalleeBits :
        projectionRunnerGeneratedAtomBits pcp input request ≤
          projectionRunnerAtomCalleeBits pcp input := by
      unfold projectionRunnerAtomCalleeBits
      apply le_foldr_max_of_mem
      exact List.mem_map.mpr ⟨request, hrequest, rfl⟩
    have hcalleeAtMaximum :
        projectionRunnerGeneratedAtomBits pcp input request ≤
          max (projectionRunnerAtomCalleeBits pcp input)
            (balancedCallRequiredBits output requests) :=
      hcalleeBits.trans (Nat.le_max_left _ _)
    have hrequestRange := hrequest
    dsimp only [requests] at hrequestRange
    rw [projectionRunnerRangeRequests,
      balancedRangeRequestAtoms_eq_map_range, List.mem_map] at hrequestRange
    obtain ⟨index, hindex, hrequestEq⟩ := hrequestRange
    simp only [Nat.zero_add] at hrequestEq
    subst request
    exact run_projectionRunnerGeneratedAtom pcp input index
      (max (projectionRunnerAtomCalleeBits pcp input)
        (balancedCallRequiredBits output requests))
      hcalleeAtMaximum

def projectionRunnerAtomPreservingProgram : NPOracleProgram :=
  preserveRightProgram (balancedCallProgram projectionRunnerAtomProgram)

def projectionRunnerAtomPreservingFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  preserveRightFuel (projectionRunnerAtomBalancedFuel pcp input)

def projectionRunnerAtomPreservingBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  preserveRightBits (projectionRunnerAtomBalancedBits pcp input)
    (encodeBalancedList (projectionRunnerRangeRequests pcp input))
    (projectionRunnerRangeContext pcp input)
    (encodeBalancedList (projectionRunnerCallAtoms pcp input))

theorem run_projectionRunnerAtomPreservingProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    runNPOracleProgram projectionRunnerAtomPreservingProgram
        (projectionRunnerAtomPreservingBits pcp input)
        (projectionRunnerAtomPreservingFuel pcp input)
        (initialNPOracleState n
          (Nat.pair
            (encodeBalancedList (projectionRunnerRangeRequests pcp input))
            (projectionRunnerRangeContext pcp input))) =
      some
        (Nat.pair
          (encodeBalancedList (projectionRunnerCallAtoms pcp input))
          (projectionRunnerRangeContext pcp input)) := by
  exact run_preserveRightProgram
    (balancedCallProgram projectionRunnerAtomProgram) n
    (projectionRunnerAtomBalancedBits pcp input)
    (projectionRunnerAtomBalancedFuel pcp input)
    (encodeBalancedList (projectionRunnerRangeRequests pcp input))
    (projectionRunnerRangeContext pcp input)
    (encodeBalancedList (projectionRunnerCallAtoms pcp input))
    (run_projectionRunnerAtomBalancedProgram pcp input)

theorem projectionRunnerAtomPreservingProgram_oracleFree :
    OracleFree projectionRunnerAtomPreservingProgram := by
  apply preserveRightProgram_oracleFree
  exact balancedCallProgram_oracleFree
    projectionRunnerAtomProgram_oracleFree

/-! ## Canonical imported-runner balanced call -/

/-- One shared callee width for the public typed schedule. -/
def projectionRunnerCallCalleeBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (calls : List ProjectionRunnerCall) : ℕ :=
  (calls.map fun call => call.requiredBits pcp).foldr max 0

/-- One shared fuel bound.  Padding is observationally inert after a callee
halts, so the balanced controller needs no host-side per-atom fuel callback. -/
def projectionRunnerCallCalleeFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (calls : List ProjectionRunnerCall) : ℕ :=
  (calls.map fun call => call.fuel pcp).foldr max 0

/-- Total proof-level output function obtained by running the actual fixed
callee at the public batch budget.  It is never supplied to the runtime. -/
def projectionRunnerCallAtomOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (calls : List ProjectionRunnerCall) (atom : ℕ) : ℕ :=
  (runNPOracleProgram (projectionRunnerCallProgram pcp)
    (projectionRunnerCallCalleeBits pcp calls)
    (projectionRunnerCallCalleeFuel pcp calls)
    (initialNPOracleState (Nat.unpair atom).1 (Nat.unpair atom).2)).getD 0

theorem run_projectionRunnerCallProgram_at_batchBudget
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (calls : List ProjectionRunnerCall) (call : ProjectionRunnerCall)
    (hcall : call ∈ calls) :
    runNPOracleProgram (projectionRunnerCallProgram pcp)
        (projectionRunnerCallCalleeBits pcp calls)
        (projectionRunnerCallCalleeFuel pcp calls)
        (initialNPOracleState call.inputLength (Nat.unpair call.atom).2) =
      some (call.output pcp) := by
  have hbits :
      call.requiredBits pcp ≤ projectionRunnerCallCalleeBits pcp calls := by
    unfold projectionRunnerCallCalleeBits
    apply le_foldr_max_of_mem
    exact List.mem_map.mpr ⟨call, hcall, rfl⟩
  have hfuel :
      call.fuel pcp ≤ projectionRunnerCallCalleeFuel pcp calls := by
    unfold projectionRunnerCallCalleeFuel
    apply le_foldr_max_of_mem
    exact List.mem_map.mpr ⟨call, hcall, rfl⟩
  obtain ⟨extra, hfuelEq⟩ := Nat.exists_eq_add_of_le hfuel
  have hrun :=
    run_fuel_add
      (run_bits_mono (run_projectionRunnerCallProgram pcp call) hbits) extra
  rw [← hfuelEq] at hrun
  exact hrun

@[simp] theorem projectionRunnerCallAtomOutput_eq
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (calls : List ProjectionRunnerCall) (call : ProjectionRunnerCall)
    (hcall : call ∈ calls) :
    projectionRunnerCallAtomOutput pcp calls call.atom =
      call.output pcp := by
  unfold projectionRunnerCallAtomOutput
  rw [show (Nat.unpair call.atom).1 = call.inputLength by
    simp [ProjectionRunnerCall.atom]]
  rw [run_projectionRunnerCallProgram_at_batchBudget pcp calls call hcall]
  rfl

def projectionRunnerCallBalancedBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  let calls := projectionRunnerCalls pcp input
  max (projectionRunnerCallCalleeBits pcp calls) <|
    balancedCallRequiredBits
      (projectionRunnerCallAtomOutput pcp calls)
      (calls.map ProjectionRunnerCall.atom)

def projectionRunnerCallBalancedFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  let calls := projectionRunnerCalls pcp input
  balancedCallFuel (projectionRunnerCallProgram pcp)
    (fun _ => projectionRunnerCallCalleeFuel pcp calls)
    (calls.map ProjectionRunnerCall.atom)

theorem run_projectionRunnerCallBalancedProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    runNPOracleProgram
        (balancedCallProgram (projectionRunnerCallProgram pcp))
        (projectionRunnerCallBalancedBits pcp input)
        (projectionRunnerCallBalancedFuel pcp input)
        (initialNPOracleState n
          (encodeBalancedList (projectionRunnerCallAtoms pcp input))) =
      some
        (encodeBalancedList (projectionRunnerCallOutputs pcp input)) := by
  let calls := projectionRunnerCalls pcp input
  let atoms := calls.map ProjectionRunnerCall.atom
  let output := projectionRunnerCallAtomOutput pcp calls
  change
    runNPOracleProgram
        (balancedCallProgram (projectionRunnerCallProgram pcp))
        (max (projectionRunnerCallCalleeBits pcp calls)
          (balancedCallRequiredBits output atoms))
        (balancedCallFuel (projectionRunnerCallProgram pcp)
          (fun _ => projectionRunnerCallCalleeFuel pcp calls) atoms)
        (initialNPOracleState n (encodeBalancedList atoms)) =
      some
        (encodeBalancedList
          (calls.map (projectionRunnerOutput pcp)))
  have houtputs :
      atoms.map output = calls.map (projectionRunnerOutput pcp) := by
    dsimp only [atoms]
    rw [List.map_map]
    apply List.map_congr_left
    intro call hcall
    simp only [Function.comp_apply, output,
      projectionRunnerCallAtomOutput_eq pcp calls call hcall,
      projectionRunnerOutput]
  rw [← houtputs]
  apply run_balancedCallProgram_from n atoms
    (fun _ => projectionRunnerCallCalleeFuel pcp calls) output
  · exact Nat.le_max_right _ _
  · intro atom hatom
    rw [List.mem_map] at hatom
    obtain ⟨call, hcall, rfl⟩ := hatom
    rw [show (Nat.unpair call.atom).1 = call.inputLength by
      simp [ProjectionRunnerCall.atom]]
    have hrun :=
      run_projectionRunnerCallProgram_at_batchBudget pcp calls call hcall
    have hrunAtMaximum :
        runNPOracleProgram (projectionRunnerCallProgram pcp)
            (max (projectionRunnerCallCalleeBits pcp calls)
              (balancedCallRequiredBits output atoms))
            (projectionRunnerCallCalleeFuel pcp calls)
            (initialNPOracleState call.inputLength
              (Nat.unpair call.atom).2) =
          some (call.output pcp) :=
      run_bits_mono hrun (Nat.le_max_left _ _)
    simpa only [output, projectionRunnerCallAtomOutput_eq pcp calls call hcall]
      using hrunAtMaximum

def projectionRunnerCallPreservingProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) : NPOracleProgram :=
  preserveRightProgram (balancedCallProgram (projectionRunnerCallProgram pcp))

def projectionRunnerCallPreservingFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  preserveRightFuel (projectionRunnerCallBalancedFuel pcp input)

def projectionRunnerCallPreservingBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (context : ℕ) : ℕ :=
  preserveRightBits (projectionRunnerCallBalancedBits pcp input)
    (encodeBalancedList (projectionRunnerCallAtoms pcp input)) context
    (encodeBalancedList (projectionRunnerCallOutputs pcp input))

theorem run_projectionRunnerCallPreservingProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (context : ℕ) :
    runNPOracleProgram (projectionRunnerCallPreservingProgram pcp)
        (projectionRunnerCallPreservingBits pcp input context)
        (projectionRunnerCallPreservingFuel pcp input)
        (initialNPOracleState n
          (Nat.pair
            (encodeBalancedList (projectionRunnerCallAtoms pcp input))
            context)) =
      some
        (Nat.pair
          (encodeBalancedList (projectionRunnerCallOutputs pcp input))
          context) := by
  exact run_preserveRightProgram
    (balancedCallProgram (projectionRunnerCallProgram pcp)) n
    (projectionRunnerCallBalancedBits pcp input)
    (projectionRunnerCallBalancedFuel pcp input)
    (encodeBalancedList (projectionRunnerCallAtoms pcp input)) context
    (encodeBalancedList (projectionRunnerCallOutputs pcp input))
    (run_projectionRunnerCallBalancedProgram pcp input)

theorem projectionRunnerCallPreservingProgram_oracleFree
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    OracleFree (projectionRunnerCallPreservingProgram pcp) := by
  apply preserveRightProgram_oracleFree
  exact balancedCallProgram_oracleFree
    (projectionRunnerCallProgram_oracleFree pcp)

/-! ## End-to-end public projection table -/

def projectionRunnerBalancedProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram <|
    linkPrograms projectionRunnerAtomPreservingProgram
      (projectionRunnerCallPreservingProgram pcp)

def projectionRunnerBalancedInput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  generatedBalancedRangeInput (projectionRunnerRangeCount pcp n)
    (projectionRunnerRangeContext pcp input)

def projectionRunnerBalancedOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  Nat.pair
    (encodeBalancedList (projectionRunnerCallOutputs pcp input))
    (projectionRunnerRangeContext pcp input)

def projectionRunnerBalancedFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  linkFuel
    (linkPrograms projectionRunnerAtomPreservingProgram
      (projectionRunnerCallPreservingProgram pcp))
    (generatedBalancedRangeFuel n (projectionRunnerRangeCount pcp n)
      (projectionRunnerRangeContext pcp input))
    (linkFuel (projectionRunnerCallPreservingProgram pcp)
      (projectionRunnerAtomPreservingFuel pcp input)
      (projectionRunnerCallPreservingFuel pcp input))

def projectionRunnerBalancedBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) : ℕ :=
  max (natBitLength n) <|
    max
      (generatedBalancedRangeRequiredBits n
        (projectionRunnerRangeCount pcp n)
        (projectionRunnerRangeContext pcp input)) <|
      max (projectionRunnerAtomPreservingBits pcp input)
        (projectionRunnerCallPreservingBits pcp input
          (projectionRunnerRangeContext pcp input))

theorem projectionRunnerBalancedProgram_oracleFree
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    OracleFree (projectionRunnerBalancedProgram pcp) := by
  apply oracleFree_linkPrograms
  · exact generatedBalancedRangeProgram_oracleFree
  · apply oracleFree_linkPrograms
    · exact projectionRunnerAtomPreservingProgram_oracleFree
    · exact projectionRunnerCallPreservingProgram_oracleFree pcp

theorem run_projectionRunnerBalancedProgram
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) :
    runNPOracleProgram (projectionRunnerBalancedProgram pcp)
        (projectionRunnerBalancedBits pcp input)
        (projectionRunnerBalancedFuel pcp input)
        (initialNPOracleState n
          (projectionRunnerBalancedInput pcp input)) =
      some (projectionRunnerBalancedOutput pcp input) := by
  let context := projectionRunnerRangeContext pcp input
  let count := projectionRunnerRangeCount pcp n
  let maximumBits := projectionRunnerBalancedBits pcp input
  have hinputBits : natBitLength n ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hgeneratorBits :
      generatedBalancedRangeRequiredBits n count context ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hatomBits :
      projectionRunnerAtomPreservingBits pcp input ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcallBits :
      projectionRunnerCallPreservingBits pcp input context ≤
        maximumBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength n).trans hinputBits
  apply run_linkPrograms hpositive hinputBits
  · simpa only [projectionRunnerBalancedInput, count, context] using
      run_bits_mono
        (run_generatedBalancedRangeProgram n count context) hgeneratorBits
  · apply run_linkPrograms hpositive hinputBits
    · have hrun :=
        run_bits_mono
          (run_projectionRunnerAtomPreservingProgram pcp input) hatomBits
      simpa only [generatedBalancedRangeOutput,
        projectionRunnerRangeRequests, count, context] using hrun
    · have hrun :=
        run_bits_mono
          (run_projectionRunnerCallPreservingProgram pcp input context)
          hcallBits
      simpa only [projectionRunnerBalancedOutput, context] using hrun

end NearCubicWires.ProjectionRunnerBalancedProgram
