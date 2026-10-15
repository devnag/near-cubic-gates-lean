import Proof.Circuits.BoundedOracleStructuralFormulaIndex
import Proof.Circuits.BoundedOracleStructuralTableCompiler
import Proof.MachineModel.GeneratedBalancedRangeProgram

/-!
# Pointwise structural formula from public projection outputs

This is the sole semantic target of the fixed atom callee.  It interprets one
global formula index from the actual projection-runner table and the public
shape; it never accepts a circuit, node schedule, or formula list as context.
-/

namespace NearCubicWires.BoundedOracleStructuralFormulaTable

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.SourceInterfaces

def tableBoundedOracleStructuralFormulaAtomAt
    (outputs : List ℕ) (width count bound index : ℕ) : ℕ :=
  let inputArity := descriptionWidth width bound
  let nodes :=
    tableBoundedOracleStructuralNodeSchedule outputs width count bound
  structuralFormulaAtomAtSchedule inputArity nodes
    (tableBoundedOracleStructuralOutputIndex
      outputs width count bound)
    index

def tableBoundedOracleStructuralFormulaLength
    (outputs : List ℕ) (width count bound : ℕ) : ℕ :=
  descriptionWidth width bound +
    (tableBoundedOracleStructuralNodeSchedule
      outputs width count bound).length + 1

/-- Public context shared by every generated formula-atom request.  The table
is retained only in its canonical balanced representation; width, query
count, and circuit bound are the complete structural shape. -/
def tableBoundedOracleStructuralFormulaContext
    (outputs : List ℕ) (width count bound : ℕ) : ℕ :=
  Nat.pair (encodeBalancedList outputs)
    (Nat.pair width (Nat.pair count bound))

def tableBoundedOracleStructuralFormulaRequests
    (inputLength : ℕ) (outputs : List ℕ)
    (width count bound : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength
    (tableBoundedOracleStructuralFormulaContext
      outputs width count bound)
    0
    (tableBoundedOracleStructuralFormulaLength
      outputs width count bound)

def tableBoundedOracleStructuralFormulaRequestIndex
    (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

def tableBoundedOracleStructuralFormulaRequestOutput
    (outputs : List ℕ) (width count bound request : ℕ) : ℕ :=
  tableBoundedOracleStructuralFormulaAtomAt outputs width count bound
    (tableBoundedOracleStructuralFormulaRequestIndex request)

theorem tableBoundedOracleStructuralFormulaRequests_outputs
    (inputLength : ℕ) (outputs : List ℕ)
    (width count bound : ℕ) :
    (tableBoundedOracleStructuralFormulaRequests
      inputLength outputs width count bound).map
        (tableBoundedOracleStructuralFormulaRequestOutput
          outputs width count bound) =
      (List.range
        (tableBoundedOracleStructuralFormulaLength
          outputs width count bound)).map
        (tableBoundedOracleStructuralFormulaAtomAt
          outputs width count bound) := by
  unfold tableBoundedOracleStructuralFormulaRequests
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro index _
  simp [tableBoundedOracleStructuralFormulaRequestOutput,
    tableBoundedOracleStructuralFormulaRequestIndex,
    balancedRangeRequestAtom]

@[simp] theorem tableBoundedOracleStructuralFormulaAtomAt_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound index : ℕ) :
    tableBoundedOracleStructuralFormulaAtomAt
        (projectionRunnerCallOutputs pcp input)
        (pcp.toSemantic.nativeWidth n) (pcp.queryCount n) bound index =
      boundedOracleStructuralFormulaAtomAt
        pcp.toSemantic input bound index := by
  unfold tableBoundedOracleStructuralFormulaAtomAt
  have hnodes :
      tableBoundedOracleStructuralNodeSchedule
          (projectionRunnerCallOutputs pcp input)
          (pcp.toSemantic.nativeWidth n) (pcp.queryCount n) bound =
        boundedOracleStructuralNodeSchedule
          pcp.toSemantic input bound :=
    tableBoundedOracleStructuralNodeSchedule_runnerOutputs
      pcp input bound
  have houtput :
      tableBoundedOracleStructuralOutputIndex
          (projectionRunnerCallOutputs pcp input)
          (pcp.toSemantic.nativeWidth n) (pcp.queryCount n) bound =
        boundedOracleStructuralOutputIndex
          pcp.toSemantic input bound :=
    tableBoundedOracleStructuralOutputIndex_runnerOutputs
      pcp input bound
  unfold boundedOracleStructuralFormulaAtomAt
  exact congrArg₂
    (fun nodes outputIndex =>
      structuralFormulaAtomAtSchedule
        (descriptionWidth (pcp.toSemantic.nativeWidth n) bound)
        nodes outputIndex index)
    hnodes houtput

@[simp] theorem map_range_tableBoundedOracleStructuralFormulaAtomAt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (List.range
      (boundedOracleStructuralFormulaAtoms
        pcp.toSemantic input bound).length).map
        (tableBoundedOracleStructuralFormulaAtomAt
          (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound) =
      boundedOracleStructuralFormulaAtoms
        pcp.toSemantic input bound := by
  calc
    _ = (List.range
          (boundedOracleStructuralFormulaAtoms
            pcp.toSemantic input bound).length).map
          (boundedOracleStructuralFormulaAtomAt
            pcp.toSemantic input bound) := by
      apply List.map_congr_left
      intro index _
      exact tableBoundedOracleStructuralFormulaAtomAt_runnerOutputs
        pcp input bound index
    _ = _ :=
      map_range_boundedOracleStructuralFormulaAtomAt
        pcp.toSemantic input bound

@[simp] theorem tableBoundedOracleStructuralFormulaLength_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    tableBoundedOracleStructuralFormulaLength
        (projectionRunnerCallOutputs pcp input)
        (pcp.nativeWidth n) (pcp.queryCount n) bound =
      (boundedOracleStructuralFormulaAtoms
        pcp.toSemantic input bound).length := by
  have hscheduleLength :=
    congrArg List.length <|
      tableBoundedOracleStructuralNodeSchedule_runnerOutputs
        pcp input bound
  calc
    _ = descriptionWidth (pcp.nativeWidth n) bound +
          (boundedOracleStructuralNodeSchedule
            pcp.toSemantic input bound).length + 1 := by
      unfold tableBoundedOracleStructuralFormulaLength
      exact congrArg
        (fun length =>
          descriptionWidth (pcp.nativeWidth n) bound + length + 1)
        hscheduleLength
    _ = descriptionWidth (pcp.toSemantic.nativeWidth n) bound +
          boundedOracleStructuralGateBudget
            pcp.toSemantic input bound + 1 := by
      rw [boundedOracleStructuralNodeSchedule_length]
      simp only [ExecutableProjectionPCP.toSemantic_nativeWidth]
    _ = _ := by
      rw [boundedOracleStructuralFormulaAtoms_length]

/-- The shared generated-range ABI enumerates exactly the canonical formula
atoms when instantiated with the actual imported-runner table. -/
@[simp] theorem
    tableBoundedOracleStructuralFormulaRequests_runnerOutputs
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (tableBoundedOracleStructuralFormulaRequests n
      (projectionRunnerCallOutputs pcp input)
      (pcp.nativeWidth n) (pcp.queryCount n) bound).map
        (tableBoundedOracleStructuralFormulaRequestOutput
          (projectionRunnerCallOutputs pcp input)
          (pcp.nativeWidth n) (pcp.queryCount n) bound) =
      boundedOracleStructuralFormulaAtoms
        pcp.toSemantic input bound := by
  rw [tableBoundedOracleStructuralFormulaRequests_outputs,
    tableBoundedOracleStructuralFormulaLength_runnerOutputs,
    map_range_tableBoundedOracleStructuralFormulaAtomAt]

end NearCubicWires.BoundedOracleStructuralFormulaTable
