import Proof.Circuits.BoundedOracleStructuralFormulaAtomSchedule

/-!
# Pointwise bounded-oracle formula-atom schedule

The structural formula has one total, public index interpretation: input
tautologies first, then the canonical compiler suffix, and finally the output
unit.  The reconstruction theorem below prevents executable range generation
from introducing a second formula schedule.
-/

namespace NearCubicWires.BoundedOracleStructuralCircuit

open NearCubicWires
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

def structuralFormulaAtomAtSchedule
    (inputArity : ℕ) (nodes : List (BooleanNode inputArity))
    (outputIndex index : ℕ) : ℕ :=
  if index < inputArity then
    circuitInputFormulaClauseTautologyAtom inputArity index
  else
    match nodes[index - inputArity]? with
    | some node =>
        circuitInputFormulaClauseNodeAtom (index - inputArity) node
    | none =>
        circuitInputFormulaClauseNodeAtom outputIndex
          (.const true : BooleanNode inputArity)

/-- Interpret a global structural-formula index without materializing the
formula list.  Out-of-range indices deliberately select the final output atom;
the executable caller enumerates only the exact certified range below. -/
def boundedOracleStructuralFormulaAtomAt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound index : ℕ) : ℕ :=
  let inputArity := descriptionWidth (pcp.nativeWidth n) bound
  let nodes := boundedOracleStructuralNodeSchedule pcp input bound
  structuralFormulaAtomAtSchedule inputArity nodes
    (boundedOracleStructuralOutputIndex pcp input bound) index

private theorem map_range_nodeAtomsFrom {n : ℕ}
    (fallback start : ℕ) (nodes : List (BooleanNode n)) :
    (List.range nodes.length).map (fun offset =>
      match nodes[offset]? with
      | some node =>
          circuitInputFormulaClauseNodeAtom (start + offset) node
      | none => fallback) =
      circuitInputFormulaNodeAtomsFrom start nodes := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest inductionHypothesis =>
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.getElem?_cons_zero,
        Nat.add_zero,
        circuitInputFormulaNodeAtomsFrom]
      apply congrArg
        (fun tail =>
          circuitInputFormulaClauseNodeAtom start node :: tail)
      rw [← inductionHypothesis (start + 1)]
      apply List.map_congr_left
      intro offset _
      simp only [Function.comp_apply, List.getElem?_cons_succ]
      cases rest[offset]? <;>
        simp [Nat.add_comm, Nat.add_left_comm]

/-- Enumerating the exact global range through the pointwise interpretation
reconstructs the sole canonical structural formula-atom list. -/
@[simp] theorem map_range_boundedOracleStructuralFormulaAtomAt
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (List.range
      (boundedOracleStructuralFormulaAtoms pcp input bound).length).map
        (boundedOracleStructuralFormulaAtomAt pcp input bound) =
      boundedOracleStructuralFormulaAtoms pcp input bound := by
  let inputArity := descriptionWidth (pcp.nativeWidth n) bound
  let nodes := boundedOracleStructuralNodeSchedule pcp input bound
  let outputAtom :=
    circuitInputFormulaClauseNodeAtom
      (boundedOracleStructuralOutputIndex pcp input bound)
      (.const true : BooleanNode inputArity)
  rw [boundedOracleStructuralFormulaAtoms_length,
    ← boundedOracleStructuralNodeSchedule_length]
  unfold boundedOracleStructuralFormulaAtoms
  rw [List.append_assoc]
  change
    (List.range (inputArity + nodes.length + 1)).map
        (boundedOracleStructuralFormulaAtomAt pcp input bound) =
      (List.range inputArity).map
          (circuitInputFormulaClauseTautologyAtom inputArity) ++
        (circuitInputFormulaNodeAtomsFrom 0 nodes ++ [outputAtom])
  rw [show inputArity + nodes.length + 1 =
      inputArity + (nodes.length + 1) by omega,
    List.range_add, List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro index hindex
    have hindex_lt : index < inputArity := List.mem_range.mp hindex
    simp [boundedOracleStructuralFormulaAtomAt,
      structuralFormulaAtomAtSchedule, inputArity, hindex_lt]
  · rw [List.range_succ, List.map_append]
    apply congrArg₂ (· ++ ·)
    · rw [← map_range_nodeAtomsFrom outputAtom 0 nodes]
      apply List.map_congr_left
      intro offset _
      simp only [Function.comp_apply]
      cases hlookup : nodes[offset]? with
      | none =>
          have hlookup' :
              (boundedOracleVerifierCircuit pcp input bound).nodes[offset]? =
                none := by
            simpa only [nodes,
              boundedOracleStructuralNodeSchedule_eq_nodes] using hlookup
          simp [boundedOracleStructuralFormulaAtomAt,
            structuralFormulaAtomAtSchedule, inputArity,
            outputAtom, hlookup']
      | some node =>
          have hlookup' :
              (boundedOracleVerifierCircuit pcp input bound).nodes[offset]? =
                some node := by
            simpa only [nodes,
              boundedOracleStructuralNodeSchedule_eq_nodes] using hlookup
          simp [boundedOracleStructuralFormulaAtomAt,
            structuralFormulaAtomAtSchedule, inputArity, hlookup']
    · simp [boundedOracleStructuralFormulaAtomAt,
        structuralFormulaAtomAtSchedule, inputArity, nodes, outputAtom]

end NearCubicWires.BoundedOracleStructuralCircuit
