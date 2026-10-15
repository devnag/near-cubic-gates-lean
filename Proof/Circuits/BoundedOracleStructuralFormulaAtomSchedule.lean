import Proof.Circuits.BoundedOracleStructuralNodeSchedule
import Proof.Circuits.CircuitInputClauseBalancedCall

/-!
# Canonical bounded-oracle formula-atom schedule

The executable emitter targets heterogeneous clause-call atoms rather than a
second circuit representation.  This module states that target directly from
the canonical compiler suffix: all input tautologies, every compiled node in
topological order, then the positive output unit.  The equality below prevents
the runtime path from maintaining a shadow node/CNF schedule.
-/

namespace NearCubicWires.BoundedOracleStructuralCircuit

open NearCubicWires
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-- Exact heterogeneous call atoms expected from the structural emitter. -/
def boundedOracleStructuralFormulaAtoms
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : List ℕ :=
  let inputArity := descriptionWidth (pcp.nativeWidth n) bound
  (List.range inputArity).map
      (circuitInputFormulaClauseTautologyAtom inputArity) ++
    circuitInputFormulaNodeAtomsFrom 0
      (boundedOracleStructuralNodeSchedule pcp input bound) ++
    [circuitInputFormulaClauseNodeAtom
      (boundedOracleStructuralOutputIndex pcp input bound)
      (.const true : BooleanNode inputArity)]

/-- The emitter target is definitionally the sole complete circuit-input
formula schedule once the canonical compiler suffix is exposed. -/
@[simp] theorem boundedOracleStructuralFormulaAtoms_eq
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleStructuralFormulaAtoms pcp input bound =
      circuitInputFormulaAtoms
        (boundedOracleVerifierCircuit pcp input bound) := by
  unfold boundedOracleStructuralFormulaAtoms circuitInputFormulaAtoms
  rw [boundedOracleStructuralNodeSchedule_eq_nodes,
    boundedOracleStructuralOutputIndex_eq_output]

private theorem circuitInputFormulaNodeAtomsFrom_length {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputFormulaNodeAtomsFrom start nodes).length = nodes.length := by
  induction nodes generalizing start with
  | nil =>
      rfl
  | cons node rest ih =>
      simp only [circuitInputFormulaNodeAtomsFrom, List.length_cons, ih]

@[simp] theorem boundedOracleStructuralFormulaAtoms_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (boundedOracleStructuralFormulaAtoms pcp input bound).length =
      descriptionWidth (pcp.nativeWidth n) bound +
        boundedOracleStructuralGateBudget pcp input bound + 1 := by
  unfold boundedOracleStructuralFormulaAtoms
  simp only [List.length_append, List.length_map, List.length_range,
    circuitInputFormulaNodeAtomsFrom_length, List.length_singleton,
    boundedOracleStructuralNodeSchedule_length]

end NearCubicWires.BoundedOracleStructuralCircuit
