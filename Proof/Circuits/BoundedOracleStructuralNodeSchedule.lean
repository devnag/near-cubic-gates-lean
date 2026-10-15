import Proof.Circuits.BoundedOracleStructuralCircuit

/-!
# Canonical bounded-oracle verifier node schedule

The executable emitter needs an ordinary list of gates, while the semantic
compiler returns a verified DAG builder.  The builder's extension suffix is
already the canonical compositional schedule: each compiler layer concatenates
exactly the nodes it appends.  Exposing that suffix avoids a second recursive
gate generator whose indices could drift from the verified circuit.
-/

namespace NearCubicWires.BoundedOracleStructuralCircuit

open NearCubicWires
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces

/-- The exact topological gate schedule appended by the canonical verifier
compiler from an empty builder. -/
def boundedOracleStructuralNodeSchedule
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    List (BooleanNode
      (descriptionWidth (pcp.nativeWidth n) bound)) :=
  (compileBoundedOracleVerifier pcp input bound <|
    BooleanDAGBuilder.empty
      (descriptionWidth (pcp.nativeWidth n) bound)).extension.suffix

/-- The output address selected by the same canonical compilation. -/
def boundedOracleStructuralOutputIndex
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) : ℕ :=
  (compileBoundedOracleVerifier pcp input bound <|
    BooleanDAGBuilder.empty
      (descriptionWidth (pcp.nativeWidth n) bound)).output.val

/-- Starting from the empty builder makes the compositional extension suffix
the whole verifier circuit, rather than merely a length-equivalent list. -/
@[simp] theorem boundedOracleStructuralNodeSchedule_eq_nodes
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleStructuralNodeSchedule pcp input bound =
      (boundedOracleVerifierCircuit pcp input bound).nodes := by
  let builder :=
    BooleanDAGBuilder.empty
      (descriptionWidth (pcp.nativeWidth n) bound)
  let compiled :=
    compileBoundedOracleVerifier pcp input bound builder
  have hnodes := compiled.extension.nodes_eq
  change compiled.extension.suffix = compiled.final.nodes
  simpa only [builder, BooleanDAGBuilder.empty, List.nil_append] using
    hnodes.symm

@[simp] theorem boundedOracleStructuralOutputIndex_eq_output
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleStructuralOutputIndex pcp input bound =
      (boundedOracleVerifierCircuit pcp input bound).output.val := by
  rfl

@[simp] theorem boundedOracleStructuralNodeSchedule_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    (boundedOracleStructuralNodeSchedule pcp input bound).length =
      boundedOracleStructuralGateBudget pcp input bound := by
  rw [boundedOracleStructuralNodeSchedule_eq_nodes]
  simpa only [BooleanCircuit.size] using
    boundedOracleVerifierCircuit_size pcp input bound

theorem boundedOracleStructuralOutputIndex_lt_length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound : ℕ) :
    boundedOracleStructuralOutputIndex pcp input bound <
      (boundedOracleStructuralNodeSchedule pcp input bound).length := by
  rw [boundedOracleStructuralOutputIndex_eq_output,
    boundedOracleStructuralNodeSchedule_eq_nodes]
  exact (boundedOracleVerifierCircuit pcp input bound).output.isLt

end NearCubicWires.BoundedOracleStructuralCircuit
