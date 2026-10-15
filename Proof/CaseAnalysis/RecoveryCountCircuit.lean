import Proof.CaseAnalysis.RecoveryCountNativePorts

/-! The completed count compiler emits the literal circuit used by the
original bounded recovery formula, on the one shared description block. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem original_nodes {v : TimedDecisionMachine} {T : ℕ→ℕ}
    (pcp : ProjectionPCP v T) {n : ℕ} (x : BitInput n) (bound : ℕ) :
    (boundedOracleVerifierCircuit pcp x bound).nodes=
      (compileCountCases pcp x (BooleanDAGBuilder.empty (descriptionWidth (pcp.nativeWidth n) bound))
        (List.finRange bound)).final.nodes := by
  exact congrArg (fun counts=>
    (compileCountCases pcp x (BooleanDAGBuilder.empty (descriptionWidth (pcp.nativeWidth n) bound)) counts).final.nodes)
    (List.ofFn_id bound)

private theorem original_output {v : TimedDecisionMachine} {T : ℕ→ℕ}
    (pcp : ProjectionPCP v T) {n : ℕ} (x : BitInput n) (bound : ℕ) :
    (boundedOracleVerifierCircuit pcp x bound).output.val=
      (compileCountCases pcp x (BooleanDAGBuilder.empty (descriptionWidth (pcp.nativeWidth n) bound))
        (List.finRange bound)).output.val := by
  exact congrArg (fun counts=>
    (compileCountCases pcp x (BooleanDAGBuilder.empty (descriptionWidth (pcp.nativeWidth n) bound)) counts).output.val)
    (List.ofFn_id bound)

private theorem empty_prefix {q : ℕ} (pre : List Bool) (nodes result : List (BooleanNode q))
    (hp : pre=[]) (hn : nodes=result) :
    pre++nodes.flatMap PCPPRequestNodeSchema.native=result.flatMap PCPPRequestNodeSchema.native := by
  rw [hp,hn,List.nil_append]

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

noncomputable def Resources.circuit (_z : Resources p R Q hr hq (bound:=bound) x) :
    BooleanCircuit (descriptionWidth R bound):=
  boundedOracleVerifierCircuit (compactProjectionPCP (p.normalized R Q hr hq)) x bound

theorem Resources.circuit_nodes (z : Resources p R Q hr hq (bound:=bound) x) :
    z.circuit.nodes=(compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).final.nodes :=
  original_nodes _ _ _

theorem Resources.circuit_output (z : Resources p R Q hr hq (bound:=bound) x) :
    z.circuit.output.val=(compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).output.val :=
  original_output _ _ _

theorem Resources.circuit_graph (z : Resources p R Q hr hq (bound:=bound) x) (extra : Fin 12→List Bool)
    (f : Forward z (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound))
    (hpre : z.base.pre=[]) :
    (z.foldResult f.next [] f.refs extra).tapes 20=z.circuit.nodes.flatMap PCPPRequestNodeSchema.native :=
  (z.finish_graph _ [] extra f).trans (empty_prefix z.base.pre _ _ hpre z.circuit_nodes.symm)

theorem Resources.circuit_reference (z : Resources p R Q hr hq (bound:=bound) x) (extra : Fin 12→List Bool)
    (f : Forward z (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)) :
    (z.foldResult f.next [] f.refs extra).tapes 25=List.replicate z.circuit.output.val true :=
  (z.finish_output _ [] extra f).trans (congrArg (fun value=>List.replicate value true) z.circuit_output.symm)

theorem Resources.circuit_last (z : Resources p R Q hr hq (bound:=bound) x)
    (f : Forward z (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)) :
    z.circuit.nodes.length=z.circuit.output.val+1 :=
  (congrArg List.length z.circuit_nodes).trans ((f.output_last z _).trans
    (congrArg (fun value=>value+1) z.circuit_output.symm))

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
