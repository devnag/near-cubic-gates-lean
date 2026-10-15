import Proof.CaseAnalysis.RecoveryQueryState
import Proof.Circuits.StructuralGateBudgetEnvelope

/-! One coarse allocation bound for the original C.12 compiler. The graph
bound is supplied by the original structural ledger; the quadratic slack
also pays the stronger temporary-position premises of the physical workers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open BoundedOracleStructuralCircuit FinitePredicateCircuit OuterPCPRecovery
open R1Leaf56StructuralGateBudgetEnvelope SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workspace (n bound G : ℕ) : ℕ := G+256*(n+bound+1)^2

theorem workspace_bounds (n bound G : ℕ) :
    G+118 ≤ workspace n bound G ∧
    (bound+2)*rowWidth n bound ≤ workspace n bound G ∧
    G+(n+bound+1)*(3*(n+bound+1)+2)+3*(n+bound+1) ≤ workspace n bound G ∧
    n+bound+1 ≤ workspace n bound G := by
  unfold workspace rowWidth boundedCircuitFieldLimit
  have hp : 1 ≤ n+bound+1 := by omega
  have hs : 1 ≤ (n+bound+1)^2 := by nlinarith
  refine ⟨by nlinarith,?_,by nlinarith,by nlinarith⟩
  have hb : bound+2 ≤ 2*(n+bound+1) := by omega
  have hr : 6+2*(n+bound+1) ≤ 8*(n+bound+1) := by omega
  have hm := Nat.mul_le_mul hb hr
  nlinarith

theorem graph_le_workspace {n bound G g : ℕ} (h : g ≤ G) :
    g ≤ workspace n bound G := by
  have hw := (workspace_bounds n bound G).1
  omega

theorem temporary_le_workspace {n bound G g count : ℕ}
    (hg : g ≤ G) (hc : count ≤ n+bound+1) :
    g+count*(3*boundedCircuitFieldLimit n bound+2)+
      3*boundedCircuitFieldLimit n bound ≤ workspace n bound G := by
  have hw := (workspace_bounds n bound G).2.2.1
  have hm := Nat.mul_le_mul_right (3*(n+bound+1)+2) hc
  unfold boundedCircuitFieldLimit
  omega

theorem index_le_workspace {n bound G : ℕ} (row : Fin (bound+1))
    (start : ℕ) (hs : start ≤ rowWidth n bound) :
    RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+
      rowWidth n bound ≤ workspace n bound G := by
  have hr : row.val ≤ bound := by omega
  have hm := Nat.mul_le_mul_right (rowWidth n bound) hr
  have hw := (workspace_bounds n bound G).2.1
  unfold RecoveryBoundedNativeUnaryLoop.firstIndex
  have he : (bound+2)*rowWidth n bound=
      bound*rowWidth n bound+rowWidth n bound+rowWidth n bound := by ring
  omega

/-- The complete original-node allocation contract follows from its final
graph size. Intermediate builders are genuine prefixes of that same graph. -/
theorem node_fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (address : BitInput n) (wires : List (LiveWire b))
    (G : ℕ) (hc : wires.length ≤ bound)
    (hg : (compileUniversalNode b row address wires).compiled.final.nodes.length ≤ G) :
    RecoveryBoundedTableNode.Fits b row address wires (workspace n bound G) := by
  let left:=compileFirstFieldSelect b row wires
  let right:=compileSecondFieldSelect left.final row (liftLiveWires left.extension wires)
  let constant:=compileExpr right.final (firstFieldEqualsExpr row 1)
  let input:=compileExpr constant.final (constantAddressSelectionExpr row address)
  let seven:=RecoveryBoundedUniversalNode.cases b row address wires
  let selected:=compileFieldSelect seven.final tagEqualsExpr row seven.values
  have ho:=RecoveryBoundedUniversalNode.original_node b row address wires
  have hselected : selected.final.nodes.length ≤ G := by
    rw [←ho.1]
    exact hg
  have hseven : seven.final.nodes.length ≤ G := selected.extension.length_le.trans hselected
  have hlayout:=RecoveryBoundedUniversalNode.cases_layout b row address wires
  have hnext:=RecoveryBoundedNodeAddress.expression_next constant.final
    (constantAddressSelectionExpr row address)
  have hinput : input.final.nodes.length ≤ G := by
    change input.output.val+1=input.final.nodes.length at hnext
    have he : seven.final.nodes.length=input.output.val+4 := hlayout.2.1
    omega
  have hconstant : constant.final.nodes.length ≤ G := input.extension.length_le.trans hinput
  have hright : right.final.nodes.length ≤ G := constant.extension.length_le.trans hconstant
  have hleft : left.final.nodes.length ≤ G := right.extension.length_le.trans hright
  have hb : b.nodes.length ≤ G := left.extension.length_le.trans hleft
  have hF : boundedCircuitFieldLimit n bound=n+bound+1 := rfl
  have hwidth : rowWidth n bound=2*boundedCircuitFieldLimit n bound+6 := by
    unfold rowWidth
    omega
  have hfirst:=index_le_workspace (G:=G) (n:=n) row 6 (by unfold rowWidth; omega)
  have hsecond:=index_le_workspace (G:=G) (n:=n) row
    (6+boundedCircuitFieldLimit n bound) (by unfold rowWidth; omega)
  have htag:=index_le_workspace (G:=G) (n:=n) row 0 (Nat.zero_le _)
  rw [hwidth] at hfirst hsecond htag
  have hsmall := (workspace_bounds n bound G).2.2.2
  have hw := (workspace_bounds n bound G).1
  refine ⟨hfirst,hsecond,htag,temporary_le_workspace hb (by omega),by omega,by omega,
    graph_le_workspace hleft,temporary_le_workspace hleft (by omega),
    graph_le_workspace hright,?_,?_,graph_le_workspace hinput,?_,
    graph_le_workspace hg⟩
  · have ht:=temporary_le_workspace (n:=n) (bound:=bound) (count:=0) hright (by omega)
    simpa only [Nat.zero_mul,Nat.add_zero] using ht
  · have ht:=temporary_le_workspace (n:=n) (bound:=bound) (count:=n) hconstant (by omega)
    change constant.final.nodes.length+n*(3*boundedCircuitFieldLimit n bound+1)+
      3*boundedCircuitFieldLimit n bound ≤ workspace n bound G
    have hm : n*(3*boundedCircuitFieldLimit n bound+1) ≤
        n*(3*boundedCircuitFieldLimit n bound+2) := Nat.mul_le_mul_left _ (by omega)
    omega
  · change seven.final.nodes.length+118 ≤ workspace n bound G
    omega

/-- A cold arithmetic expression bounds the actual original final graph;
the original clause bound is its only semantic resource premise. -/
def originalWorkspace (q bound queries clauses : ℕ) : ℕ :=
  workspace q bound (structuralGateEnvelope q bound queries clauses+queries+clauses)

theorem original_graph_bound
    {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : SourceInterfaces.ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound clauses : ℕ)
    (hclauses : ∀ randomness, (pcp.decision input randomness).clauses.length ≤ clauses) :
    (boundedOracleVerifierCircuit pcp input bound).size ≤
      originalWorkspace (pcp.nativeWidth n) bound (pcp.queryCount n) clauses := by
  have hg:=boundedOracleStructuralGateBudget_envelope pcp input bound clauses hclauses
  rw [boundedOracleVerifierCircuit_size]
  exact graph_le_workspace (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
