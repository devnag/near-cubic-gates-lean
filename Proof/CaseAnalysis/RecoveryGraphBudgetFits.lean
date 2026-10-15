import Proof.CaseAnalysis.RecoveryGraphBudgetPolynomial
import Proof.CaseAnalysis.RecoveryGrammarAllocationFits

/-! The existing original graph Fits predicates lift to the caller's paid
coarse workspace. No exact graph size is evaluated by a new machine. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open BoundedOracleStructuralCircuit FinitePredicateCircuit SourceInterfaces
open CloseoutRecoveryWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem node_fits_mono {n bound U W : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (row : Fin (bound+1))
    (address : BitInput n) (wires : List (LiveWire b)) (hUW : U ≤ W)
    (h : RecoveryBoundedTableNode.Fits b row address wires U) :
    RecoveryBoundedTableNode.Fits b row address wires W := by
  rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,o⟩
  exact ⟨a.trans hUW,b.trans hUW,c.trans hUW,d.trans hUW,e.trans hUW,f.trans hUW,
    g.trans hUW,h.trans hUW,i.trans hUW,j.trans hUW,k.trans hUW,l.trans hUW,m.trans hUW,o.trans hUW⟩

private theorem queries_fits_mono {n bound U W : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (total : ℕ) (ht : total ≤ bound)
    (addresses : List (BitInput n)) (hUW : U ≤ W)
    (h : RecoveryBoundedQueries.Fits b total U ht addresses) :
    RecoveryBoundedQueries.Fits b total W ht addresses := by
  induction addresses generalizing b with
  | nil=>trivial
  | cons address rest ih=>
    rcases h with ⟨htable,houtput,hrest⟩
    refine ⟨fun k hk=>node_fits_mono _ _ _ _ hUW (htable k hk),?_,ih _ hrest⟩
    exact ⟨houtput.1.trans hUW,houtput.2.1.trans hUW,
      houtput.2.2.1.trans hUW,houtput.2.2.2.trans hUW⟩

theorem row_fits_coarse {machine : TimedDecisionMachine} {timeBound : ℕ→ℕ}
    (pcp : ProjectionPCP machine timeBound) {n bound : ℕ} (input : BitInput n)
    (b : BooleanDAGBuilder (descriptionWidth (pcp.nativeWidth n) bound))
    (count G W : ℕ) (hc : count ≤ bound) (randomness : BitInput (pcp.nativeWidth n))
    (hW : workspace (pcp.nativeWidth n) bound G ≤ W)
    (hg : (compileVerifierRow pcp input b count hc randomness).compiled.final.nodes.length ≤ G) :
    RecoveryBoundedQueries.Fits b count W hc (projectedAddresses pcp input randomness) :=
  queries_fits_mono b count hc _ hW (row_fits pcp input b count G hc randomness hg)

theorem allocation_coarse (q bound G W : ℕ) (hW : workspace q bound G ≤ W) :
    RecoveryBoundedGrammarCold.Allocation q bound G W := by
  have h := CloseoutRecoveryGrammarResources.allocation q bound G
  exact ⟨h.graph.trans hW,h.tag.trans hW,h.field.trans hW,h.less.trans hW,
    fun row start hs=>(h.index row start hs).trans hW⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
