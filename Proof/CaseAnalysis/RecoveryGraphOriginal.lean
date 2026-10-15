import Proof.CaseAnalysis.RecoveryGraphRun
import Proof.CaseAnalysis.RecoveryGraphBudgetOriginal
import Proof.CaseAnalysis.RecoveryGraphBudgetSupport
import Proof.CaseAnalysis.RecoveryGraphBudgetScalarWhole

/-! All physical graph and serializer resources follow from the original
source and the one paid W. No graph, node count or scratch bank is supplied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage
open ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit BalancedCNFSATEncoding
open RecoveryBoundedGraphBudget CloseoutRecoveryWorkspace
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width ≤ R) (hq : p.queries ≤ Q)
variable {n bound : ℕ} (x : BitInput n) (W : ℕ)

theorem original_run (hb : 0<bound)
    (hW : originalWorkspace R bound Q (Codec.clauses p).length ≤ W)
    (hsource : (DedupBytes.fields p).length ≤ W) (htwo : 2^R ≤ W) :
    let c:=boundedOracleVerifierCircuit (compactProjectionPCP (p.normalized R Q hr hq)) x bound
    ∃ r,LocalBitMultitape.run machine (budget (scalarBacking W) W R bound c)
      (insert [] (RecoveryBoundedColdPrepared.input R bound (capacity W) Q (Codec.clauses p).length (scalarBacking W)
        (RecoveryBoundedRowProjection.bank p R Q (bitInputOfCode R 0) (scalarBacking W)) (DedupBytes.fields p)))=some r ∧
      r.steps ≤ budget (scalarBacking W) W R bound c ∧
      r.final.tapes 1657=frame (balancedCNFPayload (CircuitInputCNF.circuitInputFormula c)).bits ∧
      r.final.heads 1657=0 ∧
      r.final.tapes 144=ZeroPadding.pad (scalarBacking W) (List.replicate (descriptionWidth R bound) true) ∧
      r.final.heads 144=0 ∧
      (∀ j : Fin 5,r.final.tapes (j.natAdd 1659)=
        RecoveryBoundedColdCompile.raw R bound (capacity W) Q (Codec.clauses p).length j ∧
        r.final.heads (j.natAdd 1659)=0) := by
  have fields:=original_workspace_fields R bound Q (Codec.clauses p).length
  have hs0:=support_bound W R Q bound (DedupBytes.fields p)
    (fields.1.trans hW) (fields.2.2.1.trans hW) (fields.2.1.trans hW) hsource htwo
  have hs : support W R Q bound (DedupBytes.fields p++[]) ≤ scalarSupport W := by
    simpa only [List.append_nil,scalarSupport] using hs0
  let z:=originalResources p R Q hr hq x W (scalarSupport W) [] hW hs
  have hf : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x
      (BooleanDAGBuilder.empty (descriptionWidth R bound)) (List.finRange bound)).final.nodes.length ≤ z.base.G :=
    original_final p R Q hr hq x
  have hn : z.circuit.nodes.length ≤ W :=
    (congrArg List.length z.circuit_nodes).le.trans (hf.trans z.base.graph_bound)
  have ha:= (workspace_description R bound (originalG p R Q bound) W hW).2.2.2
  have fits:=serializer_fits z.circuit W (scalarSupport W) ha hn
  have stack:=empty_stack_bounds (p:=p) (R:=R) (Q:=Q) (bound:=bound)
    (W:=W) (S:=scalarSupport W) (sourceTail:=[]) (hS:=hs)
  exact run z rfl rfl rfl hb stack.1 stack.2 hf fits.1 fits.2.1 fits.2.2

def coefficient : ℕ:=8192*330000000066+1+wholeCoefficient

theorem budget_bound {arity : ℕ} (c : BooleanCircuit arity)
    (ha : arity ≤ W) (hc : c.nodes.length ≤ W) (hR : R ≤ W) (hb : bound ≤ W) (htwo : 2^R ≤ W) :
    budget (scalarBacking W) W R bound c ≤ coefficient*(W+1)^48 := by
  have whole:=whole_scalar c W R bound ha hc hR hb htwo
  have back:=scalar_backing W
  have pow : (W+1)^6 ≤ (W+1)^48:=Nat.pow_le_pow_right (by omega) (by decide)
  have prep : RecoveryBoundedColdPrepared.budget (scalarBacking W) ≤ 
      (8192*330000000066)*(W+1)^48 := by
    change 8192*(scalarBacking W+2) ≤ _
    exact (Nat.mul_le_mul_left 8192 (back.trans (Nat.mul_le_mul_left _ pow))).trans_eq (by ring)
  have one : 1 ≤ (W+1)^48:=Nat.one_le_pow _ _ (by omega)
  unfold budget RecoveryBoundedColdCompile.budget coefficient
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdGraph
