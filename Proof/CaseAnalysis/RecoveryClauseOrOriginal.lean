import Proof.CaseAnalysis.RecoveryClauseLiteralOriginal

/-! The reusable paid OR run is the original compileOr, with unchanged
query references, literal stream and bounded scratch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOrOriginal
open LocalBitMultitape SourceInterfaces RepairRepresentation FinitePredicateCircuit
open BoundedOracleStructuralCircuit RecoveryBoundedClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b) :
    (compileOr b left right).output.val=b.nodes.length := rfl
theorem count {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b) :
    (compileOr b left right).final.nodes.length=b.nodes.length+1 := by
  change (b.nodes++([.or left.output.val right.output.val] : List (BooleanNode n))).length=_
  simp only [List.length_append,List.length_singleton]
theorem graph_eq {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b) (out : List Bool) :
    RecoveryBoundedClauseOr.graph left.output.val right.output.val out=
      out++(compileOr b left right).extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  rw [RecoveryBoundedClauseMeaning.or_native]
  exact congrArg (fun xs=>out++xs) (RecoveryBoundedClauseNative.or_native n left.output.val right.output.val)

theorem original_run {n : ℕ} (b : BooleanDAGBuilder n) (left right : LiveWire b)
    (H : Fin 71→ℕ) (A : Fin 71→List Bool) (W C L : ℕ) (out pre source refs : List Bool)
    (h : State H A b.nodes.length left.output.val right.output.val C L out pre source refs)
    (hb : b.nodes.length ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let compiled:=compileOr b left right
    ∃ r,runFrom RecoveryBoundedClauseOr.machine (literalBudget W C)
      ⟨RecoveryBoundedClauseOr.machine.start,H,A⟩=some r ∧ r.steps ≤ literalBudget W C ∧
      State r.final.heads r.final.tapes compiled.final.nodes.length compiled.output.val right.output.val C L
        (out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) pre source refs := by
  obtain ⟨r,rr,rs,_rh,_rt,hs⟩:=RecoveryBoundedClauseOr.node_run H A b.nodes.length left.output.val right.output.val
    W C L out pre source refs h hb (left.output.isLt.le.trans hb) (right.output.isLt.le.trans hb) hC
  refine ⟨r,rr,rs,?_⟩
  rw [output,count,←graph_eq]
  exact hs

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOrOriginal
