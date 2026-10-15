import Proof.CaseAnalysis.RecoveryReferenceAppend

/-! Connect the executed framed-reference head to the literal next prefix
of compileGuardedAny, the selector used by both original field selections. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem original_head_nodes {n : ℕ} (b : BooleanDAGBuilder n)
    (condition : BoolExpr n) (wire : LiveWire b) (rest : List (GuardedChoice b)) :
    ((compileGuardedAny b (⟨condition,wire⟩::rest)).extension.suffix).take (condition.nodeCount+1)=
      (compileExpr b condition).extension.suffix++
        [BooleanNode.and (compileExpr b condition).output.val wire.output.val] := by
  rw [RecoveryBoundedUniversal.compileGuardedAny_nodes,compileExpr_nodes,compileExpr_output]
  change (RecoveryBoundedUniversal.guardNodes b.nodes.length
    ((condition,wire.output.val)::RecoveryBoundedUniversal.choices rest)).take _=_
  rw [RecoveryBoundedUniversal.guardNodes]
  rw [List.append_assoc (exprNodes b.nodes.length condition++[_])]
  have hlen : (exprNodes b.nodes.length condition++
      [BooleanNode.and (b.nodes.length+condition.nodeCount-1) wire.output.val]).length=
      condition.nodeCount+1 := by simp only [List.length_append,exprNodes_length,List.length_singleton]
  rw [←hlen,List.take_left]

theorem original_head_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C : ℕ) (out pre skipped tail : List Bool)
    (wire : LiveWire b) (rest : List (GuardedChoice b))
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (budget wire.output.val limit C)
      (entry (n:=n) row start b.nodes.length C value limit wire.output.val out pre skipped tail)=some r ∧
      r.steps ≤ budget wire.output.val limit C ∧
      r.final.heads 37=skipped.length+2*wire.output.val+1 ∧
      r.final.tapes 37=skipped++frame (List.replicate wire.output.val true)++tail ∧
      r.final.tapes 20=out++
        (((compileGuardedAny b (⟨unaryEqualsExpr row start limit value hblock,wire⟩::rest)).extension.suffix).take
          ((unaryEqualsExpr row start limit value hblock).nodeCount+1)).flatMap PCPPRequestNodeSchema.native ∧
      r.final.heads 20=(r.final.tapes 20).length ∧
      r.final.heads=(completeState b row start limit value C wire.output.val out pre skipped tail hblock).heads ∧
      r.final.tapes=(completeState b row start limit value C wire.output.val out pre skipped tail hblock).tapes := by
  obtain ⟨r,hr,rs,rh,rt,ro,rg,rhf,rtf⟩:=append_run b row start limit value W C out pre skipped tail wire hblock hi hp hC
  refine ⟨r,hr,rs,rh,rt,?_,rg,rhf,rtf⟩
  rw [original_head_nodes,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    ←List.append_assoc]
  exact ro

theorem budget_cubic (ref limit W : ℕ) (hr : ref ≤ W) (hl : limit ≤ W) :
    budget ref limit (16384*(W+1)^2) ≤ 8388608*(W+1)^3 := by
  have h:=RecoveryBoundedNativeGuarded.budget_cubic limit W hl
  have power : W+1 ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W*W),Nat.zero_le (W*W*W)]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
