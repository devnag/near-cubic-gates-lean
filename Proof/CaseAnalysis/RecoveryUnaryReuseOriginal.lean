import Proof.CaseAnalysis.RecoveryUnaryReuseOutput

/-! The paid reusable unary call appends the literal original compileExpr
suffix and returns its actual live output with all scratch accounted for. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (budget limit C) (entry (n:=n) row start b.nodes.length C D value limit out)=some r ∧
      r.steps ≤ budget limit C ∧ r.final.heads=heads emitted ∧
      r.final.tapes=data 0 compiled.output.val C D value limit
        (forward (n:=n) row start b.nodes.length value limit out).flag emitted := by
  let compiled:=compileExpr b (unaryEqualsExpr row start limit value hblock)
  let items:=unaryItems row start limit value hblock
  let a:=forward (n:=n) row start b.nodes.length value limit out
  let f:=result row start b.nodes.length value limit out hblock
  have hl : items.length=limit := by simp only [items,unaryItems,List.length_ofFn]
  have hz : f.erased ≤ C := RecoveryBoundedSelectorLoop.unary_erased_bound b.nodes.length a.position W C
    (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) items (by rw [hl]; exact hp) hC
  obtain ⟨old,oldRun,_,oldGraph,oldOutput,_,_,_,_,_,_⟩:=
    RecoveryBoundedNativeUnaryJoin.original_run b row start limit value W C out [] hblock hi hp hC
  obtain ⟨base,baseRun,_,_,baseData⟩:=RecoveryBoundedNativeUnaryJoin.complete_run
    b row start limit value W C out [] hblock hi hp hC
  have he : base=old := Option.some.inj (baseRun.symm.trans oldRun)
  subst base
  rw [baseData,complete_tapes] at oldGraph oldOutput
  change f.out=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native at oldGraph
  change List.replicate f.acc true=List.replicate (b.nodes.length+prefixCount items+limit) true at oldOutput
  have ha : f.acc=compiled.output.val := by
    have hh:=congrArg List.length oldOutput
    simp only [List.length_replicate] at hh
    change f.acc=(compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val
    rw [RecoveryBoundedSelectorLoop.condition_output]
    exact hh
  obtain ⟨r,hr,rs,rh,rt⟩:=unary_run b row start limit value W C D out hblock hi hp hC hD
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh,finished_heads,oldGraph]
  · rw [rt,finished_tapes _ _ _ _ _ _ _ _ _ hz,oldGraph,ha]

end NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
