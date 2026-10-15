import Proof.CaseAnalysis.RecoveryConstantUnaryLayout

/-! The original constant-value equality executes beside both selected
children and returns its exact graph suffix, output and complete bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem unary_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W C D total L : ℕ) (out source : List Bool)
    (secondIndex firstIndex : ℕ) (savedFirst savedSecond : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    let compiled:=compileExpr b (unaryEqualsExpr row start limit 1 hblock)
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom unary (RecoveryBoundedUnaryReuse.budget limit C)
      ⟨unary.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond⟩=some r ∧
      r.steps ≤ RecoveryBoundedUnaryReuse.budget limit C ∧ r.final.heads=heads emitted ∧
      r.final.tapes=afterUnary (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val C D limit total L (RecoveryBoundedUnaryReuse.forward (n:=n) row start b.nodes.length 1 limit out).flag
        emitted source secondIndex firstIndex savedFirst savedSecond := by
  have hC1 : 1 ≤ C := by
    have h : 0 < (W+1)^2 := by positivity
    omega
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedUnaryReuse.literal_run b row start limit 1 W C D out hblock hi hp hC hD
  obtain ⟨r,hr,rf,rs⟩:=RecoveryFocus.run_config unarySlots unary_injective RecoveryBoundedUnaryReuse.machine
    (heads out) (data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      b.nodes.length C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond) _ _ p hpRun
  have he : RecoveryFocus.config unarySlots (heads out)
      (data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond)
      (RecoveryBoundedUnaryReuse.entry (n:=n) row start b.nodes.length C D 1 limit out)=
      (⟨unary.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond⟩ : Configuration 48 _) := by
    apply WilliamsSourceCrop.focus_same unarySlots
      (⟨unary.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length C D 1 limit total L out source secondIndex firstIndex savedFirst savedSecond⟩ : Configuration 48 _)
      (RecoveryBoundedUnaryReuse.entry (n:=n) row start b.nodes.length C D 1 limit out)
    · intro j
      rw [RecoveryBoundedUnaryReuse.entry_heads]
      exact unary_heads out j
    · intro j
      rw [RecoveryBoundedUnaryReuse.entry_tapes]
      exact unary_tapes _ _ _ _ _ _ _ _ _ _ _ _ _ hC1 j
  rw [he] at hr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · rw [rf]
    have hheads:=unary_final_heads out
      (out++(compileExpr b (unaryEqualsExpr row start limit 1 hblock)).extension.suffix.flatMap PCPPRequestNodeSchema.native)
    funext i
    have h:=congrFun hheads i
    cases hpi : RecoveryFocus.pick unarySlots i with
    | none=>simpa only [RecoveryFocus.config,hpi] using h
    | some j=>simpa only [RecoveryFocus.config,hpi,ph] using h
  · rw [rf]
    change install unarySlots _ p.final.tapes=_
    rw [pt]
    exact unary_install _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
