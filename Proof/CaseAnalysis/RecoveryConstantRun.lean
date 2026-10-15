import Proof.CaseAnalysis.RecoveryConstantUnaryRun

/-! The actual second-selector output is saved, its counter is advanced,
and the original constant-value expression executes with both child outputs
retained for the subsequent NOT/AND/OR and guarded tag cases. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine prepare unary
def budget (prior index limit C : ℕ):=2*C+4*prior+4*index+30+RecoveryBoundedUnaryReuse.budget limit C

theorem constant_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit prior W C D total L : ℕ) (out source : List Bool)
    (secondIndex : ℕ) (savedFirst : List Bool) (hblock : start+limit ≤ rowWidth n bound)
    (hbase : prior+1=b.nodes.length)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hsecond : secondIndex ≤ W) (htotal : total ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let compiled:=compileExpr b (unaryEqualsExpr row start limit 1 hblock)
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom machine (budget prior index limit C)
      ⟨machine.start,heads out,data secondIndex prior C D total limit total L out source secondIndex index savedFirst
        (List.replicate C false)⟩=some r ∧
      r.steps ≤ budget prior index limit C ∧ r.final.heads=heads emitted ∧
      r.final.tapes=afterUnary index compiled.output.val C D limit total L
        (RecoveryBoundedUnaryReuse.forward (n:=n) row start b.nodes.length 1 limit out).flag
        emitted source secondIndex index savedFirst (ZeroPadding.pad C (List.replicate prior true)) := by
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  have hpriorC : prior+1 ≤ C := by nlinarith [Nat.zero_le (W*W)]
  have hsC : secondIndex ≤ C := by nlinarith [Nat.zero_le (W*W)]
  have hiC : index+1 ≤ C := by
    change RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+1 ≤ C
    nlinarith [Nat.zero_le (W*W)]
  have htC : total ≤ C := by nlinarith [Nat.zero_le (W*W)]
  obtain ⟨a,ar,asteps,ah,atapes⟩:=prepare_run secondIndex prior C D total limit total L out source secondIndex index savedFirst
    hpriorC hsC hiC htC
  obtain ⟨r,hr,rs,rh,rt⟩:=unary_run b row start limit W C D total L out source secondIndex index savedFirst
    (ZeroPadding.pad C (List.replicate prior true)) hblock hi hp hC hD
  have hlast : runFrom unary (RecoveryBoundedUnaryReuse.budget limit C) (restart a.final unary.start)=some r := by
    change runFrom unary _ ⟨unary.start,a.final.heads,a.final.tapes⟩=some r
    rw [ah,atapes,hbase]
    exact hr
  have full:=Composition.run_join prepare unary _ _ _ a r ar hlast
  have hbudget : (2*C+4*prior+4*index+29)+1+RecoveryBoundedUnaryReuse.budget limit C=budget prior index limit C := by
    unfold budget
    omega
  rw [hbudget] at full
  refine ⟨joinedReceipt a r,full,?_,rh,rt⟩
  change a.steps+1+r.steps ≤ budget prior index limit C
  rw [asteps]
  unfold budget
  omega

theorem budget_cubic (prior index limit W : ℕ) (hp : prior ≤ W) (hi : index ≤ W) (hl : limit ≤ W) :
    budget prior index limit (16384*(W+1)^2) ≤ 16777232*(W+1)^3 := by
  have h:=RecoveryBoundedUnaryReuse.budget_cubic limit W hl
  unfold budget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedConstant
