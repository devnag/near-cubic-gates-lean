import Proof.CaseAnalysis.RecoverySelectorPairBudget

/-! The original unary expression compiler runs with its reusable backing
and pays to restore its value cursor. Graph output and saved fields remain. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 36):=decide (i=34)
def caps (C : ℕ) (i : Fin 36):=if i=1 ∨ i=29 ∨ i=31 ∨ i=34 then C else 0
noncomputable def machine:=MaskedReset.machine RecoveryBoundedNativeUnaryJoin.machine selected
def budget (limit C : ℕ):=2*RecoveryBoundedNativeUnaryJoin.budget limit C+2
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit : ℕ) (out : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 36 D) (Rewind.recording
    (ZeroPadding.config (caps C)
      (RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start base C value limit out [])) 0)
noncomputable def finished {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit : ℕ) (out : List Bool) (hblock : start+limit ≤ rowWidth n bound) :=
  let c:=ZeroPadding.config (caps C)
    (RecoveryBoundedNativeUnaryJoin.completeState row start base C value limit out [] hblock)
  TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate D false)
    {c with heads:=fun i=>if selected i then 0 else c.heads i}

theorem unary_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit C ≤ D) :
    ∃ r,runFrom machine (budget limit C) (entry (n:=n) row start b.nodes.length C D value limit out)=some r ∧
      r.steps ≤ budget limit C ∧
      r.final.heads=(finished row start b.nodes.length C D value limit out hblock).heads ∧
      r.final.tapes=(finished row start b.nodes.length C D value limit out hblock).tapes := by
  obtain ⟨base,hbase,bs,bh,bt⟩:=RecoveryBoundedNativeUnaryJoin.complete_run
    b row start limit value W C out [] hblock hi hp hC
  obtain ⟨p,hpRun,pf,ps,_⟩:=ZeroPadding.run_config RecoveryBoundedNativeUnaryJoin.machine (caps C) _ _ base hbase
  have hstart : ∀ i,selected i=true →
      (ZeroPadding.config (caps C)
        (RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start b.nodes.length C value limit out [])).heads i=0 := by
    intro i hs
    have he : i=34 := by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.workspace_run RecoveryBoundedNativeUnaryJoin.machine selected _ D _ p hpRun
    hstart (by rw [ps]; exact bs.trans hD)
  have hb : 2*p.steps+2 ≤ budget limit C := by rw [ps]; unfold budget; omega
  have more:=runFrom_moreFuel machine _ (budget limit C-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩
  · rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config]
    rw [bh]
    rfl
  · rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config]
    rw [bt]
    rfl

theorem budget_cubic (limit W : ℕ) (hl : limit ≤ W) :
    budget limit (16384*(W+1)^2) ≤ 8388610*(W+1)^3 := by
  have h:=RecoveryBoundedNativeGuarded.budget_cubic limit W hl
  have hb : RecoveryBoundedNativeUnaryJoin.budget limit (16384*(W+1)^2) ≤
      RecoveryBoundedNativeGuarded.budget limit (16384*(W+1)^2) := by
    unfold RecoveryBoundedNativeGuarded.budget
    omega
  have hp : 0 < (W+1)^3 := by positivity
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedUnaryReuse
