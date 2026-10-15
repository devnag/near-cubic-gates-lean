import Proof.CaseAnalysis.RecoveryGuardedConsumer

/-! A paid selective rewind returns only the value cursor. The native graph
and reference stream keep their append positions; the erased inner stack
and field-index backing remain physically allocated for the next guard. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReset
open LocalBitMultitape SourceInterfaces RepairRepresentation
open FinitePredicateCircuit BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 39) : Bool:=decide (i=34)
def caps (C : ℕ) (i : Fin 39) : ℕ:=if i=1 ∨ i=31 then C else 0
noncomputable def machine:=MaskedReset.machine RecoveryBoundedReferenceAppend.machine selected
def budget (ref limit C : ℕ):=2*RecoveryBoundedReferenceAppend.budget ref limit C+2
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out pre skipped tail : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 39 D) (Rewind.recording
    (ZeroPadding.config (caps C)
      (RecoveryBoundedReferenceAppend.entry (n:=n) row start base C value limit ref out pre skipped tail)) 0)

noncomputable def completeState {n bound : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (row : Fin (bound+1))
    (start limit value C D ref : ℕ) (out pre skipped tail : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  let final:=ZeroPadding.config (caps C)
    (RecoveryBoundedReferenceAppend.completeState b row start limit value C ref out pre skipped tail hblock)
  TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate D false)
    {final with heads:=fun i=>if selected i then 0 else final.heads i}

theorem reset_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C D : ℕ) (out pre skipped tail : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C)
    (hD : RecoveryBoundedReferenceAppend.budget wire.output.val limit C ≤ D) :
    ∃ r,runFrom machine (budget wire.output.val limit C)
      (entry (n:=n) row start b.nodes.length C D value limit wire.output.val out pre skipped tail)=some r ∧
      r.steps ≤ budget wire.output.val limit C ∧
      r.final.heads=(completeState b row start limit value C D wire.output.val out pre skipped tail hblock).heads ∧
      r.final.tapes=(completeState b row start limit value C D wire.output.val out pre skipped tail hblock).tapes := by
  obtain ⟨base,hbase,bs,_bh,_bt,_bo,_bg,bhFull,btFull⟩:=
    RecoveryBoundedReferenceAppend.append_run b row start limit value W C out pre skipped tail
      wire hblock hi hp hC
  obtain ⟨p,hpRun,pf,ps,_pp⟩:=ZeroPadding.run_config RecoveryBoundedReferenceAppend.machine (caps C)
    _ _ base hbase
  have hstart : ∀ i,selected i=true →
      (ZeroPadding.config (caps C) (RecoveryBoundedReferenceAppend.entry (n:=n) row start
        b.nodes.length C value limit wire.output.val out pre skipped tail)).heads i=0 := by
    intro i hs
    have he : i=34 := by simpa only [selected,decide_eq_true_eq] using hs
    subst i
    rfl
  obtain ⟨r,hr,rf,rs,_rp⟩:=MaskedReset.workspace_run RecoveryBoundedReferenceAppend.machine selected
    _ D _ p hpRun hstart (by rw [ps]; exact bs.trans hD)
  have hb : 2*p.steps+2 ≤ budget wire.output.val limit C := by
    rw [ps]
    unfold budget
    omega
  have more:=runFrom_moreFuel machine _ (budget wire.output.val limit C-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_⟩
  · rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config]
    rw [bhFull]
    rfl
  · rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config]
    rw [btFull]
    rfl

theorem budget_cubic (ref limit W : ℕ) (hr : ref ≤ W) (hl : limit ≤ W) :
    budget ref limit (16384*(W+1)^2) ≤ 16777218*(W+1)^3 := by
  have h:=RecoveryBoundedReferenceAppend.budget_cubic ref limit W hr hl
  have hp : 0 < (W+1)^3 := by positivity
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReset
