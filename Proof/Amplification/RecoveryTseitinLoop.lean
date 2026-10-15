import Proof.Amplification.RecoveryTseitinBody

/-! The fixed ordinary repeater emits the original tautologies in increasing
input-variable order. Every binary increment, return and final rewind is paid. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinTautology
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open RecoveryTseitinKernel CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem cfg_data {t s : Nat} (phase : Fin 5) (c d : Configuration t s) (total driver : Nat)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

private theorem iteration_data {t s fuel : Nat} (body : Machine t s)
    (c d : Configuration t s) (total pos : Nat) (r : ExecutionReceipt t s)
    (hc : c.control=body.start) (hp : pos<total) (hr : runFrom body fuel c=some r)
    (hh : r.final.heads=d.heads) (ht : r.final.tapes=d.tapes) :
    Timed (RepeatMachine.machine body (fun _ _=>true)) (r.steps+2)
      (RepeatMachine.cfg 0 c total (pos+1)) (RepeatMachine.cfg 0 d total (pos+2)) := by
  have h := RepeatMachine.iteration body (fun _ _=>true) c total pos r hc hp hr
  change Timed _ _ _ (RepeatMachine.cfg 0 r.final total (pos+2)) at h
  rw [cfg_data 0 r.final d total (pos+2) hh ht] at h
  exact h

private theorem exhaust_run {t s : Nat} (body : Machine t s) (c : Configuration t s) (total : Nat) :
    ∃ r,runFrom (RepeatMachine.machine body (fun _ _=>true)) (total+3)
      (RepeatMachine.cfg 0 c total (total+1))=some r ∧
      r.final=RepeatMachine.cfg 3 c total 1 ∧ r.steps=total+3 :=
  (RepeatMachine.exhaust body (fun _ _=>true) c total).run
    (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

noncomputable def loopMachine := RepeatMachine.machine bodyMachine (fun _ _=>true)
noncomputable def loopCfg (phase : Fin 5) (cap : Nat) (data : Fin 239→List Bool)
    (out : List Bool) (total driver : Nat) := RepeatMachine.cfg phase
      (⟨bodyMachine.start,heads out.length,input data out cap⟩ : Configuration 241 _)
      total driver
def emitted (index : Nat) : Nat→List Bool
  | 0=>[]
  | count+1=>RepairOrdinary.frame (word index)++emitted (index+1) count

theorem remaining_run (cap index count : Nat) (ambient : Fin 239→List Bool) (out : List Bool)
    (total pos : Nat) (hn : pos+count=total) (hv : Valid cap index ambient)
    (hc : ∀ j,j<count → capacity (index+j) ≤ cap) :
    ∃ after : Fin 239→List Bool,∃ r,
      runFrom loopMachine (count*(bodyBudget cap+2)+total+3)
        (loopCfg 0 cap ambient out total (pos+1))=some r ∧
      r.final=loopCfg 3 cap after (out++emitted index count) total 1 ∧
      Valid cap (index+count) after ∧
      (∀ i : Fin 239,1 ≤ i.val → i.val<3 → after i=ambient i) ∧
      r.steps ≤ count*(bodyBudget cap+2)+total+3 := by
  induction count generalizing index ambient out pos with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := exhaust_run bodyMachine
      (⟨bodyMachine.start,heads out.length,input ambient out cap⟩ : Configuration 241 _) total
    exact ⟨ambient,r,by simpa only [loopMachine,loopCfg,Nat.zero_mul,Nat.zero_add] using hr,
      by simpa only [loopCfg,emitted,List.append_nil] using hf,
      by simpa only [Nat.add_zero] using hv,by intros; rfl,by simpa only [Nat.zero_mul,Nat.zero_add] using hs.le⟩
  | succ count ih =>
    obtain ⟨middle,body,hbody,bh,bt,bv,bkeep,bs⟩ := body_run cap index ambient out
      (by simpa only [Nat.add_zero] using hc 0 (by omega)) hv
    let next := (⟨bodyMachine.start,heads (out++RepairOrdinary.frame (word index)).length,
      input middle (out++RepairOrdinary.frame (word index)) cap⟩ : Configuration 241 _)
    have hstep := iteration_data bodyMachine _ next total pos body rfl (by omega) hbody bh bt
    change Timed loopMachine (body.steps+2)
      (loopCfg 0 cap ambient out total (pos+1))
      (loopCfg 0 cap middle (out++RepairOrdinary.frame (word index)) total (pos+2)) at hstep
    obtain ⟨after,rest,hrest,rf,rv,rkeep,rs⟩ := ih (index+1) middle (out++RepairOrdinary.frame (word index))
      (pos+1) (by omega) bv (by
        intro j hj
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using hc (j+1) (by omega))
    have hmid : pos+2=(pos+1)+1 := by omega
    rw [hmid] at hstep
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hr,hf,hs,_hspace⟩ := hprefix.followedBy rest hrest
    have hbound : (body.steps+2)+(count*(bodyBudget cap+2)+total+3) ≤
        (count+1)*(bodyBudget cap+2)+total+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have hmore := runFrom_moreFuel loopMachine _
      ((count+1)*(bodyBudget cap+2)+total+3-((body.steps+2)+(count*(bodyBudget cap+2)+total+3))) _ result hr
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨after,result,hmore,?_,?_,?_,?_⟩
    · rw [hf,rf]
      simp only [emitted,List.append_assoc]
    · simpa only [Nat.add_assoc,Nat.add_comm 1 count] using rv
    · intro i hi hit
      exact (rkeep i hi hit).trans (bkeep i hi hit)
    · rw [hs]
      omega

end NearCubicWires.RepairSource.RecoveryTseitinTautology
