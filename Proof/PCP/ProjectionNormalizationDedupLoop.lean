import Proof.PCP.ProjectionNormalizationDedupSemantics

/-! Complete physical outer keep-last loop. Its driver is the actual parsed
source count; every candidate body returns that driver's next position and
all state needed by the following iteration. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev bodySize := Fintype.card (RecoveryCalls.Control sizes)
noncomputable def loopCfg (phase : Fin 2) (d : Store) := cfg (phase.natAdd bodySize) d
def loopBudget (d : Store) (rows : List SuffixScan.Clause) :=
  3*(SuffixScan.stream rows).length+rows.length*(4*d.count*(2*d.cap+6)+27)+1

theorem iteration (d e : Store) (fuel : ℕ) (r : ExecutionReceipt 12 bodySize)
    (hr : runFrom body fuel (cfg body.start d)=some r) (hf : r.final=stopped e)
    (hread : (cfg body.start d).scanned 3=true) :
    Timed machine (r.steps+2) (loopCfg 0 d) (loopCfg 0 e) := by
  have enter := Timed.single (StreamController.test_halted body 3)
    (StreamController.enter_step body 3 (cfg body.start d) hread)
  obtain ⟨hp,hh⟩ := StreamController.body_prefix body 3 fuel (cfg body.start d) r hr
  have hbody : Timed machine r.steps (controlConfig RecordController.code (cfg body.start d))
      (controlConfig RecordController.code r.final) := ⟨_,hp⟩
  have leave := Timed.single (StreamController.body_halted body 3 r.final.control)
    (StreamController.return_step body 3 r.final hh)
  have h := enter.trans (hbody.trans leave)
  rw [hf] at h
  have ht : 1+(r.steps+1)=r.steps+2 := by omega
  simpa only [ht,machine,loopCfg,stopped,cfg,Composition.restart,controlConfig,RecordController.test] using h

theorem loop_run (rows : List SuffixScan.Clause) (d : Store) (pre suffix : List Bool) (pos : ℕ)
    (hsource : d.source=pre++SuffixScan.stream rows++suffix) (hpos : d.sourcePos=pre.length)
    (hcp : d.candidatePos=d.candidate.length) (hdriver : d.driverPos=pos+1) (hn : pos+rows.length=d.count)
    (hcopy : ∀ row∈rows,(ClauseEquality.stream row).length+2 ≤ d.copyCap)
    (hcap : ∀ a∈rows,∀ b∈rows,ClauseProbe.budget a b ≤ d.cap)
    (hlog : 2*(rows.length*(2*d.cap+6)+1)+2 ≤ d.scanCap) :
    ∃ r,runFrom machine (loopBudget d rows) (loopCfg 0 d)=some r ∧
      r.steps ≤ loopBudget d rows ∧ r.final=loopCfg 1 (process rows d) := by
  classical
  induction rows generalizing d pre pos with
  | nil =>
    have he : pos=d.count := by simpa using hn
    have hread : (cfg body.start d).scanned 3=false := by simp [cfg,Configuration.scanned,hdriver,he]
    obtain ⟨r,hr,hf,hs⟩ := (Timed.single (StreamController.test_halted body 3)
      (StreamController.stop_step body 3 (cfg body.start d) hread)).run (StreamController.stop_halted body 3)
    refine ⟨r,?_,?_,?_⟩
    · simpa [machine,loopCfg,loopBudget,cfg,controlConfig,RecordController.test] using hr
    · simpa [loopBudget] using hs.le
    · simpa [loopCfg,process,cfg,controlConfig,RecordController.stop] using hf
  | cons row rows ih =>
    have hlen : rows.length ≤ d.count := by simp only [List.length_cons] at hn; omega
    have hmul := Nat.mul_le_mul_right (2*d.cap+6) (show rows.length ≤ (row::rows).length by simp)
    have hlogTail : 2*(rows.length*(2*d.cap+6)+1)+2 ≤ d.scanCap := by omega
    obtain ⟨a,ha,hat,haf⟩ := body_run d pre row rows suffix pos hsource hpos hcp hdriver hn
      (hcopy row (by simp)) (fun b hb => hcap row (by simp) b (by simp [hb])) hlogTail
    have hread : (cfg body.start d).scanned 3=true := by
      simp [cfg,Configuration.scanned,hdriver]
      simp only [List.length_cons] at hn
      omega
    have hprefix := iteration d (result d row rows) _ a ha haf hread
    obtain ⟨tail,ht,htt,htf⟩ := ih (result d row rows) (pre++ClauseEquality.stream row) (pos+1)
      (by simpa only [result_source,SuffixScan.stream_cons,List.append_assoc] using hsource)
      (by simp only [result_sourcePos,hpos,List.length_append])
      (by simp only [result_candidatePos,result_candidate,List.length_append])
      (by simp only [result_driverPos,hdriver,Nat.add_assoc])
      (by simp only [result_count,List.length_cons] at hn ⊢; omega)
      (fun r hr => by simpa only [result_copyCap] using hcopy r (by simp [hr]))
      (fun a ha b hb => by simpa only [result_cap] using hcap a (by simp [ha]) b (by simp [hb]))
      (by simpa only [result_cap,result_scanCap] using hlogTail)
    have hmul' := Nat.mul_le_mul_right (2*d.cap+6) hlen
    have hbody : a.steps+2 ≤ 3*(ClauseEquality.stream row).length+4*d.count*(2*d.cap+6)+27 := by
      dsimp only [bodyBudget] at hat
      nlinarith
    rcases hprefix with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail ht
    have htime : (a.steps+2)+loopBudget (result d row rows) rows ≤ loopBudget d (row::rows) := by
      simp only [loopBudget,result_count,result_cap,SuffixScan.stream_cons,List.length_append,List.length_cons]
      nlinarith
    have hm := runFrom_moreFuel machine _
      (loopBudget d (row::rows)-((a.steps+2)+loopBudget (result d row rows) rows)) _ r hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨r,hm,?_,?_⟩
    · rw [hs]; omega
    · rw [hf,htf]
      rfl

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
