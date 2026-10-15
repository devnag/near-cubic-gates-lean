import Proof.PCP.ProjectionNormalizationSharedDriver

/-! Scan the actual remaining suffix of the outer unary driver in place.
No remaining-count word is supplied or copied. The enclosing restoration
returns this cursor and the original clause cursor to their entry positions. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.SharedDriverScan
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine SharedDriverProbe.machine 5
noncomputable def cfg (phase : Fin 2) (candidate source : List Bool) (candidatePos sourcePos : ℕ)
    (eq found : Bool) (cap count driver : ℕ) :=
  SharedDriverProbe.cfg (phase.natAdd SharedDriverProbe.size) candidate source candidatePos sourcePos eq found cap count driver

theorem driver_read {s : ℕ} (q : Fin s) (candidate source : List Bool) (cp sp : ℕ)
    (eq found : Bool) (cap count pos : ℕ) :
    (SharedDriverProbe.cfg q candidate source cp sp eq found cap count (pos+1)).scanned 5=decide (pos<count) := by
  simp [SharedDriverProbe.cfg,Configuration.scanned,TapeEmbedding.config,Fin.addCases]

theorem iteration (c : Configuration 6 SharedDriverProbe.size) (fuel : ℕ)
    (r : ExecutionReceipt 6 SharedDriverProbe.size) (hc : c.control=SharedDriverProbe.machine.start)
    (hr : runFrom SharedDriverProbe.machine fuel c=some r) (hread : c.scanned 5=true) :
    Timed machine (r.steps+2)
      (controlConfig (fun _ => RecordController.test SharedDriverProbe.size) c)
      (controlConfig (fun _ => RecordController.test SharedDriverProbe.size) r.final) := by
  have he : Composition.restart c SharedDriverProbe.machine.start=c := by
    apply configuration_ext
    · exact hc.symm
    · rfl
    · rfl
  have enter := Timed.single (StreamController.test_halted SharedDriverProbe.machine 5)
    (StreamController.enter_step SharedDriverProbe.machine 5 c hread)
  rw [he] at enter
  obtain ⟨hp,hh⟩ := StreamController.body_prefix SharedDriverProbe.machine 5 fuel c r hr
  have body : Timed machine r.steps (controlConfig RecordController.code c)
      (controlConfig RecordController.code r.final) := ⟨_,hp⟩
  have leave := Timed.single (StreamController.body_halted SharedDriverProbe.machine 5 r.final.control)
    (StreamController.return_step SharedDriverProbe.machine 5 r.final hh)
  have h := enter.trans (body.trans leave)
  have ht : 1+(r.steps+1)=r.steps+2 := by omega
  simpa only [ht,machine] using h

theorem scan_run (left : SuffixScan.Clause) (candidatePrefix pre : List Bool) (rows : List SuffixScan.Clause)
    (suffix : List Bool) (eq found : Bool) (cap total pos : ℕ) (hn : pos+rows.length=total)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap) :
    ∃ r,runFrom machine (rows.length*(2*cap+6)+1)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap total (pos+1))=some r ∧
      r.steps ≤ rows.length*(2*cap+6)+1 ∧
      r.final=cfg 1 (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length (pre.length+(SuffixScan.stream rows).length) (SuffixScan.endEq left rows eq)
        (SuffixScan.seen left rows found) cap total (total+1) := by
  classical
  induction rows generalizing pre eq found pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    let c := SharedDriverProbe.cfg SharedDriverProbe.machine.start (candidatePrefix++ClauseEquality.stream left)
      (pre++suffix) candidatePrefix.length pre.length eq found cap total (total+1)
    have hh : c.scanned 5=false := by simp [c,driver_read]
    obtain ⟨r,hr,hf,hs⟩ := (Timed.single (StreamController.test_halted SharedDriverProbe.machine 5)
      (StreamController.stop_step SharedDriverProbe.machine 5 c hh)).run
      (StreamController.stop_halted SharedDriverProbe.machine 5)
    refine ⟨r,?_,?_,?_⟩
    · simpa [machine,cfg,c,SuffixScan.stream,SharedDriverProbe.cfg,controlConfig,TapeEmbedding.config,ProbeReuse.cfg,RecordController.test] using hr
    · simpa using hs.le
    · simpa [cfg,c,SuffixScan.stream,SuffixScan.endEq,SuffixScan.seen,SharedDriverProbe.cfg,controlConfig,TapeEmbedding.config,ProbeReuse.cfg,RecordController.stop] using hf
  | cons row rows ih =>
    have hrow := hcap row (by simp)
    have htail : ∀ r∈rows,ClauseProbe.budget left r ≤ cap := fun r hr => hcap r (by simp [hr])
    obtain ⟨body,hb,hbt,hbf⟩ := SharedDriverProbe.probe_run left row candidatePrefix pre
      (SuffixScan.stream rows++suffix) eq found cap total (pos+1) hrow
    have hstep := iteration
      (SharedDriverProbe.cfg SharedDriverProbe.machine.start (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream row++(SuffixScan.stream rows++suffix)) candidatePrefix.length pre.length eq found cap total (pos+1))
      _ body rfl hb (by rw [driver_read]; simp only [List.length_cons] at hn; simp; omega)
    rw [hbf] at hstep
    change Timed machine (body.steps+2)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream row++(SuffixScan.stream rows++suffix))
        candidatePrefix.length pre.length eq found cap total (pos+1))
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream row++(SuffixScan.stream rows++suffix))
        candidatePrefix.length (pre.length+(ClauseEquality.stream row).length) (decide (left=row))
        (found||decide (left=row)) cap total (pos+1+1)) at hstep
    obtain ⟨tail,ht,htt,htf⟩ := ih (pre++ClauseEquality.stream row) (decide (left=row))
      (found||decide (left=row)) (pos+1) (by simp only [List.length_cons] at hn; omega) htail
    have hmid : cfg 0 (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream row++(SuffixScan.stream rows++suffix)) candidatePrefix.length
        (pre.length+(ClauseEquality.stream row).length) (decide (left=row)) (found||decide (left=row)) cap total (pos+1+1)=
      cfg 0 (candidatePrefix++ClauseEquality.stream left) ((pre++ClauseEquality.stream row)++SuffixScan.stream rows++suffix)
        candidatePrefix.length (pre++ClauseEquality.stream row).length (decide (left=row))
        (found||decide (left=row)) cap total ((pos+1)+1) := by simp only [List.append_assoc,List.length_append]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hstep⟩
    obtain ⟨result,hr,hf,hs,_⟩ := hstep.followedBy tail ht
    have htime : (body.steps+2)+(rows.length*(2*cap+6)+1) ≤ (row::rows).length*(2*cap+6)+1 := by
      simp only [List.length_cons]
      nlinarith
    have hm := runFrom_moreFuel machine _
      ((row::rows).length*(2*cap+6)+1-((body.steps+2)+(rows.length*(2*cap+6)+1))) _ result hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,?_,?_,?_⟩
    · simpa only [SuffixScan.stream_cons,List.append_assoc] using hm
    · rw [hs]; omega
    · rw [hf,htf]
      simp only [SuffixScan.stream_cons,SuffixScan.endEq,SuffixScan.seen_cons,List.append_assoc,List.length_append,Nat.add_assoc]

end NearCubicWires.RepairSource.ProjectionNormalization.SharedDriverScan
