import Proof.PCP.ProjectionNormalizationReuse

namespace NearCubicWires.RepairSource.ProjectionNormalization.SuffixScan
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Clause := Fin 3 → List Bool
def stream (rows : List Clause) := (rows.map ClauseEquality.stream).flatten
noncomputable def endEq (left : Clause) : List Clause → Bool → Bool
  | [],old => old
  | right::rows,_ => endEq left rows (decide (left=right))
noncomputable def seen (left : Clause) (rows : List Clause) (old : Bool) := old||decide (left∈rows)
noncomputable def machine := RepeatMachine.machine ClauseProbe.machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (candidate source : List Bool) (candidatePos sourcePos : ℕ)
    (eq found : Bool) (cap total driver : ℕ) :=
  RepeatMachine.cfg phase (ProbeReuse.cfg ClauseProbe.machine.start candidate source candidatePos sourcePos eq found cap) total driver

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (row : Clause) (rows : List Clause) :
    stream (row::rows)=ClauseEquality.stream row++stream rows := rfl

theorem seen_cons (left right : Clause) (rows : List Clause) (old : Bool) :
    seen left rows (old||decide (left=right))=seen left (right::rows) old := by
  classical
  simp [seen,List.mem_cons,Bool.or_assoc]

theorem remaining (left : Clause) (candidatePrefix pre : List Bool) (rows : List Clause)
    (suffix : List Bool) (eq found : Bool) (cap total pos : ℕ) (hn : pos+rows.length=total)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap) :
    ∃ r,runFrom machine (rows.length*(2*cap+4)+total+3)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++stream rows++suffix)
        candidatePrefix.length pre.length eq found cap total (pos+1))=some r ∧
      r.steps ≤ rows.length*(2*cap+4)+total+3 ∧
      r.final=cfg 3 (candidatePrefix++ClauseEquality.stream left) (pre++stream rows++suffix)
        candidatePrefix.length (pre.length+(stream rows).length) (endEq left rows eq)
        (seen left rows found) cap total 1 := by
  classical
  induction rows generalizing pre eq found pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust ClauseProbe.machine (fun _ _ => true)
      (ProbeReuse.cfg ClauseProbe.machine.start (candidatePrefix++ClauseEquality.stream left)
        (pre++suffix) candidatePrefix.length pre.length eq found cap) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.length_nil,List.append_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
    · simpa [cfg,endEq,seen] using hf
  | cons row rows ih =>
    have hrow := hcap row (by simp)
    have htail : ∀ r∈rows,ClauseProbe.budget left r ≤ cap := fun r hr => hcap r (by simp [hr])
    obtain ⟨body,hb,hbt,hbf⟩ := ProbeReuse.probe_run left row candidatePrefix pre (stream rows++suffix) eq found cap hrow
    have hstep := RepeatMachine.iteration ClauseProbe.machine (fun _ _ => true)
      (ProbeReuse.cfg ClauseProbe.machine.start (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream row++(stream rows++suffix)) candidatePrefix.length pre.length eq found cap)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    rw [hbf] at hstep
    change Timed machine (body.steps+2)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream row++(stream rows++suffix))
        candidatePrefix.length pre.length eq found cap total (pos+1))
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream row++(stream rows++suffix))
        candidatePrefix.length (pre.length+(ClauseEquality.stream row).length) (decide (left=row))
        (found||decide (left=row)) cap total (pos+2)) at hstep
    obtain ⟨tail,ht,htt,htf⟩ := ih (pre++ClauseEquality.stream row) (decide (left=row))
      (found||decide (left=row)) (pos+1) (by simp only [List.length_cons] at hn; omega) htail
    have hmid : cfg 0 (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream row++(stream rows++suffix)) candidatePrefix.length
        (pre.length+(ClauseEquality.stream row).length) (decide (left=row))
        (found||decide (left=row)) cap total (pos+2)=
      cfg 0 (candidatePrefix++ClauseEquality.stream left) ((pre++ClauseEquality.stream row)++stream rows++suffix)
        candidatePrefix.length (pre++ClauseEquality.stream row).length (decide (left=row))
        (found||decide (left=row)) cap total ((pos+1)+1) := by
      simp only [List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hstep⟩
    obtain ⟨result,hr,hf,hs,_⟩ := hstep.followedBy tail ht
    have htime : (body.steps+2)+(rows.length*(2*cap+4)+total+3) ≤
        (row::rows).length*(2*cap+4)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have hm := runFrom_moreFuel machine _
      ((row::rows).length*(2*cap+4)+total+3-((body.steps+2)+(rows.length*(2*cap+4)+total+3))) _ result hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hs]; omega
    · rw [hf,htf]
      simp only [stream_cons,endEq,seen_cons,List.append_assoc,List.length_append,Nat.add_assoc]

theorem scan_run (left : Clause) (candidatePrefix pre : List Bool) (rows : List Clause)
    (suffix : List Bool) (eq found : Bool) (cap : ℕ)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap) :
    ∃ r,runFrom machine (rows.length*(2*cap+5)+3)
      (cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++stream rows++suffix)
        candidatePrefix.length pre.length eq found cap rows.length 1)=some r ∧
      r.steps ≤ rows.length*(2*cap+5)+3 ∧
      r.final=cfg 3 (candidatePrefix++ClauseEquality.stream left) (pre++stream rows++suffix)
        candidatePrefix.length (pre.length+(stream rows).length) (endEq left rows eq)
        (seen left rows found) cap rows.length 1 := by
  have h := remaining left candidatePrefix pre rows suffix eq found cap rows.length 0 (by omega) hcap
  have he : rows.length*(2*cap+4)+rows.length+3=rows.length*(2*cap+5)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.ProjectionNormalization.SuffixScan
