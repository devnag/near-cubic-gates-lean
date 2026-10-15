import Proof.PCP.ProjectionNormalizationDedupLayout

/-! Actual focused callee receipts on the common keep-last store. Source
positions here are identified with literal prefixes already reached by the
preceding callee; every copy, rewind, and branch is paid by the fixed graph. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copyOut (d : Store) (row : SuffixScan.Clause) :=
  { d with
    sourcePos := d.sourcePos+(ClauseEquality.stream row).length
    candidate := d.candidate++ClauseEquality.stream row
    candidatePos := d.candidate.length }
noncomputable def scanOut (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :=
  {d with eq:=SuffixScan.endEq row rows d.eq,found:=SuffixScan.seen row rows d.found}
def keepOut (d : Store) (row : SuffixScan.Clause) :=
  {d with candidatePos:=d.candidatePos+(ClauseEquality.stream row).length,out:=d.out++ClauseEquality.stream row}
def discardOut (d : Store) (row : SuffixScan.Clause) :=
  {d with candidatePos:=d.candidatePos+(ClauseEquality.stream row).length,discard:=d.discard++ClauseEquality.stream row}

theorem copy_run (d : Store) (pre : List Bool) (row : SuffixScan.Clause) (suffix : List Bool)
    (hsource : d.source=pre++ClauseEquality.stream row++suffix) (hpos : d.sourcePos=pre.length)
    (hcp : d.candidatePos=d.candidate.length) (hcap : (ClauseEquality.stream row).length+2 ≤ d.copyCap) :
    ∃ r,runFrom copyProgram (2*(ClauseEquality.stream row).length+6) (cfg copyProgram.start d)=some r ∧
      r.steps ≤ 2*(ClauseEquality.stream row).length+6 ∧ r.final=cfg CandidateCopy.finalCode (copyOut d row) := by
  obtain ⟨base,hb,hbs,hbf⟩ := CandidateCopy.copy_run pre row suffix d.candidate d.copyCap hcap
  rw [←hsource,←hpos] at hb hbf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config copySlots (by decide) CandidateCopy.machine
    (cfg copyProgram.start d).heads (cfg copyProgram.start d).tapes _ _ base hb
  rw [copy_place,←hcp] at hr
  refine ⟨r,hr,hrs.le.trans hbs,?_⟩
  rw [hrf,hbf,copy_place]
  rfl

theorem scan_run (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause)
    (candidatePrefix pre suffix : List Bool) (pos : ℕ)
    (hsource : d.source=pre++SuffixScan.stream rows++suffix) (hpos : d.sourcePos=pre.length)
    (hcandidate : d.candidate=candidatePrefix++ClauseEquality.stream row) (hcp : d.candidatePos=candidatePrefix.length)
    (hdriver : d.driverPos=pos+1) (hn : pos+rows.length=d.count)
    (hcap : ∀ r∈rows,ClauseProbe.budget row r ≤ d.cap)
    (hlog : 2*(rows.length*(2*d.cap+6)+1)+2 ≤ d.scanCap) :
    ∃ r,runFrom scanProgram (4*(rows.length*(2*d.cap+6)+1)+6) (cfg scanProgram.start d)=some r ∧
      r.steps ≤ 4*(rows.length*(2*d.cap+6)+1)+6 ∧ r.final=cfg SharedDriverRestore.finalCode (scanOut d row rows) := by
  obtain ⟨base,hb,hbs,hbf⟩ := SharedDriverReuse.scan_run row candidatePrefix pre rows suffix d.eq d.found
    d.cap d.count pos d.scanCap hn hcap hlog
  rw [←hsource,←hcandidate,←hpos,←hcp,←hdriver] at hb hbf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config scanSlots (by decide) SharedDriverRestore.machine
    (cfg scanProgram.start d).heads (cfg scanProgram.start d).tapes _ _ base hb
  rw [scan_place] at hr
  refine ⟨r,hr,hrs.le.trans hbs,?_⟩
  rw [hrf,hbf,scan_place]
  rfl

theorem keep_run (d : Store) (pre : List Bool) (row : SuffixScan.Clause)
    (hcandidate : d.candidate=pre++ClauseEquality.stream row) (hcp : d.candidatePos=pre.length) :
    ∃ r,runFrom keepProgram ((ClauseEquality.stream row).length+2) (cfg keepProgram.start d)=some r ∧
      r.steps=(ClauseEquality.stream row).length+2 ∧ r.final=cfg ClauseCopy.finalCode (keepOut d row) := by
  obtain ⟨base,hb,hbf,hbs⟩ := ClauseCopy.copy_run pre row [] d.out
  simp only [List.append_nil] at hb hbf
  rw [←hcandidate,←hcp] at hb hbf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config keepSlots (by decide) ClauseCopy.machine
    (cfg keepProgram.start d).heads (cfg keepProgram.start d).tapes _ _ base hb
  rw [keep_place] at hr
  refine ⟨r,hr,hrs.trans hbs,?_⟩
  rw [hrf,hbf,keep_place]
  rfl

theorem discard_run (d : Store) (pre : List Bool) (row : SuffixScan.Clause)
    (hcandidate : d.candidate=pre++ClauseEquality.stream row) (hcp : d.candidatePos=pre.length) :
    ∃ r,runFrom discardProgram ((ClauseEquality.stream row).length+2) (cfg discardProgram.start d)=some r ∧
      r.steps=(ClauseEquality.stream row).length+2 ∧ r.final=cfg ClauseCopy.finalCode (discardOut d row) := by
  obtain ⟨base,hb,hbf,hbs⟩ := ClauseCopy.copy_run pre row [] d.discard
  simp only [List.append_nil] at hb hbf
  rw [←hcandidate,←hcp] at hb hbf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config discardSlots (by decide) ClauseCopy.machine
    (cfg discardProgram.start d).heads (cfg discardProgram.start d).tapes _ _ base hb
  rw [discard_place] at hr
  refine ⟨r,hr,hrs.trans hbs,?_⟩
  rw [hrf,hbf,discard_place]
  rfl

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
