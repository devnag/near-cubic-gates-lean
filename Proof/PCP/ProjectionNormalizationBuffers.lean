import Proof.PCP.ProjectionNormalizationClauseCopy

/-! Reusable erased logs for the concrete keep-last body. The candidate is
append-only; its saved cursor is restored without erasing or rescanning it. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace SharedDriverReuse

def capacities (cap : ℕ) : Fin 8 → ℕ := ![0,0,0,0,0,0,cap,cap]
theorem padded_cfg {s : ℕ} (q : Fin s) (candidate source : List Bool) (cp sp : ℕ)
    (eq found : Bool) (cap count driver sourceLog driverLog logCap : ℕ) :
    ZeroPadding.config (capacities logCap)
      (SharedDriverRestore.cfg q candidate source cp sp eq found cap count driver sourceLog driverLog)=
      SharedDriverRestore.cfg q candidate source cp sp eq found cap count driver
        (max logCap sourceLog) (max logCap driverLog) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,capacities,SharedDriverRestore.cfg,Rewind.Workspace.pad_zeros]

theorem scan_run (left : SuffixScan.Clause) (candidatePrefix pre : List Bool) (rows : List SuffixScan.Clause)
    (suffix : List Bool) (eq found : Bool) (cap total pos logCap : ℕ) (hn : pos+rows.length=total)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap)
    (hlog : 2*(rows.length*(2*cap+6)+1)+2 ≤ logCap) :
    ∃ r,runFrom SharedDriverRestore.machine (4*(rows.length*(2*cap+6)+1)+6)
      (SharedDriverRestore.cfg SharedDriverRestore.machine.start
        (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap total (pos+1) logCap logCap)=some r ∧
      r.steps ≤ 4*(rows.length*(2*cap+6)+1)+6 ∧
      r.final=SharedDriverRestore.cfg SharedDriverRestore.finalCode
        (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length (SuffixScan.endEq left rows eq) (SuffixScan.seen left rows found)
        cap total (pos+1) logCap logCap := by
  classical
  obtain ⟨base,sl,dl,hb,hsl,hdl,hbs,hbf⟩ := SharedDriverRestore.scan_run left candidatePrefix pre rows suffix eq found cap total pos hn hcap
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config SharedDriverRestore.machine (capacities logCap) _ _ base hb
  rw [padded_cfg] at hr
  simp only [Nat.max_zero] at hr
  refine ⟨r,hr,hrs.le.trans hbs,?_⟩
  rw [hrf,hbf,padded_cfg,max_eq_left (show sl ≤ logCap by omega),max_eq_left (hdl.trans hlog)]

end SharedDriverReuse
namespace CandidateCopy

noncomputable def machine := CursorRestore.machine ClauseCopy.machine 1
def finalCode : Fin 11 := (1 : Fin 2).natAdd 9
def cfg (q : Fin 11) (source : List Bool) (sp : ℕ) (candidate : List Bool) (cp logCap : ℕ) : Configuration 3 11 :=
  ⟨q,![sp,cp,0],![source,candidate,List.replicate logCap false]⟩

theorem input_eq (source candidate : List Bool) (sp logCap : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities 2 logCap)
      (Rewind.recording (ClauseCopy.cfg ClauseCopy.machine.start source sp candidate) 0)=
      cfg machine.start source sp candidate candidate.length logCap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,Rewind.recording,Rewind.config,ClauseCopy.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,ClauseCopy.cfg,cfg,Fin.addCases,ZeroPadding.pad]

theorem copy_run (pre : List Bool) (fields : SuffixScan.Clause) (suffix candidate : List Bool)
    (logCap : ℕ) (hcap : (ClauseEquality.stream fields).length+2 ≤ logCap) :
    ∃ r,runFrom machine (2*(ClauseEquality.stream fields).length+6)
      (cfg machine.start (pre++ClauseEquality.stream fields++suffix) pre.length candidate candidate.length logCap)=some r ∧
      r.steps ≤ 2*(ClauseEquality.stream fields).length+6 ∧
      r.final=cfg finalCode (pre++ClauseEquality.stream fields++suffix)
        (pre.length+(ClauseEquality.stream fields).length) (candidate++ClauseEquality.stream fields) candidate.length logCap := by
  obtain ⟨source,hs,hsf,hst⟩ := ClauseCopy.copy_run pre fields suffix candidate
  obtain ⟨base,delta,hb,hd,hbs,hbf⟩ := CursorRestore.restore_run ClauseCopy.machine 1 (ClauseCopy.forward 1) _ _ source hs
  rw [hst] at hb hd hbs
  have ht : 2*((ClauseEquality.stream fields).length+2)+2=2*(ClauseEquality.stream fields).length+6 := by omega
  rw [ht] at hb
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config machine (Rewind.Workspace.capacities 2 logCap) _ _ base hb
  rw [input_eq] at hr
  refine ⟨r,hr,by omega,?_⟩
  rw [hrf,hbf,SelectiveReset.padded_finished,max_eq_left (hd.trans hcap),hsf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,ClauseCopy.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,ClauseCopy.cfg,cfg,Fin.addCases]

end CandidateCopy
end NearCubicWires.RepairSource.ProjectionNormalization
