import Proof.PCP.ProjectionNormalizationClause

namespace NearCubicWires.RepairSource.ProjectionNormalization.ProbeReuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev rawSize := 2+((ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size))+2)
abbrev size := rawSize+2
noncomputable def finalCode : Fin size := (1 : Fin 2).natAdd rawSize
def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) : Configuration 5 s :=
  ⟨q,![lp,rp,0,0,0],![left,right,[eq],[found],List.replicate cap false]⟩

theorem input_eq (q : Fin rawSize) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities 4 cap)
      (Rewind.recording (ClauseProbe.cfg q left right lp rp eq found) 0)=
      cfg (q.castAdd 2) left right lp rp eq found cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,Rewind.recording,Rewind.config,ClauseProbe.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,ClauseProbe.cfg,cfg,Fin.addCases,ZeroPadding.pad]

theorem output_eq (left right : List Bool) (lp rp : ℕ) (eq found : Bool) (cap : ℕ) :
    SelectiveReset.finished (s := rawSize) ![lp,rp,0,0] ![left,right,[eq],[found]] cap=
      cfg finalCode left right lp rp eq found cap := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,Fin.addCases]
  · funext i; fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,cfg,Fin.addCases]

theorem probe_run (left right : Fin 3 → List Bool) (candidatePrefix pre tail : List Bool)
    (eq found : Bool) (cap : ℕ) (hcap : ClauseProbe.budget left right ≤ cap) :
    ∃ r,runFrom ClauseProbe.machine (2*ClauseProbe.budget left right+2)
      (cfg ClauseProbe.machine.start (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found cap)=some r ∧
      r.steps ≤ 2*ClauseProbe.budget left right+2 ∧
      r.final=cfg finalCode (candidatePrefix++ClauseEquality.stream left)
        (pre++ClauseEquality.stream right++tail) candidatePrefix.length
        (pre.length+(ClauseEquality.stream right).length) (decide (left=right))
        (found||decide (left=right)) cap := by
  classical
  obtain ⟨base,delta,hb,hd,hs,hf⟩ := ClauseProbe.probe_run left right candidatePrefix pre tail eq found
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config ClauseProbe.machine
    (Rewind.Workspace.capacities 4 cap) _ _ base hb
  rw [input_eq] at hr
  refine ⟨r,hr,by omega,?_⟩
  rw [hrf,hf,SelectiveReset.padded_finished,max_eq_left (hd.trans hcap),output_eq]

end NearCubicWires.RepairSource.ProjectionNormalization.ProbeReuse
