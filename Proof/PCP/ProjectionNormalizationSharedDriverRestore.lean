import Proof.PCP.ProjectionNormalizationSharedDriverScan

/-! The later-clause scan restores both cursors of its caller: the original
clause stream and the already advanced outer count driver. No remaining-count
copy, global source rewind, or candidate erasure is performed. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace CursorRestore

theorem stream_forward {t s : ℕ} (p : Machine t s) (driver i : Fin t) (hp : NoLeft p i) :
    NoLeft (StreamController.machine p driver) i := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q=true
    · simp [StreamController.machine,hh] at ha
      subst a; simp [StreamController.jump]
    · cases hr : p.rule q bits with
      | none => simp [StreamController.machine,hh,hr] at ha
      | some b =>
        simp [StreamController.machine,hh,hr] at ha
        subst a
        exact hp q bits b hr
  · simp only [StreamController.machine,Fin.addCases_right] at ha
    split at ha
    · split at ha <;> cases ha <;> simp [StreamController.jump]
    · contradiction

end CursorRestore
namespace SharedDriverRestore

abbrev scanSize := SharedDriverProbe.size+2
abbrev size := scanSize+2+2
noncomputable def sourceReset := CursorRestore.machine SharedDriverScan.machine 1
noncomputable def machine := CursorRestore.machine sourceReset 5
noncomputable def finalCode : Fin size := (1 : Fin 2).natAdd (scanSize+2)
def cfg {s : ℕ} (q : Fin s) (candidate source : List Bool) (cp sp : ℕ)
    (eq found : Bool) (cap count driver sourceLog driverLog : ℕ) : Configuration 8 s :=
  ⟨q,![cp,sp,0,0,0,driver,0,0],![candidate,source,[eq],[found],List.replicate cap false,
    CompareMachine.word count,List.replicate sourceLog false,List.replicate driverLog false]⟩

theorem body_forward (i : Fin 6) (hi : i=1 ∨ i=5) : CursorRestore.NoLeft SharedDriverProbe.machine i := by
  have ha : CursorRestore.NoLeft SharedDriverProbe.advance i := by
    intro q bits a ha
    simp only [SharedDriverProbe.advance] at ha
    split at ha
    · cases ha
      by_cases h : i=5 <;> simp [h]
    · contradiction
  have hp : CursorRestore.NoLeft SharedDriverProbe.probe i := by
    intro q bits a ha
    cases hr : ClauseProbe.machine.rule q (fun j => bits (j.castAdd 1)) with
    | none => simp [SharedDriverProbe.probe,TapeEmbedding.machine,hr] at ha
    | some b =>
      simp [SharedDriverProbe.probe,TapeEmbedding.machine,hr] at ha
      subst a
      rcases hi with hi|hi
      · subst i
        have hf := CursorRestore.other_forward ClauseProbe.raw (0 : Fin 4) 1 (by decide) (ClauseProbe.raw_forward 1)
        simpa [TapeEmbedding.action,Fin.addCases] using hf q (fun j => bits (j.castAdd 1)) b hr
      · subst i
        simp [TapeEmbedding.action,Fin.addCases]
  exact CursorRestore.composition_forward SharedDriverProbe.advance SharedDriverProbe.probe i ha hp

theorem source_forward : CursorRestore.NoLeft SharedDriverScan.machine 1 :=
  CursorRestore.stream_forward SharedDriverProbe.machine 5 1 (body_forward 1 (Or.inl rfl))
theorem driver_forward : CursorRestore.NoLeft sourceReset 5 :=
  CursorRestore.other_forward SharedDriverScan.machine 1 (5 : Fin 6) (by decide)
    (CursorRestore.stream_forward SharedDriverProbe.machine 5 5 (body_forward 5 (Or.inr rfl)))

theorem input_eq (q : Fin scanSize) (candidate source : List Bool) (cp sp : ℕ)
    (eq found : Bool) (cap count driver : ℕ) :
    Rewind.recording (Rewind.recording (SharedDriverProbe.cfg q candidate source cp sp eq found cap count driver) 0) 0=
      cfg (q.castAdd 2 |>.castAdd 2) candidate source cp sp eq found cap count driver 0 0 := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [Rewind.recording,Rewind.config,SharedDriverProbe.cfg,TapeEmbedding.config,ProbeReuse.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;> simp [Rewind.recording,Rewind.config,SharedDriverProbe.cfg,TapeEmbedding.config,ProbeReuse.cfg,cfg,Fin.addCases]

theorem scan_run (left : SuffixScan.Clause) (candidatePrefix pre : List Bool) (rows : List SuffixScan.Clause)
    (suffix : List Bool) (eq found : Bool) (cap total pos : ℕ) (hn : pos+rows.length=total)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap) :
    ∃ r sourceLog driverLog,runFrom machine (4*(rows.length*(2*cap+6)+1)+6)
      (cfg machine.start (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap total (pos+1) 0 0)=some r ∧
      sourceLog ≤ rows.length*(2*cap+6)+1 ∧ driverLog ≤ 2*(rows.length*(2*cap+6)+1)+2 ∧
      r.steps ≤ 4*(rows.length*(2*cap+6)+1)+6 ∧
      r.final=cfg finalCode (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length (SuffixScan.endEq left rows eq) (SuffixScan.seen left rows found)
        cap total (pos+1) sourceLog driverLog := by
  classical
  obtain ⟨base,hb,hbs,hbf⟩ := SharedDriverScan.scan_run left candidatePrefix pre rows suffix eq found cap total pos hn hcap
  obtain ⟨a,sourceLog,ha,hsl,has,haf⟩ := CursorRestore.restore_run SharedDriverScan.machine 1 source_forward _ _ base hb
  obtain ⟨r,driverLog,hr,hdl,hrs,hrf⟩ := CursorRestore.restore_run sourceReset 5 driver_forward _ _ a ha
  change runFrom machine (2*a.steps+2)
    (Rewind.recording (Rewind.recording (SharedDriverProbe.cfg _ _ _ _ _ _ _ _ _ _) 0) 0)=some r at hr
  rw [input_eq] at hr
  have htime : 2*a.steps+2 ≤ 4*(rows.length*(2*cap+6)+1)+6 := by omega
  have hm := runFrom_moreFuel machine _ (4*(rows.length*(2*cap+6)+1)+6-(2*a.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,sourceLog,driverLog,hm,by omega,by omega,by omega,?_⟩
  rw [hrf,haf,hbf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,Rewind.recording,SharedDriverScan.cfg,SharedDriverProbe.cfg,
        TapeEmbedding.config,ProbeReuse.cfg,cfg,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,SharedDriverScan.cfg,SharedDriverProbe.cfg,
        TapeEmbedding.config,ProbeReuse.cfg,cfg,Fin.addCases]

end SharedDriverRestore
end NearCubicWires.RepairSource.ProjectionNormalization
