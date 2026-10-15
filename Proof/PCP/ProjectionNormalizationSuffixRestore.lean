import Proof.PCP.ProjectionNormalizationSuffixScan

/-! One paid original-source restoration around the whole later-clause scan.
The source starts at the position immediately following the candidate and
returns to precisely that position; it is never rewound to the global origin. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace CursorRestore

theorem other_forward {t s : ℕ} (p : Machine t s) (target i : Fin t) (hi : i≠target)
    (hp : NoLeft p i) : NoLeft (machine p target) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q=true
    · simp [machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [machine,hh,hr] at ha
      | some b =>
        simp [machine,hh,hr] at ha
        subst a
        simpa only [recordAction,Fin.addCases_left] using hp q (fun j => bits (j.castAdd 1)) b hr
  · simp only [machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha
        simp [MaskedReset.rewindAction,hi]
      · cases ha
        simp [Rewind.finishAction]
    · contradiction

theorem repeat_forward {t s : ℕ} (p : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (i : Fin t) (hp : NoLeft p i) :
    NoLeft (RepeatMachine.machine p accepted) (i.castAdd 1) := by
  intro state bits a ha
  cases hs : (RepeatMachine.code s).symm state with
  | inl q =>
    simp only [RepeatMachine.machine,hs] at ha
    split at ha
    · cases ha
      simp [RepeatMachine.action]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [hr] at ha
      | some b =>
        simp only [hr,Option.map_some,Option.some.injEq] at ha
        subst a
        simpa only [RepeatMachine.bodyAction,Fin.addCases_left] using hp q (fun j => bits (j.castAdd 1)) b hr
  | inr q =>
    simp only [RepeatMachine.machine,hs] at ha
    split at ha
    · split at ha <;> cases ha <;> simp [RepeatMachine.action]
    · split at ha
      · cases ha; simp [RepeatMachine.action]
      · split at ha
        · split at ha <;> cases ha <;> simp [RepeatMachine.action]
        · contradiction

end CursorRestore
namespace SuffixRestore

noncomputable def machine := CursorRestore.machine SuffixScan.machine 1
noncomputable def ending (candidate source : List Bool) (candidatePos sourcePos : ℕ)
    (eq found : Bool) (cap count log : ℕ) :=
  SelectiveReset.finished (s := Fintype.card (RepeatMachine.Control ProbeReuse.size))
    (SuffixScan.cfg 3 candidate source candidatePos sourcePos eq found cap count 1).heads
    (SuffixScan.cfg 3 candidate source candidatePos sourcePos eq found cap count 1).tapes log

theorem source_forward : CursorRestore.NoLeft SuffixScan.machine 1 := by
  have hp := CursorRestore.other_forward ClauseProbe.raw (0 : Fin 4) 1 (by decide) (ClauseProbe.raw_forward 1)
  exact CursorRestore.repeat_forward ClauseProbe.machine (fun _ _ => true) (1 : Fin 5) hp

theorem scan_run (left : SuffixScan.Clause) (candidatePrefix pre : List Bool) (rows : List SuffixScan.Clause)
    (suffix : List Bool) (eq found : Bool) (cap : ℕ)
    (hcap : ∀ row∈rows,ClauseProbe.budget left row ≤ cap) :
    ∃ r log,runFrom machine (2*(rows.length*(2*cap+5)+3)+2)
      (Rewind.recording (SuffixScan.cfg 0 (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length eq found cap rows.length 1) 0)=some r ∧
      log ≤ rows.length*(2*cap+5)+3 ∧ r.steps ≤ 2*(rows.length*(2*cap+5)+3)+2 ∧
      r.final=ending (candidatePrefix++ClauseEquality.stream left) (pre++SuffixScan.stream rows++suffix)
        candidatePrefix.length pre.length (SuffixScan.endEq left rows eq) (SuffixScan.seen left rows found)
        cap rows.length log := by
  classical
  obtain ⟨base,hb,hbs,hbf⟩ := SuffixScan.scan_run left candidatePrefix pre rows suffix eq found cap hcap
  obtain ⟨r,log,hr,hl,hrs,hf⟩ := CursorRestore.restore_run SuffixScan.machine 1 source_forward _ _ base hb
  have htime : 2*base.steps+2 ≤ 2*(rows.length*(2*cap+5)+3)+2 := by omega
  have hm := runFrom_moreFuel machine _ (2*(rows.length*(2*cap+5)+3)+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,log,hm,by omega,by omega,?_⟩
  rw [hf,hbf]
  unfold ending
  congr 1
  funext i
  fin_cases i <;>
    simp [SuffixScan.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ProbeReuse.cfg,Fin.addCases]

end SuffixRestore
end NearCubicWires.RepairSource.ProjectionNormalization
