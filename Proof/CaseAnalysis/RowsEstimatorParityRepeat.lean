import Proof.CaseAnalysis.RowsEstimatorParityNatural

/-! Repeated fixed byte blocks can resume at an actual partially consumed unary driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Repeat
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding Glyph
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copies {t : ℕ} (fs : List (Stroke t)) (b : Bool) (n : ℕ) (i : Fin t):=
  (List.replicate n (word fs b i)).flatten
noncomputable def machine {t : ℕ} (fs : List (Stroke t)):=CloseoutRowsDegreeLoop.machine (Glyph.machine fs)

theorem remaining {t : ℕ} (fs : List (Stroke t)) (b : Bool) (source : List Bool) (pos Q : ℕ)
    (hb:readTapeBit source pos=b) (j n : ℕ) (out : Fin t→List Bool) (hn:j+n=Q) :
    ∃ time≤n*(2*fs.length+2)+Q+3,Timed (machine fs) time
      (RepeatMachine.cfg 0 (cfg (Glyph.machine fs).start source pos out) Q (j+1))
      (RepeatMachine.cfg 3 (cfg (Glyph.machine fs).start source pos (fun i=>out i++copies fs b n i)) Q 1) := by
  induction n generalizing j out with
  | zero=>
    have hj:j=Q:=by omega
    subst j
    refine ⟨Q+3,by simp,?_⟩
    simpa only [machine,CloseoutRowsDegreeLoop.machine,copies,List.replicate_zero,List.flatten_nil,List.append_nil] using
      RepeatMachine.exhaust (Glyph.machine fs) (fun _ _=>true) (cfg (Glyph.machine fs).start source pos out) Q
  | succ n ih=>
    obtain ⟨r,hr,rh,rt,rs⟩:=word_run fs b source pos out hb
    have hstep:=RepeatMachine.iteration (Glyph.machine fs) (fun _ _=>true)
      (cfg (Glyph.machine fs).start source pos out) Q j r rfl (by omega) hr
    simp only [↓reduceIte] at hstep
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (cfg (Glyph.machine fs).start source pos (fun i=>out i++word fs b i)) Q (j+2) rh rt] at hstep
    obtain ⟨time,ht,tail⟩:=ih (j+1) (fun i=>out i++word fs b i) (by omega)
    rw [show j+1+1=j+2 by omega] at tail
    have whole:=hstep.trans tail
    refine ⟨r.steps+2+time,by nlinarith,?_⟩
    have he:(fun i=>(out i++word fs b i)++copies fs b n i)=(fun i=>out i++copies fs b (n+1) i):=by
      funext i
      simp [copies,List.replicate_succ,List.append_assoc]
    rw [he] at whole
    exact whole

theorem repeat_run {t : ℕ} (fs : List (Stroke t)) (b : Bool) (source : List Bool) (pos Q j n : ℕ)
    (out : Fin t→List Bool) (hb:readTapeBit source pos=b) (hn:j+n=Q) : ∃ r,
    runFrom (machine fs) (n*(2*fs.length+2)+Q+3)
      (RepeatMachine.cfg 0 (cfg (Glyph.machine fs).start source pos out) Q (j+1))=some r ∧
      r.final=RepeatMachine.cfg 3 (cfg (Glyph.machine fs).start source pos (fun i=>out i++copies fs b n i)) Q 1 ∧
      r.steps≤n*(2*fs.length+2)+Q+3 := by
  obtain ⟨time,ht,run⟩:=remaining fs b source pos Q hb j n out hn
  obtain ⟨r,hr,rf,rs⟩:=run.run (by
    simp [machine,CloseoutRowsDegreeLoop.machine,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more:=runFrom_moreFuel (machine fs) time (n*(2*fs.length+2)+Q+3-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,rf,rs.le.trans ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Repeat
