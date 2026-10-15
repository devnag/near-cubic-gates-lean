import Proof.PCP.ProjectionNormalizationForwardRules

namespace NearCubicWires.RepairSource.ProjectionNormalization.ClauseProbe
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (eq found : Bool) : Configuration 4 s :=
  ⟨q,![lp,rp,0,0],![left,right,[eq],[found]]⟩
def boot : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,none,some true,none],fun _ => .stay⟩ else none
def finish : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then some ⟨1,![none,none,none,some (bits 3||bits 2)],fun _ => .stay⟩ else none
def slots : Fin 3 → Fin 4 := ![0,1,2]
noncomputable def compareProgram := RecoveryFocus.machine slots ClauseEquality.machine
noncomputable def tailProgram := Composition.machine compareProgram finish
noncomputable def raw := Composition.machine boot tailProgram
noncomputable def rawFinal := (1 : Fin 2).natAdd (ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size)) |>.natAdd 2
noncomputable def machine := CursorRestore.machine raw 0
def budget (left right : Fin 3 → List Bool) := ClauseEquality.budget left right+4

theorem boot_run (left right : List Bool) (lp rp : ℕ) (eq found : Bool) :
    ∃ r,runFrom boot 1 (cfg 0 left right lp rp eq found)=some r ∧
      r.final=cfg 1 left right lp rp true found ∧ r.steps=1 := by
  have h : step boot (cfg 0 left right lp rp eq found)=some (cfg 1 left right lp rp true found) := by
    simp [step,boot,cfg]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem finish_run (left right : List Bool) (lp rp : ℕ) (eq found : Bool) :
    ∃ r,runFrom finish 1 (cfg 0 left right lp rp eq found)=some r ∧
      r.final=cfg 1 left right lp rp eq (found||eq) ∧ r.steps=1 := by
  have he : readTapeBit [eq] 0=eq := rfl
  have hf : readTapeBit [found] 0=found := rfl
  have h : step finish (cfg 0 left right lp rp eq found)=some (cfg 1 left right lp rp eq (found||eq)) := by
    simp [step,finish,cfg,Configuration.scanned,he,hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem compare_place (oldq q : Fin (ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size)))
    (left right : List Bool) (oldlp oldrp lp rp : ℕ) (oldeq eq found : Bool) :
    RecoveryFocus.config slots (cfg oldq left right oldlp oldrp oldeq found).heads
      (cfg oldq left right oldlp oldrp oldeq found).tapes (ClauseEquality.cfg q left right lp rp eq)=
      cfg q left right lp rp eq found := by
  apply TransitionEvent.focused_eq slots (by decide) (cfg oldq left right oldlp oldrp oldeq found)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl)
  · intro i h; fin_cases i <;> first | rfl | exact False.elim (h 2 rfl)

theorem compare_run (left right : Fin 3 → List Bool) (candidatePrefix pre tail : List Bool) (found : Bool) :
    ∃ r,runFrom compareProgram (ClauseEquality.budget left right)
      (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length true found)=some r ∧
      r.final=cfg ClauseEquality.finalCode (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length)
        (decide (left=right)) found ∧ r.steps=ClauseEquality.budget left right := by
  classical
  obtain ⟨base,hb,hf,hs⟩ := ClauseEquality.clause_run left right candidatePrefix pre [] tail true
  simp only [List.append_nil,Bool.true_and] at hb hf
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slots (by decide) ClauseEquality.machine
    (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length true found).heads
    (cfg compareProgram.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length true found).tapes
    _ _ base hb
  rw [compare_place] at hr
  refine ⟨r,hr,?_,hrs.trans hs⟩
  rw [hrf,hf,compare_place]

theorem raw_run (left right : Fin 3 → List Bool) (candidatePrefix pre tail : List Bool) (eq found : Bool) :
    ∃ r,runFrom raw (budget left right)
      (cfg raw.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found)=some r ∧
      r.final=cfg rawFinal (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length)
        (decide (left=right)) (found||decide (left=right)) ∧ r.steps=budget left right := by
  classical
  obtain ⟨a,ha,haf,hat⟩ := boot_run (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail) candidatePrefix.length pre.length eq found
  obtain ⟨b,hb,hbf,hbt⟩ := compare_run left right candidatePrefix pre tail found
  obtain ⟨c,hc,hcf,hct⟩ := finish_run (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
    (candidatePrefix.length+(ClauseEquality.stream left).length) (pre.length+(ClauseEquality.stream right).length) (decide (left=right)) found
  have hb' : runFrom compareProgram (ClauseEquality.budget left right) (Composition.restart a.final compareProgram.start)=some b := by rw [haf]; exact hb
  have hc' : runFrom finish 1 (Composition.restart b.final finish.start)=some c := by rw [hbf]; exact hc
  have hbc := Composition.run_join compareProgram finish _ _ _ b c hb' hc'
  have he : Composition.leftConfig 2 (Composition.restart a.final compareProgram.start)=
      Composition.restart a.final tailProgram.start := rfl
  rw [he] at hbc
  have hall := Composition.run_join boot tailProgram _ _ _ a (Composition.joinedReceipt b c) ha hbc
  have htime : 1+1+(ClauseEquality.budget left right+1+1)=budget left right := by dsimp [budget]; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt a (Composition.joinedReceipt b c),hall,?_,?_⟩
  · change Composition.rightConfig 2 (Composition.rightConfig _ c.final)=_
    rw [hcf]
    rfl
  · change a.steps+1+(b.steps+1+c.steps)=_
    rw [hat,hbt,hct]
    exact htime

theorem raw_forward (i : Fin 3) : CursorRestore.NoLeft raw (slots i) := by
  have hb : CursorRestore.NoLeft boot (slots i) := by
    intro q bits a ha
    simp only [boot] at ha
    split at ha
    · cases ha; simp
    · contradiction
  have hf : CursorRestore.NoLeft finish (slots i) := by
    intro q bits a ha
    simp only [finish] at ha
    split at ha
    · cases ha; simp
    · contradiction
  exact CursorRestore.composition_forward boot tailProgram (slots i) hb
    (CursorRestore.composition_forward compareProgram finish (slots i)
      (CursorRestore.focus_forward slots (by decide) ClauseEquality.machine i (CursorRestore.clause_forward i)) hf)

theorem probe_run (left right : Fin 3 → List Bool) (candidatePrefix pre tail : List Bool) (eq found : Bool) :
    ∃ r delta,runFrom machine (2*budget left right+2)
      (Rewind.recording (cfg raw.start (candidatePrefix++ClauseEquality.stream left) (pre++ClauseEquality.stream right++tail)
        candidatePrefix.length pre.length eq found) 0)=some r ∧
      delta ≤ budget left right ∧ r.steps=budget left right+delta+2 ∧
      r.final=SelectiveReset.finished (s := 2+((ClauseEquality.size+(ClauseEquality.size+ClauseEquality.size))+2))
        ![candidatePrefix.length,pre.length+(ClauseEquality.stream right).length,0,0]
        ![candidatePrefix++ClauseEquality.stream left,pre++ClauseEquality.stream right++tail,
          [decide (left=right)],[found||decide (left=right)]] delta := by
  classical
  obtain ⟨base,hb,hf,hs⟩ := raw_run left right candidatePrefix pre tail eq found
  obtain ⟨r,delta,hr,hd,ht,hrf⟩ := CursorRestore.restore_run raw 0 (raw_forward 0) _ _ base hb
  rw [hs] at hr hd ht
  refine ⟨r,delta,hr,hd,ht,?_⟩
  rw [hrf,hf]
  congr 1
  funext i; fin_cases i <;> rfl

end NearCubicWires.RepairSource.ProjectionNormalization.ClauseProbe
