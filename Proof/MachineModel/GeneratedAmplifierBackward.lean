import Proof.MachineModel.GeneratedAmplifierSemantics

/-! Locate the last framed address from the physically retained input end.
The actual unary arity drives exactly 2*n+1 backward moves and is restored. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Backward
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then some ⟨1,fun _ => none,![.left,.stay]⟩
    else if q.val=1 then some (if bits 1 then ⟨2,fun _ => none,![.left,.right]⟩
      else ⟨3,fun _ => none,fun _ => .stay⟩)
    else if q.val=2 then some ⟨1,fun _ => none,![.left,.stay]⟩ else none
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (n pos head : ℕ) : Configuration 2 s :=
  ⟨q,![pos,head],![source,UnaryTemplate.tape n]⟩

theorem start_step (source : List Bool) (n pos : ℕ) :
    step raw (cfg 0 source n (pos+1) 1)=some (cfg 1 source n pos 1) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem mark_step (source : List Bool) (n pos k : ℕ) (hk : k<n) :
    step raw (cfg 1 source n (pos+1) (k+1))=some (cfg 2 source n pos (k+2)) := by
  simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark n k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem second_step (source : List Bool) (n pos head : ℕ) :
    step raw (cfg 2 source n (pos+1) head)=some (cfg 1 source n pos head) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (source : List Bool) (n pos : ℕ) :
    step raw (cfg 1 source n pos (n+1))=some (cfg 3 source n pos (n+1)) := by
  simp [step,raw,cfg,Configuration.scanned]
  rfl

theorem scan_timed (source : List Bool) (n pos k remaining : ℕ) (he : k+remaining=n) :
    Timed raw (2*remaining+1) (cfg 1 source n (pos+2*remaining) (k+1)) (cfg 3 source n pos (n+1)) := by
  induction remaining generalizing k with
  | zero =>
    have hk : k=n := by omega
    subst k
    simpa using Timed.single (by rfl) (stop_step source n pos)
  | succ remaining ih =>
    have hm := mark_step source n (pos+2*remaining+1) k (by omega)
    have hs := second_step source n (pos+2*remaining) (k+2)
    have ht := ih (k+1) (by omega)
    have h := (Timed.single (by rfl : raw.halted (1 : Fin 4)=false) hm).trans
      ((Timed.single (by rfl : raw.halted (2 : Fin 4)=false) hs).trans ht)
    have htime : 1+(1+(2*remaining+1))=2*(remaining+1)+1 := by omega
    have hpos : pos+2*remaining+1+1=pos+2*(remaining+1) := by omega
    rw [htime,hpos] at h
    exact h

def slot : Fin 1→Fin 2 := fun _ => 1
noncomputable def reset := RecoveryFocus.machine slot UnaryTemplate.machine
noncomputable def machine := Composition.machine raw reset

theorem backward_run (source : List Bool) (n pos : ℕ) :
    ∃ r,runFrom machine (3*n+5) (cfg 0 source n (pos+2*n+1) 1)=some r ∧
      r.final=cfg 6 source n pos 1 ∧ r.steps=3*n+5 := by
  have ht := (Timed.single (by rfl : raw.halted (0 : Fin 4)=false) (start_step source n (pos+2*n))).trans
    (scan_timed source n pos 0 n (by omega))
  have htime : 1+(2*n+1)=2*n+2 := by omega
  rw [htime] at ht
  obtain ⟨base,hb,hf,hs⟩ := ht.run (by rfl)
  obtain ⟨last,hl,hlf,hls,_⟩ := UnaryTemplate.reset_run n
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slot (by decide) UnaryTemplate.machine
    base.final.heads base.final.tapes _ _ last hl
  have hi : RecoveryFocus.config slot base.final.heads base.final.tapes
      (UnaryTemplate.config 0 (UnaryTemplate.tape n) (n+1))=Composition.restart base.final reset.start := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot,RecoveryFocus.pick,
        cfg,UnaryTemplate.config,Composition.restart]
    · funext i; fin_cases i <;> simp [RecoveryFocus.config,slot,RecoveryFocus.pick,
        cfg,UnaryTemplate.config,Composition.restart]
  rw [hi] at hfocus
  have hj := Composition.run_join raw reset (2*n+2) (n+2) _ base focused hb hfocus
  have hn : (2*n+2)+1+(n+2)=3*n+5 := by omega
  rw [hn] at hj
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_⟩
  · change Composition.rightConfig 4 focused.final=_
    rw [hff,hlf,hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,slot,RecoveryFocus.pick,
        cfg,UnaryTemplate.config]
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,slot,RecoveryFocus.pick,
        cfg,UnaryTemplate.config]
  · change base.steps+1+focused.steps=_
    rw [hs,hfs,hls]
    exact hn

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Backward
