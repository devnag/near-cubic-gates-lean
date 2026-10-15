import Proof.MachineModel.OrdinaryWilliamsPreparation

/-! Actual cursor positioning past a raw natWord header, driven by its
physical unary width. The header and width are preserved; the width head
is restored to one, while the source retains its streaming endpoint. -/
namespace NearCubicWires.RepairOrdinary.MatrixNaturalCursor
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scan : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then some ⟨1,fun _ => none,![.stay,.right]⟩
    else if q.val=1 then
      if bits 1 then some ⟨2,fun _ => none,![.right,.right]⟩
      else some ⟨3,fun _ => none,![.right,.stay]⟩
    else if q.val=2 then some ⟨1,fun _ => none,![.right,.stay]⟩ else none
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (w pos head : ℕ) : Configuration 2 s :=
  ⟨q,![pos,head],![source,UnaryTemplate.tape w]⟩

theorem start_step (source : List Bool) (w pos : ℕ) :
    step scan (cfg 0 source w pos 0)=some (cfg 1 source w pos 1) := by
  simp [step,scan,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem mark_step (source : List Bool) (w pos k : ℕ) (hk : k < w) :
    step scan (cfg 1 source w pos (k+1))=some (cfg 2 source w (pos+1) (k+2)) := by
  simp [step,scan,cfg,Configuration.scanned,UnaryTemplate.tape_mark w k hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction]

theorem second_step (source : List Bool) (w pos head : ℕ) :
    step scan (cfg 2 source w pos head)=some (cfg 1 source w (pos+1) head) := by
  simp [step,scan,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem stop_step (source : List Bool) (w pos : ℕ) :
    step scan (cfg 1 source w pos (w+1))=some (cfg 3 source w (pos+1) (w+1)) := by
  simp [step,scan,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem scan_timed (source : List Bool) (w pos k rem : ℕ) (he : k+rem=w) :
    Timed scan (2*rem+1) (cfg 1 source w pos (k+1)) (cfg 3 source w (pos+2*rem+1) (w+1)) := by
  induction rem generalizing pos k with
  | zero =>
    have hk : k=w := by omega
    subst k
    simpa using Timed.single (by rfl) (stop_step source w pos)
  | succ rem ih =>
    have ht := (Timed.single (by rfl) (mark_step source w pos k (by omega))).trans
      (Timed.single (by rfl) (second_step source w (pos+1) (k+2)))
    have hn := ih (pos+2) (k+1) (by omega)
    have hall := ht.trans (by simpa [Nat.add_assoc] using hn)
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem scan_run (source : List Bool) (w pos : ℕ) :
    ∃ r : ExecutionReceipt 2 4,
      runFrom scan (2*w+2) (cfg 0 source w pos 0)=some r ∧
      r.final=cfg 3 source w (pos+2*w+1) (w+1) ∧ r.steps=2*w+2 := by
  have ht := (Timed.single (by rfl) (start_step source w pos)).trans (scan_timed source w pos 0 w (by omega))
  have htime : 1+(2*w+1)=2*w+2 := by omega
  rw [htime] at ht
  exact ht.run (by rfl)

def slots : Fin 1 → Fin 2 := fun _ => 1
noncomputable def reset := RecoveryFocus.machine slots UnaryTemplate.machine
noncomputable def machine := Composition.machine scan reset

theorem cursor_run (source : List Bool) (w pos : ℕ) :
    ∃ r : ExecutionReceipt 2 7,
      runFrom machine (3*w+5) (cfg 0 source w pos 0)=some r ∧
      r.final=cfg 6 source w (pos+2*w+1) 1 ∧ r.steps=3*w+5 := by
  obtain ⟨base,hb,hf,hs⟩ := scan_run source w pos
  obtain ⟨last,hl,hlf,hls,_⟩ := UnaryTemplate.reset_run w
  have hi : RecoveryFocus.config slots base.final.heads base.final.tapes
      (UnaryTemplate.config 0 (UnaryTemplate.tape w) (w+1)) = Composition.restart base.final reset.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [hf]; rfl
    · intro i; rw [hf]; rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) UnaryTemplate.machine
    base.final.heads base.final.tapes _ _ last hl
  rw [hi] at hfocus
  have hj := Composition.run_join scan reset (2*w+2) (w+2) _ base focused hb hfocus
  have htime : (2*w+2)+1+(w+2)=3*w+5 := by omega
  rw [htime] at hj
  have hin : Composition.leftConfig 3 (cfg (s:=4) 0 source w pos 0)=cfg (s:=7) 0 source w pos 0 := rfl
  rw [hin] at hj
  have hp0 : RecoveryFocus.pick slots (0 : Fin 2)=none := by decide
  have hp1 : RecoveryFocus.pick slots (1 : Fin 2)=some (0 : Fin 1) := RecoveryFocus.pick_slot slots (by decide) 0
  refine ⟨Composition.joinedReceipt base focused,hj,?_,?_⟩
  · change Composition.rightConfig 4 focused.final=_
    rw [hff,hlf,hf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hp0,hp1,UnaryTemplate.config,cfg]
    · funext i; fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hp0,hp1,UnaryTemplate.config,cfg]
  · change base.steps+1+focused.steps=_
    rw [hs,hfs,hls]
    exact htime

end NearCubicWires.RepairOrdinary.MatrixNaturalCursor
