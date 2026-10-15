import Proof.Hierarchy.CompetitorRecordScalarBounds

/-! A single paid saturating rewind of the appended record stream. The raw
capacity comes from scalar metadata; the scan logs and restores its driver.
No record bit is changed, including the empty-stream case. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRecordRewind
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 3) (source : List Bool) (pos C driver logHead : ℕ) (log : List Bool) :
    Configuration 3 3 := ⟨q,![pos,driver,logHead],![source,List.replicate C true,log]⟩
def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then
    some (if scan 1 then ⟨0,![none,none,some true],![.left,.right,.right]⟩
      else ⟨1,fun _=>none,![.stay,.stay,.left]⟩)
    else if q.val=1 then some (if scan 2 then
      ⟨1,![none,none,some false],![.stay,.left,.left]⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩) else none

theorem forward_step (source : List Bool) (pos C done : ℕ) (hd : done < C) :
    step machine (cfg 0 source (pos-done) C done done (List.replicate done true))=
      some (cfg 0 source (pos-(done+1)) C (done+1) (done+1) (List.replicate (done+1) true)) := by
  simp [step,machine,cfg,Configuration.scanned,readTapeBit,List.getD,hd]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.sub_sub]
  · funext i;fin_cases i <;> simp only [applyAction]
    · rfl
    · rfl
    · change writeTapeBit (List.replicate done true) done true=List.replicate (done+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate done true) true

theorem bridge_step (source : List Bool) (pos C : ℕ) :
    step machine (cfg 0 source (pos-C) C C C (List.replicate C true))=
      some (cfg 1 source (pos-C) C C (C-1) (List.replicate C true)) := by
  simp [step,machine,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem back_step (source : List Bool) (pos C n z : ℕ) :
    step machine (cfg 1 source pos C (n+1) n (List.replicate (n+1) true++List.replicate z false))=
      some (cfg 1 source pos C n (n-1) (List.replicate n true++List.replicate (z+1) false)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.erase_counter]

theorem stop_step (source : List Bool) (pos C z : ℕ) :
    step machine (cfg 1 source pos C 0 0 (List.replicate z false))=
      some (cfg 2 source pos C 0 0 (List.replicate z false)) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem forward_timed (source : List Bool) (pos C remaining done : ℕ) (h : done+remaining=C) :
    Timed machine (remaining+1)
      (cfg 0 source (pos-done) C done done (List.replicate done true))
      (cfg 1 source (pos-C) C C (C-1) (List.replicate C true)) := by
  induction remaining generalizing done with
  | zero =>
    have he : done=C := by omega
    subst done
    exact Timed.single (by rfl) (bridge_step source pos C)
  | succ remaining ih =>
    exact Timed.step (by rfl) (forward_step source pos C done (by omega))
      (ih (done+1) (by omega))

theorem back_timed (source : List Bool) (pos C n z : ℕ) :
    Timed machine (n+1)
      (cfg 1 source pos C n (n-1) (List.replicate n true++List.replicate z false))
      (cfg 2 source pos C 0 0 (List.replicate (n+z) false)) := by
  induction n generalizing z with
  | zero => simpa using Timed.single (by rfl) (stop_step source pos C z)
  | succ n ih =>
    have h := Timed.step (by rfl) (back_step source pos C n z) (ih (z+1))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_sub_cancel] using h

theorem rewind_run (source : List Bool) (C pos : ℕ) (hpos : pos ≤ C) :
    ∃ actual,runFrom machine (2*C+2) (cfg 0 source pos C 0 0 [])=some actual ∧
      actual.final=cfg 2 source 0 C 0 0 (List.replicate C false) ∧ actual.steps=2*C+2 := by
  have hf := forward_timed source pos C C 0 (by omega)
  have hb := back_timed source (pos-C) C C 0
  simp only [Nat.sub_zero,Nat.add_zero,List.replicate_zero,List.append_nil] at hf hb
  have h := hf.trans hb
  rw [Nat.sub_eq_zero_of_le hpos] at h
  have he : C+1+(C+1)=2*C+2 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.CompetitorRecordRewind
