import Proof.Supplier.RowMaskPositionParts

/-! Erase the occurrence-index template using the retained mask-length
template. Both heads return to one and no fresh reset allocation is needed. -/
namespace NearCubicWires.RepairOrdinary.RowMaskIndexClear
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q bits=>if q.val=0 then some (if bits 1 then
    ⟨0,![some false,none],fun _=>.right⟩ else ⟨1,fun _=>none,fun _=>.left⟩)
    else if q.val=1 then some (if bits 1 then
      ⟨1,fun _=>none,fun _=>.left⟩ else ⟨2,fun _=>none,fun _=>.right⟩) else none

def cfg (q : Fin 3) (source : List Bool) (N pos : ℕ) : Configuration 2 3 :=
  ⟨q,fun _=>pos,![source,UnaryTemplate.tape N]⟩

theorem forward_step (pre tail : List Bool) (N : ℕ)
    (hm : readTapeBit (UnaryTemplate.tape N) pre.length=true) :
    step machine (cfg 0 (pre++true::tail) N pre.length)=
      some (cfg 0 (pre++false::tail) N (pre.length+1)) := by
  simp [step,machine,cfg,Configuration.scanned,hm]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i
    · exact BinaryIncrement.write_prefix pre tail true false
    · rfl

theorem forward (processed remaining N : ℕ) (hn : processed+remaining=N) :
    Timed machine remaining
      (cfg 0 (List.replicate (processed+1) false++List.replicate remaining true++[false]) N (processed+1))
      (cfg 0 (List.replicate (N+2) false) N (N+1)) := by
  induction remaining generalizing processed with
  | zero =>
    have he : processed=N := by omega
    subst processed
    simpa [List.replicate_add,Nat.add_assoc] using
      Timed.refl machine (cfg 0 (List.replicate (N+2) false) N (N+1))
  | succ remaining ih =>
    have hs := forward_step (List.replicate (processed+1) false) (List.replicate remaining true++[false]) N
      (by simpa using UnaryTemplate.tape_mark N processed (by omega))
    have hp : List.replicate (processed+1) false++false::(List.replicate remaining true++[false])=
        List.replicate (processed+1+1) false++List.replicate remaining true++[false] := by
      simp [List.replicate_add,List.append_assoc]
    simp only [List.length_replicate,hp] at hs
    have h := (Timed.single (by rfl) hs).trans (ih (processed+1) (by omega))
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm] using h

theorem back_step (source : List Bool) (N j : ℕ) (hj : j<N) :
    step machine (cfg 1 source N (j+1))=some (cfg 1 source N j) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark N j hj]
  rfl

theorem back (source : List Bool) (N j : ℕ) (hj : j≤N) :
    Timed machine (j+1) (cfg 1 source N j) (cfg 2 source N 1) := by
  induction j with
  | zero =>
    apply Timed.single (by rfl)
    simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape]
    rfl
  | succ j ih =>
    simpa only [Nat.add_comm 1 (j+1)] using
      (Timed.single (by rfl) (back_step source N j (by omega))).trans (ih (by omega))

theorem clear_run (N : ℕ) :
    ∃ r,runFrom machine (2*N+2) (cfg 0 (UnaryTemplate.tape N) N 1)=some r ∧
      r.final=cfg 2 (List.replicate (N+2) false) N 1 ∧ r.steps=2*N+2 := by
  have hf := forward 0 N N (by omega)
  have hs : step machine (cfg 0 (List.replicate (N+2) false) N (N+1))=
      some (cfg 1 (List.replicate (N+2) false) N N) := by
    simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_end]
    rfl
  have h := (hf.trans (Timed.single (by rfl) hs)).trans (back (List.replicate (N+2) false) N N (by omega))
  have he : N+1+(N+1)=2*N+2 := by omega
  rw [he] at h
  simpa [UnaryTemplate.tape] using h.run (by rfl)

end NearCubicWires.RepairOrdinary.RowMaskIndexClear
