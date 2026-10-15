import Proof.MachineModel.Basic

/-! P25: copy one framed native word from the stream cursor onto a fresh
destination tape, verbatim, then pay the return of the destination head by
erasing one unary marker per copied byte. The stream head advances past the
frame and nothing else on the stream changes. Tapes: 0 stream, 1 destination,
2 marker counter. States: 0 mark/end, 1 payload, 2 enter rewind, 3 rewind, 4 halt. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace FrameCopy

def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, ![none, some true, some true], ![.right, .right, .right]⟩
      else ⟨2, ![none, some false, some true], ![.right, .right, .right]⟩)
    else if q.val = 1 then some ⟨0, ![none, some (bits 0), some true], ![.right, .right, .right]⟩
    else if q.val = 2 then some ⟨3, fun _ => none, ![.stay, .stay, .left]⟩
    else if q.val = 3 then some (if bits 2 then ⟨3, ![none, none, some false], ![.stay, .left, .left]⟩
      else ⟨4, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (q : Fin 5) (input : List Bool) (ih : ℕ) (dest : List Bool) (dh : ℕ)
    (counter : List Bool) (kh : ℕ) : Configuration 3 5 :=
  ⟨q, ![ih, dh, kh], ![input, dest, counter]⟩

@[simp] theorem halted_four : machine.halted 4 = true := rfl

/-- During the copy the destination and the counter have the same length as the
number of copied bytes and both heads sit at their ends. -/
def copying (q : Fin 5) (input : List Bool) (ih : ℕ) (dest : List Bool) : Configuration 3 5 :=
  cfg q input ih dest dest.length (List.replicate dest.length true) dest.length

theorem mark_step (input : List Bool) (ih : ℕ) (dest : List Bool) (h : readTapeBit input ih = true) :
    step machine (copying 0 input ih dest) = some (copying 1 input (ih+1) (dest ++ [true])) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

theorem bit_step (input : List Bool) (ih : ℕ) (dest : List Bool) :
    step machine (copying 1 input ih dest) = some (copying 0 input (ih+1) (dest ++ [readTapeBit input ih])) := by
  simp [step, machine, copying, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

theorem end_step (input : List Bool) (ih : ℕ) (dest : List Bool) (h : readTapeBit input ih = false) :
    step machine (copying 0 input ih dest) = some (copying 2 input (ih+1) (dest ++ [false])) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

theorem copy_timed (pre w rest dest : List Bool) :
    Timed machine (frame w).length (copying 0 (pre ++ frame w ++ rest) pre.length dest)
      (copying 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (dest ++ frame w)) := by
  induction w generalizing pre dest with
  | nil =>
    have h := Timed.single (p := machine) (by rfl)
      (end_step (pre ++ frame [] ++ rest) pre.length dest (by rw [read_start pre _ rest (frame_pos [])]; rfl))
    simpa [frame_nil] using h
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have hb : readTapeBit (pre ++ frame (b :: w) ++ rest) (pre.length+1) = b := by
      have h := read_shift pre (frame (b :: w)) rest 1 (by simp [frame_cons])
      rw [h]; rfl
    have s1 := Timed.single (p := machine) (by rfl)
      (mark_step (pre ++ frame (b :: w) ++ rest) pre.length dest (by rw [read_start pre _ rest (frame_pos _)]; rfl))
    have s2 := Timed.single (p := machine) (by rfl)
      (bit_step (pre ++ frame (b :: w) ++ rest) (pre.length+1) (dest ++ [true]))
    rw [hb] at s2
    have s3 := ih (pre ++ [true, b]) (dest ++ [true, b])
    rw [← hw] at s3
    have hl : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    rw [hl] at s3
    have e3 : dest ++ [true] ++ [b] = dest ++ [true, b] := by simp
    rw [e3] at s2
    have h := (s1.trans s2).trans s3
    have e1 : 1 + 1 + (frame w).length = (frame (b :: w)).length := by
      simp only [frame_length', List.length_cons]; omega
    have e2 : pre.length + 1 + 1 + (frame w).length = pre.length + (frame (b :: w)).length := by
      simp only [frame_length', List.length_cons]; omega
    have e4 : dest ++ [true, b] ++ frame w = dest ++ frame (b :: w) := by simp [frame_cons]
    rw [e4, e1, e2] at h
    exact h

/-! ## Return of the destination head, driven by the markers -/

theorem enter_step (input : List Bool) (ih : ℕ) (dest : List Bool) (k : ℕ) :
    step machine (cfg 2 input ih dest (k+1) (List.replicate (k+1) true) (k+1)) =
      some (cfg 3 input ih dest (k+1) (List.replicate (k+1) true) k) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_step (input : List Bool) (ih : ℕ) (dest : List Bool) (k z : ℕ) :
    step machine (cfg 3 input ih dest (k+1) (List.replicate (k+1) true ++ List.replicate z false) k) =
      some (cfg 3 input ih dest k (List.replicate k true ++ List.replicate (z+1) false) (k-1)) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.erase_counter]

theorem stop_step (input : List Bool) (ih : ℕ) (dest : List Bool) (z : ℕ) :
    step machine (cfg 3 input ih dest 0 (List.replicate z false) 0) =
      some (cfg 4 input ih dest 0 (List.replicate z false) 0) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem back_timed (input : List Bool) (ih : ℕ) (dest : List Bool) (k z : ℕ) :
    Timed machine (k+1) (cfg 3 input ih dest (k+1) (List.replicate (k+1) true ++ List.replicate z false) k)
      (cfg 3 input ih dest 0 (List.replicate (k+1+z) false) 0) := by
  induction k generalizing z with
  | zero =>
    have h := Timed.single (p := machine) (by rfl) (back_step input ih dest 0 z)
    have e : 0+1+z = z+1 := by omega
    rw [e]
    simpa using h
  | succ k ihk =>
    have h1 := back_step input ih dest (k+1) z
    rw [Nat.add_sub_cancel] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ihk (z+1))
    have e : k+1+(z+1) = k+1+1+z := by omega
    rw [e] at h
    have e2 : 1 + (k+1) = k+1+1 := by omega
    rw [e2] at h; exact h

theorem rewind_timed (input : List Bool) (ih : ℕ) (dest : List Bool) (k : ℕ) :
    Timed machine (k+3) (cfg 2 input ih dest (k+1) (List.replicate (k+1) true) (k+1))
      (cfg 4 input ih dest 0 (List.replicate (k+1) false) 0) := by
  have s1 := Timed.single (p := machine) (by rfl) (enter_step input ih dest k)
  have s2 := back_timed input ih dest k 0
  simp only [List.replicate_zero, List.append_nil, Nat.add_zero] at s2
  have s3 := Timed.single (p := machine) (by rfl) (stop_step input ih dest (k+1))
  have h := (s1.trans s2).trans s3
  have e : 1 + (k+1) + 1 = k+3 := by omega
  rw [e] at h; exact h

/-- The complete framed copy: exactly `2·|frame w| + 2` paid transitions. -/
theorem copy_run (pre w rest : List Bool) :
    ∃ r : ExecutionReceipt 3 5,
      runFrom machine (2*(frame w).length+2) (cfg 0 (pre ++ frame w ++ rest) pre.length [] 0 [] 0) = some r ∧
      r.final = cfg 4 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (frame w) 0
        (List.replicate (frame w).length false) 0 ∧
      r.steps = 2*(frame w).length+2 := by
  have hc := copy_timed pre w rest []
  simp only [List.nil_append] at hc
  obtain ⟨k, hk⟩ : ∃ k, (frame w).length = k+1 := ⟨(frame w).length - 1, by have := frame_pos w; omega⟩
  have hr := rewind_timed (pre ++ frame w ++ rest) (pre.length + (frame w).length) (frame w) k
  have hstart : copying 0 (pre ++ frame w ++ rest) pre.length [] =
      cfg 0 (pre ++ frame w ++ rest) pre.length [] 0 [] 0 := rfl
  have hmid : copying 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (frame w) =
      cfg 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (frame w) (k+1)
        (List.replicate (k+1) true) (k+1) := by
    simp only [copying, hk]
  rw [hstart, hmid] at hc
  have h := hc.trans hr
  rw [← hk] at h
  have e : (frame w).length + (k+3) = 2*(frame w).length+2 := by omega
  rw [e] at h
  exact h.run rfl

end FrameCopy

end NearCubicWires.ExtDecompositionBatch
