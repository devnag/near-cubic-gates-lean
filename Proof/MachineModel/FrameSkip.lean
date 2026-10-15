import Proof.MachineModel.Basic

/-! P25: traverse one framed field in place. `skip` only moves the stream head
past `frame w`; `skipMark` additionally appends one marker per scanned byte to
a measure tape, so the frame region's exact byte count is physically recorded. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace FrameSkip

/-- States: 0 read mark, 1 skip payload bit, 2 halt. -/
def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, fun _ => .right⟩
      else ⟨2, fun _ => none, fun _ => .right⟩)
    else if q.val = 1 then some ⟨0, fun _ => none, fun _ => .right⟩
    else none

def cfg (q : Fin 3) (input : List Bool) (ih : ℕ) : Configuration 1 3 := ⟨q, fun _ => ih, fun _ => input⟩

@[simp] theorem halted_two : machine.halted 2 = true := rfl

theorem mark_step (input : List Bool) (ih : ℕ) (h : readTapeBit input ih = true) :
    step machine (cfg 0 input ih) = some (cfg 1 input (ih+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem end_step (input : List Bool) (ih : ℕ) (h : readTapeBit input ih = false) :
    step machine (cfg 0 input ih) = some (cfg 2 input (ih+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem bit_step (input : List Bool) (ih : ℕ) :
    step machine (cfg 1 input ih) = some (cfg 0 input (ih+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction, HeadMove.apply]
  · rfl

theorem skip_timed (pre w rest : List Bool) :
    Timed machine (2*w.length+1) (cfg 0 (pre ++ frame w ++ rest) pre.length)
      (cfg 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length)) := by
  induction w generalizing pre with
  | nil =>
    have h := Timed.single (p := machine) (by rfl)
      (end_step (pre ++ frame [] ++ rest) pre.length (by rw [read_start pre _ rest (frame_pos [])]; rfl))
    simpa [frame_nil] using h
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have s1 := Timed.single (p := machine) (by rfl)
      (mark_step (pre ++ frame (b :: w) ++ rest) pre.length (by rw [read_start pre _ rest (frame_pos _)]; rfl))
    have s2 := Timed.single (p := machine) (by rfl) (bit_step (pre ++ frame (b :: w) ++ rest) (pre.length+1))
    have s3 := ih (pre ++ [true, b])
    rw [← hw] at s3
    simp only [List.length_append, List.length_cons, List.length_nil] at s3
    have h := (s1.trans s2).trans s3
    have e1 : 1 + 1 + (2*w.length+1) = 2*(b :: w).length+1 := by simp; omega
    have e2 : pre.length + (0+1+1) + (frame w).length = pre.length + (frame (b :: w)).length := by
      simp only [frame_length', List.length_cons]; omega
    rw [e1, e2] at h
    simpa only [Nat.add_assoc] using h

theorem skip_run (pre w rest : List Bool) :
    ∃ r : ExecutionReceipt 1 3, runFrom machine (2*w.length+1) (cfg 0 (pre ++ frame w ++ rest) pre.length) = some r ∧
      r.final = cfg 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) ∧ r.steps = 2*w.length+1 :=
  (skip_timed pre w rest).run rfl

end FrameSkip

namespace FrameSkipMark

/-- Tape 0 stream, tape 1 measure (one `true` appended per scanned byte). -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, ![none, some true], ![.right, .right]⟩
      else ⟨2, ![none, some true], ![.right, .right]⟩)
    else if q.val = 1 then some ⟨0, ![none, some true], ![.right, .right]⟩
    else none

def cfg (q : Fin 3) (input : List Bool) (ih : ℕ) (marks : ℕ) : Configuration 2 3 :=
  ⟨q, ![ih, marks], ![input, List.replicate marks true]⟩

@[simp] theorem halted_two : machine.halted 2 = true := rfl

theorem mark_step (input : List Bool) (ih m : ℕ) (h : readTapeBit input ih = true) :
    step machine (cfg 0 input ih m) = some (cfg 1 input (ih+1) (m+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem end_step (input : List Bool) (ih m : ℕ) (h : readTapeBit input ih = false) :
    step machine (cfg 0 input ih m) = some (cfg 2 input (ih+1) (m+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem bit_step (input : List Bool) (ih m : ℕ) :
    step machine (cfg 1 input ih m) = some (cfg 0 input (ih+1) (m+1)) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem skip_timed (pre w rest : List Bool) (m : ℕ) :
    Timed machine (2*w.length+1) (cfg 0 (pre ++ frame w ++ rest) pre.length m)
      (cfg 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (m + (frame w).length)) := by
  induction w generalizing pre m with
  | nil =>
    have h := Timed.single (p := machine) (by rfl)
      (end_step (pre ++ frame [] ++ rest) pre.length m (by rw [read_start pre _ rest (frame_pos [])]; rfl))
    simpa [frame_nil] using h
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have s1 := Timed.single (p := machine) (by rfl)
      (mark_step (pre ++ frame (b :: w) ++ rest) pre.length m (by rw [read_start pre _ rest (frame_pos _)]; rfl))
    have s2 := Timed.single (p := machine) (by rfl) (bit_step (pre ++ frame (b :: w) ++ rest) (pre.length+1) (m+1))
    have s3 := ih (pre ++ [true, b]) (m+1+1)
    rw [← hw] at s3
    simp only [List.length_append, List.length_cons, List.length_nil] at s3
    have h := (s1.trans s2).trans s3
    have e1 : 1 + 1 + (2*w.length+1) = 2*(b :: w).length+1 := by simp; omega
    have e2 : pre.length + (0+1+1) + (frame w).length = pre.length + (frame (b :: w)).length := by
      simp only [frame_length', List.length_cons]; omega
    have e3 : m+1+1+(frame w).length = m + (frame (b :: w)).length := by
      simp only [frame_length', List.length_cons]; omega
    rw [e1, e2, e3] at h
    simpa only [Nat.add_assoc] using h

theorem skip_run (pre w rest : List Bool) (m : ℕ) :
    ∃ r : ExecutionReceipt 2 3, runFrom machine (2*w.length+1) (cfg 0 (pre ++ frame w ++ rest) pre.length m) = some r ∧
      r.final = cfg 2 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (m + (frame w).length) ∧
      r.steps = 2*w.length+1 :=
  (skip_timed pre w rest m).run rfl

end FrameSkipMark

end NearCubicWires.ExtDecompositionBatch
