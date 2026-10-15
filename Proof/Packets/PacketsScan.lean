import Proof.MachineModel.FrameCopy

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

/-- The doubled payload of a frame: each bit behind a `true` marker. -/
def dbl (w : List Bool) : List Bool := w.flatMap (fun b => [true, b])

theorem frame_append (u v : List Bool) : frame (u ++ v) = dbl u ++ frame v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [dbl, frame_cons, ih]

theorem frame_eq_dbl (w : List Bool) : frame w = dbl w ++ [false] := by
  have h := frame_append w []
  simpa [frame_nil] using h

@[simp] theorem dbl_length (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [dbl] at ih ⊢; omega

/-! ## `CountTrue` -/

namespace CountTrue

/-- Tapes: 0 source (a frame), 1 unary output. States: 0 marker, 1 payload, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, ![.right, .stay]⟩
      else ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some (if bits 0 then ⟨0, ![none, some true], ![.right, .right]⟩
      else ⟨0, fun _ => none, ![.right, .stay]⟩)
    else none

def cfg (q : Fin 3) (src : List Bool) (sh c : ℕ) : Configuration 2 3 :=
  ⟨q, ![sh, c], ![src, List.replicate c true]⟩

theorem mark_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 0 src sh c) = some (cfg 1 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem one_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 1 src sh c) = some (cfg 0 src (sh+1) (c+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem zero_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 1 src sh c) = some (cfg 0 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem end_step (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 0 src sh c) = some (cfg 2 src sh c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem scan_timed (pre w rest : List Bool) (c : ℕ) :
    Timed machine (2 * w.length) (cfg 0 (pre ++ frame w ++ rest) pre.length c)
      (cfg 0 (pre ++ frame w ++ rest) (pre.length + 2 * w.length) (c + w.count true)) := by
  induction w generalizing pre c with
  | nil => simpa using Timed.refl machine (cfg 0 (pre ++ frame [] ++ rest) pre.length c)
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have hm : readTapeBit (pre ++ frame (b :: w) ++ rest) pre.length = true := by
      rw [read_start pre _ rest (frame_pos _)]; rfl
    have hb : readTapeBit (pre ++ frame (b :: w) ++ rest) (pre.length+1) = b := by
      have h := read_shift pre (frame (b :: w)) rest 1 (by simp [frame_cons])
      rw [h]; rfl
    have s1 := Timed.single (p := machine) (by rfl) (mark_step _ _ c hm)
    have hl : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    cases b with
    | true =>
      have s2 := Timed.single (p := machine) (by rfl) (one_step _ (pre.length+1) c hb)
      have s3 := ih (pre ++ [true, true]) (c+1)
      rw [← hw, hl] at s3
      have h := (s1.trans s2).trans s3
      have e1 : 1 + 1 + 2 * w.length = 2 * (true :: w).length := by simp; omega
      have e2 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (true :: w).length := by simp; omega
      have e3 : c + 1 + w.count true = c + (true :: w).count true := by simp; omega
      rw [e1, e2, e3] at h
      exact h
    | false =>
      have s2 := Timed.single (p := machine) (by rfl) (zero_step _ (pre.length+1) c hb)
      have s3 := ih (pre ++ [true, false]) c
      rw [← hw, hl] at s3
      have h := (s1.trans s2).trans s3
      have e1 : 1 + 1 + 2 * w.length = 2 * (false :: w).length := by simp; omega
      have e2 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (false :: w).length := by simp; omega
      have e3 : c + w.count true = c + (false :: w).count true := by simp
      rw [e1, e2, e3] at h
      exact h

/-- **The count.** Exactly `(frame w).length` steps; output `replicate (w.count true) true`. -/
theorem run (pre w rest : List Bool) :
    ∃ r : ExecutionReceipt 2 3,
      runFrom machine (frame w).length (cfg 0 (pre ++ frame w ++ rest) pre.length 0) = some r ∧
      r.final = cfg 2 (pre ++ frame w ++ rest) (pre.length + 2 * w.length) (w.count true) ∧
      r.steps = (frame w).length := by
  have hs := scan_timed pre w rest 0
  have he : readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * w.length) = false := by
    rw [read_shift pre (frame w) rest (2 * w.length) (by simp), frame_eq_dbl]
    have h := read_suffix (dbl w) [false] 0
    rw [dbl_length, Nat.add_zero] at h
    rw [h]
    rfl
  have s := hs.trans (Timed.single (p := machine) (by rfl) (end_step _ _ _ he))
  rw [Nat.zero_add] at s
  obtain ⟨r, hr, hf, hsteps⟩ := s.run rfl
  have e : 2 * w.length + 1 = (frame w).length := by simp
  rw [e] at hr hsteps
  exact ⟨r, hr, hf, hsteps⟩

end CountTrue

/-! ## `CountFrames` -/

namespace CountFrames

/-- Tapes: 0 source (a frame of a concatenation of frames), 1 unary output.
States: 0 outer marker, 1 inner marker, 2 outer marker (inner payload next), 3 inner payload, 4 halt. -/
def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, ![.right, .stay]⟩
      else ⟨4, fun _ => none, fun _ => .stay⟩)
    else if q.val = 1 then some (if bits 0 then ⟨2, fun _ => none, ![.right, .stay]⟩
      else ⟨0, ![none, some true], ![.right, .right]⟩)
    else if q.val = 2 then some ⟨3, fun _ => none, ![.right, .stay]⟩
    else if q.val = 3 then some ⟨0, fun _ => none, ![.right, .stay]⟩
    else none

def cfg (q : Fin 5) (src : List Bool) (sh c : ℕ) : Configuration 2 5 :=
  ⟨q, ![sh, c], ![src, List.replicate c true]⟩

theorem a_true (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 0 src sh c) = some (cfg 1 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem b_true (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = true) :
    step machine (cfg 1 src sh c) = some (cfg 2 src (sh+1) c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem c_any (src : List Bool) (sh c : ℕ) :
    step machine (cfg 2 src sh c) = some (cfg 3 src (sh+1) c) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem d_any (src : List Bool) (sh c : ℕ) :
    step machine (cfg 3 src sh c) = some (cfg 0 src (sh+1) c) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem b_false (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 1 src sh c) = some (cfg 0 src (sh+1) (c+1)) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem a_false (src : List Bool) (sh c : ℕ) (h : readTapeBit src sh = false) :
    step machine (cfg 0 src sh c) = some (cfg 4 src sh c) := by
  simp [step, machine, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem dbl_append (u v : List Bool) : dbl (u ++ v) = dbl u ++ dbl v := by
  simp [dbl, List.flatMap_append]

theorem dbl_frame_nil : dbl (frame []) = [true, false] := rfl

theorem dbl_frame_cons (b : Bool) (x : List Bool) :
    dbl (frame (b :: x)) = [true, true, true, b] ++ dbl (frame x) := by
  simp [frame_cons, dbl]

/-- One inner frame: `4·|x|+2` steps, one more `true` on the output. -/
theorem inner_timed (pre x rest : List Bool) (c : ℕ) :
    Timed machine (4 * x.length + 2) (cfg 0 (pre ++ dbl (frame x) ++ rest) pre.length c)
      (cfg 0 (pre ++ dbl (frame x) ++ rest) (pre.length + (dbl (frame x)).length) (c + 1)) := by
  induction x generalizing pre with
  | nil =>
    have h1 : readTapeBit (pre ++ dbl (frame []) ++ rest) pre.length = true := by
      rw [dbl_frame_nil, read_start pre _ rest (by simp)]; rfl
    have h2 : readTapeBit (pre ++ dbl (frame []) ++ rest) (pre.length + 1) = false := by
      rw [dbl_frame_nil, read_shift pre _ rest 1 (by simp)]; rfl
    have s := (Timed.single (p := machine) (by rfl) (a_true _ _ c h1)).trans
      (Timed.single (p := machine) (by rfl) (b_false _ _ c h2))
    have e : (dbl (frame [])).length = 1 + 1 := by rw [dbl_frame_nil]; rfl
    rw [e, ← Nat.add_assoc]
    simpa using s
  | cons b x ih =>
    have hw : pre ++ dbl (frame (b :: x)) ++ rest = (pre ++ [true, true, true, b]) ++ dbl (frame x) ++ rest := by
      rw [dbl_frame_cons]; simp [List.append_assoc]
    have hsrc : ∀ j, j < 4 → readTapeBit (pre ++ dbl (frame (b :: x)) ++ rest) (pre.length + j) =
        ([true, true, true, b] : List Bool).getD j false := by
      intro j hj
      rw [hw, List.append_assoc, List.append_assoc, read_suffix, read_prefix _ _ j (by simp; omega)]
      rfl
    have h0 := hsrc 0 (by omega)
    have h1 := hsrc 1 (by omega)
    simp only [Nat.add_zero] at h0
    have s1 := Timed.single (p := machine) (by rfl) (a_true _ _ c h0)
    have s2 := Timed.single (p := machine) (by rfl) (b_true _ _ c h1)
    have s3 := Timed.single (p := machine) (by rfl) (c_any (pre ++ dbl (frame (b :: x)) ++ rest) (pre.length+1+1) c)
    have s4 := Timed.single (p := machine) (by rfl) (d_any (pre ++ dbl (frame (b :: x)) ++ rest) (pre.length+1+1+1) c)
    have s5 := ih (pre ++ [true, true, true, b])
    rw [← hw] at s5
    have hl : (pre ++ [true, true, true, b]).length = pre.length+1+1+1+1 := by simp
    rw [hl] at s5
    have h := (((s1.trans s2).trans s3).trans s4).trans s5
    have e1 : 1 + 1 + 1 + 1 + (4 * x.length + 2) = 4 * (b :: x).length + 2 := by simp; omega
    have e2 : pre.length+1+1+1+1 + (dbl (frame x)).length = pre.length + (dbl (frame (b :: x))).length := by
      rw [dbl_frame_cons]; simp; omega
    rw [e1, e2] at h
    exact h

/-- The inner frames of a list, concatenated. -/
def frames (xs : List (List Bool)) : List Bool := (xs.map frame).flatten

theorem frames_cons (x : List Bool) (xs : List (List Bool)) : frames (x :: xs) = frame x ++ frames xs := rfl

/-- The step count of the scan. -/
def cost (xs : List (List Bool)) : ℕ := (xs.map (fun x => 4 * x.length + 2)).sum

theorem cost_eq (xs : List (List Bool)) : cost xs = 2 * (frames xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [cost, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, frames_cons, List.length_append, frame_length']
    ring

theorem frames_timed (pre rest : List Bool) (xs : List (List Bool)) (c : ℕ) :
    Timed machine (cost xs) (cfg 0 (pre ++ dbl (frames xs) ++ rest) pre.length c)
      (cfg 0 (pre ++ dbl (frames xs) ++ rest) (pre.length + (dbl (frames xs)).length) (c + xs.length)) := by
  induction xs generalizing pre c with
  | nil => simpa [cost, frames, dbl] using Timed.refl machine (cfg 0 (pre ++ dbl (frames []) ++ rest) pre.length c)
  | cons x xs ih =>
    have hw : pre ++ dbl (frames (x :: xs)) ++ rest = pre ++ dbl (frame x) ++ (dbl (frames xs) ++ rest) := by
      rw [frames_cons, dbl_append]; simp [List.append_assoc]
    have s1 := inner_timed pre x (dbl (frames xs) ++ rest) c
    rw [← hw] at s1
    have hw2 : pre ++ dbl (frames (x :: xs)) ++ rest = (pre ++ dbl (frame x)) ++ dbl (frames xs) ++ rest := by
      rw [frames_cons, dbl_append]; simp [List.append_assoc]
    have s2 := ih (pre ++ dbl (frame x)) (c + 1)
    rw [← hw2, List.length_append] at s2
    have h := s1.trans s2
    have e1 : 4 * x.length + 2 + cost xs = cost (x :: xs) := by simp [cost]
    have e2 : pre.length + (dbl (frame x)).length + (dbl (frames xs)).length =
        pre.length + (dbl (frames (x :: xs))).length := by
      rw [frames_cons, dbl_append, List.length_append]; omega
    have e3 : c + 1 + xs.length = c + (x :: xs).length := by simp; omega
    rw [e1, e2, e3] at h
    exact h

/-- **The count.** On the doubly-framed field `frame (frames xs)`, exactly `(frame (frames xs)).length`
steps; output `replicate xs.length true`. -/
theorem run (pre rest : List Bool) (xs : List (List Bool)) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (frame (frames xs)).length (cfg 0 (pre ++ frame (frames xs) ++ rest) pre.length 0) = some r ∧
      r.final = cfg 4 (pre ++ frame (frames xs) ++ rest) (pre.length + (dbl (frames xs)).length) xs.length ∧
      r.steps = (frame (frames xs)).length := by
  have hf : pre ++ frame (frames xs) ++ rest = pre ++ dbl (frames xs) ++ ([false] ++ rest) := by
    rw [frame_eq_dbl]; simp [List.append_assoc]
  have hs := frames_timed pre ([false] ++ rest) xs 0
  rw [← hf] at hs
  have he : readTapeBit (pre ++ frame (frames xs) ++ rest) (pre.length + (dbl (frames xs)).length) = false := by
    rw [hf, List.append_assoc, read_suffix]
    have h := read_suffix (dbl (frames xs)) ([false] ++ rest) 0
    rw [Nat.add_zero] at h
    rw [h]
    rfl
  have s := hs.trans (Timed.single (p := machine) (by rfl) (a_false _ _ _ he))
  rw [Nat.zero_add] at s
  obtain ⟨r, hr, hfin, hsteps⟩ := s.run rfl
  have e : cost xs + 1 = (frame (frames xs)).length := by
    rw [cost_eq, frame_eq_dbl, List.length_append, dbl_length]; simp
  rw [e] at hr hsteps
  exact ⟨r, hr, hfin, hsteps⟩

end CountFrames

end NearCubicWires.PacketsGlue

