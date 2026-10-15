import Proof.MachineModel.Basic
import Proof.MachineModel.OrdinaryMatrixScorePhi

namespace NearCubicWires.RepairOrdinary.MatrixBatchColumnsCopy
open LocalBitMultitape RecoveryExecution SignedSortKey NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 8 where
  descriptionBits := 0
  start := 6
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 6 then some ⟨5, fun _ => none, ![.stay, .stay, .stay, .right]⟩
    else if q.val = 5 then some (if bits 3 then ⟨0, fun _ => none, ![.stay, .stay, .stay, .right]⟩
      else ⟨7, fun _ => none, ![.stay, .stay, .stay, .left]⟩)
    else if q.val = 0 then some (if bits 0 then ⟨1, ![none, some true, some true, none], ![.right, .right, .right, .stay]⟩
      else ⟨5, ![none, some false, some true, none], ![.right, .right, .right, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, some (bits 0), some true, none], ![.right, .right, .right, .stay]⟩
    else if q.val = 7 then some (if bits 3 then ⟨7, fun _ => none, ![.stay, .stay, .stay, .left]⟩
      else ⟨2, fun _ => none, fun _ => .stay⟩)
    else if q.val = 2 then some ⟨3, fun _ => none, ![.stay, .stay, .left, .stay]⟩
    else if q.val = 3 then some (if bits 2 then ⟨3, ![none, none, some false, none], ![.stay, .left, .left, .stay]⟩
      else ⟨4, fun _ => none, fun _ => .stay⟩)
    else none

def cfg (q : Fin 8) (input : List Bool) (ih : ℕ) (dest : List Bool) (dh : ℕ)
    (marker : List Bool) (kh : ℕ) (counter : List Bool) (ch : ℕ) : Configuration 4 8 :=
  ⟨q, ![ih, dh, kh, ch], ![input, dest, marker, counter]⟩

@[simp] theorem halted_four : machine.halted 4 = true := rfl

/-- During the copy the destination and the marker have the same length as the number of copied cells
and both heads sit at their ends. -/
def copying (q : Fin 8) (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ) :
    Configuration 4 8 :=
  cfg q input ih dest dest.length (List.replicate dest.length true) dest.length counter ch

theorem start_step (input : List Bool) (ih : ℕ) (counter : List Bool) :
    step machine (copying 6 input ih [] counter 0) = some (copying 5 input ih [] counter 1) := by
  simp [step, machine, copying, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem check_true (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ)
    (h : readTapeBit counter ch = true) :
    step machine (copying 5 input ih dest counter ch) = some (copying 0 input ih dest counter (ch+1)) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem check_false (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ)
    (h : readTapeBit counter ch = false) :
    step machine (copying 5 input ih dest counter ch) = some (copying 7 input ih dest counter (ch-1)) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem mark_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ)
    (h : readTapeBit input ih = true) :
    step machine (copying 0 input ih dest counter ch) =
      some (copying 1 input (ih+1) (dest ++ [true]) counter ch) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

theorem bit_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ) :
    step machine (copying 1 input ih dest counter ch) =
      some (copying 0 input (ih+1) (dest ++ [readTapeBit input ih]) counter ch) := by
  simp [step, machine, copying, cfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

theorem end_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (ch : ℕ)
    (h : readTapeBit input ih = false) :
    step machine (copying 0 input ih dest counter ch) =
      some (copying 5 input (ih+1) (dest ++ [false]) counter ch) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end, write_end_replicate]

/-- One framed column: `|frame w|` steps, ending in the check state. -/
theorem frame_timed (pre w rest dest counter : List Bool) (ch : ℕ) :
    Timed machine (frame w).length (copying 0 (pre ++ frame w ++ rest) pre.length dest counter ch)
      (copying 5 (pre ++ frame w ++ rest) (pre.length + (frame w).length) (dest ++ frame w) counter ch) := by
  induction w generalizing pre dest with
  | nil =>
    have h := Timed.single (p := machine) (by rfl)
      (end_step (pre ++ frame [] ++ rest) pre.length dest counter ch
        (by rw [read_start pre _ rest (frame_pos [])]; rfl))
    simpa [frame_nil] using h
  | cons b w ih =>
    have hw : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by
      simp [frame_cons, List.append_assoc]
    have hb : readTapeBit (pre ++ frame (b :: w) ++ rest) (pre.length+1) = b := by
      have h := read_shift pre (frame (b :: w)) rest 1 (by simp [frame_cons])
      rw [h]; rfl
    have s1 := Timed.single (p := machine) (by rfl)
      (mark_step (pre ++ frame (b :: w) ++ rest) pre.length dest counter ch
        (by rw [read_start pre _ rest (frame_pos _)]; rfl))
    have s2 := Timed.single (p := machine) (by rfl)
      (bit_step (pre ++ frame (b :: w) ++ rest) (pre.length+1) (dest ++ [true]) counter ch)
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

/-- All columns: each is announced by one counter cell, then copied. -/
theorem columns_timed (width : ℕ) (cols : List ℕ) (pre rest dest counter : List Bool) (ch : ℕ)
    (hc : ∀ j, j < cols.length → readTapeBit counter (ch+j) = true) :
    Timed machine (cols.length + (MatrixScorePhi.columnsWord width cols).length)
      (copying 5 (pre ++ MatrixScorePhi.columnsWord width cols ++ rest) pre.length dest counter ch)
      (copying 5 (pre ++ MatrixScorePhi.columnsWord width cols ++ rest)
        (pre.length + (MatrixScorePhi.columnsWord width cols).length)
        (dest ++ MatrixScorePhi.columnsWord width cols) counter (ch + cols.length)) := by
  induction cols generalizing pre dest ch with
  | nil =>
    simpa [MatrixScorePhi.columnsWord] using (Timed.refl (p := machine) _)
  | cons x xs ih =>
    have hcw : MatrixScorePhi.columnsWord width (x :: xs) =
        frame (binary width x) ++ MatrixScorePhi.columnsWord width xs := by
      simp [MatrixScorePhi.columnsWord]
    have s1 := Timed.single (p := machine) (by rfl)
      (check_true (pre ++ MatrixScorePhi.columnsWord width (x :: xs) ++ rest) pre.length dest counter ch
        (by simpa using hc 0 (by simp)))
    have s2 := frame_timed pre (binary width x) (MatrixScorePhi.columnsWord width xs ++ rest) dest counter (ch+1)
    have hs : pre ++ frame (binary width x) ++ (MatrixScorePhi.columnsWord width xs ++ rest) =
        pre ++ MatrixScorePhi.columnsWord width (x :: xs) ++ rest := by
      rw [hcw]; simp [List.append_assoc]
    rw [hs] at s2
    have e5 : pre.length + (frame (binary width x)).length = (pre ++ frame (binary width x)).length := by simp
    rw [e5] at s2
    have s3 := ih (pre ++ frame (binary width x)) (dest ++ frame (binary width x)) (ch+1)
      (fun j hj => by
        have h := hc (j+1) (by simp; omega)
        rwa [show ch + (j+1) = ch + 1 + j by omega] at h)
    have hs3 : pre ++ frame (binary width x) ++ MatrixScorePhi.columnsWord width xs ++ rest =
        pre ++ MatrixScorePhi.columnsWord width (x :: xs) ++ rest := by
      rw [hcw]; simp [List.append_assoc]
    rw [hs3] at s3
    have h := (s1.trans s2).trans s3
    have e1 : 1 + (frame (binary width x)).length +
        (xs.length + (MatrixScorePhi.columnsWord width xs).length) =
        (x :: xs).length + (MatrixScorePhi.columnsWord width (x :: xs)).length := by
      rw [hcw]; simp; omega
    have e2 : (pre ++ frame (binary width x)).length + (MatrixScorePhi.columnsWord width xs).length =
        pre.length + (MatrixScorePhi.columnsWord width (x :: xs)).length := by
      rw [hcw]; simp; omega
    have e3 : dest ++ frame (binary width x) ++ MatrixScorePhi.columnsWord width xs =
        dest ++ MatrixScorePhi.columnsWord width (x :: xs) := by
      rw [hcw]; simp [List.append_assoc]
    have e4 : ch + 1 + xs.length = ch + (x :: xs).length := by simp; omega
    rw [e1, e2, e3, e4] at h
    exact h

/-! ## Return of the counter, driven by its leading `false` -/

theorem counter_back (input : List Bool) (ih : ℕ) (dest counter : List Bool) (j : ℕ)
    (h : readTapeBit counter (j+1) = true) :
    step machine (copying 7 input ih dest counter (j+1)) = some (copying 7 input ih dest counter j) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem counter_stop (input : List Bool) (ih : ℕ) (dest counter : List Bool)
    (h : readTapeBit counter 0 = false) :
    step machine (copying 7 input ih dest counter 0) = some (copying 2 input ih dest counter 0) := by
  simp [step, machine, copying, cfg, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem counter_timed (input : List Bool) (ih : ℕ) (dest : List Bool) (d : ℕ) :
    ∀ j, j ≤ d → Timed machine (j+1) (copying 7 input ih dest (UnaryTemplate.tape d) j)
      (copying 2 input ih dest (UnaryTemplate.tape d) 0)
  | 0, _ => Timed.single (p := machine) (by rfl)
      (counter_stop input ih dest (UnaryTemplate.tape d) (UnaryTemplate.tape_zero d))
  | j+1, hj => by
    have s1 := Timed.single (p := machine) (by rfl)
      (counter_back input ih dest (UnaryTemplate.tape d) j (UnaryTemplate.tape_mark d j (by omega)))
    have h := s1.trans (counter_timed input ih dest d j (by omega))
    rwa [show 1 + (j+1) = j+1+1 by omega] at h

/-! ## Return of the destination head, driven by the markers -/

theorem enter_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (n : ℕ) :
    step machine (cfg 2 input ih dest n (List.replicate n true) n counter 0) =
      some (cfg 3 input ih dest n (List.replicate n true) (n-1) counter 0) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · rfl

theorem back_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (k z : ℕ) :
    step machine (cfg 3 input ih dest (k+1) (List.replicate (k+1) true ++ List.replicate z false) k counter 0) =
      some (cfg 3 input ih dest k (List.replicate k true ++ List.replicate (z+1) false) (k-1) counter 0) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, Streaming.erase_counter]

theorem stop_step (input : List Bool) (ih : ℕ) (dest counter : List Bool) (z : ℕ) :
    step machine (cfg 3 input ih dest 0 (List.replicate z false) 0 counter 0) =
      some (cfg 4 input ih dest 0 (List.replicate z false) 0 counter 0) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem back_timed (input : List Bool) (ih : ℕ) (dest counter : List Bool) (k z : ℕ) :
    Timed machine (k+1) (cfg 3 input ih dest (k+1) (List.replicate (k+1) true ++ List.replicate z false) k counter 0)
      (cfg 3 input ih dest 0 (List.replicate (k+1+z) false) 0 counter 0) := by
  induction k generalizing z with
  | zero =>
    have h := Timed.single (p := machine) (by rfl) (back_step input ih dest counter 0 z)
    have e : 0+1+z = z+1 := by omega
    rw [e]
    simpa using h
  | succ k ihk =>
    have h1 := back_step input ih dest counter (k+1) z
    rw [Nat.add_sub_cancel] at h1
    have h := (Timed.single (p := machine) (by rfl) h1).trans (ihk (z+1))
    have e : k+1+(z+1) = k+1+1+z := by omega
    rw [e] at h
    have e2 : 1 + (k+1) = k+1+1 := by omega
    rw [e2] at h; exact h

theorem rewind_timed (input : List Bool) (ih : ℕ) (dest counter : List Bool) (n : ℕ) :
    Timed machine (n+2) (cfg 2 input ih dest n (List.replicate n true) n counter 0)
      (cfg 4 input ih dest 0 (List.replicate n false) 0 counter 0) := by
  cases n with
  | zero =>
    have s1 := Timed.single (p := machine) (by rfl) (enter_step input ih dest counter 0)
    have s2 := Timed.single (p := machine) (by rfl) (stop_step input ih dest counter 0)
    simpa using s1.trans s2
  | succ k =>
    have s1 := Timed.single (p := machine) (by rfl) (enter_step input ih dest counter (k+1))
    rw [Nat.add_sub_cancel] at s1
    have s2 := back_timed input ih dest counter k 0
    simp only [List.replicate_zero, List.append_nil, Nat.add_zero] at s2
    have s3 := Timed.single (p := machine) (by rfl) (stop_step input ih dest counter (k+1))
    have h := (s1.trans s2).trans s3
    have e : 1 + (k+1) + 1 = k+1+2 := by omega
    rw [e] at h; exact h

/-- The steps of the whole copy. -/
def budget (d : ℕ) (word : List Bool) : ℕ := 2*d + 2*word.length + 5

/-- **The columns copy.** From the stream cursor at the first column, the `d` framed columns are copied
verbatim onto the fresh destination; the cursor ends after the last column, and the destination head, the
marker head and the frame counter's head all return to cell 0. -/
theorem copy_run (width : ℕ) (cols : List ℕ) (pre rest : List Bool) :
    ∃ r : ExecutionReceipt 4 8,
      runFrom machine (budget cols.length (MatrixScorePhi.columnsWord width cols))
        (cfg 6 (pre ++ MatrixScorePhi.columnsWord width cols ++ rest) pre.length [] 0 [] 0
          (UnaryTemplate.tape cols.length) 0) = some r ∧
      r.final = cfg 4 (pre ++ MatrixScorePhi.columnsWord width cols ++ rest)
        (pre.length + (MatrixScorePhi.columnsWord width cols).length)
        (MatrixScorePhi.columnsWord width cols) 0
        (List.replicate (MatrixScorePhi.columnsWord width cols).length false) 0
        (UnaryTemplate.tape cols.length) 0 ∧
      r.steps = budget cols.length (MatrixScorePhi.columnsWord width cols) := by
  let cw := MatrixScorePhi.columnsWord width cols
  let src := pre ++ cw ++ rest
  let d := cols.length
  have s0 := Timed.single (p := machine) (by rfl) (start_step src pre.length (UnaryTemplate.tape d))
  have s1 := columns_timed width cols pre rest [] (UnaryTemplate.tape d) 1
    (fun j hj => by
      have h := UnaryTemplate.tape_mark d j hj
      rwa [show j + 1 = 1 + j by omega] at h)
  simp only [List.nil_append] at s1
  have hend : readTapeBit (UnaryTemplate.tape d) (1 + d) = false := by
    rw [show 1 + d = d + 1 by omega]; exact UnaryTemplate.tape_end d
  have s2 := Timed.single (p := machine) (by rfl)
    (check_false src (pre.length + cw.length) cw (UnaryTemplate.tape d) (1 + d) hend)
  rw [show 1 + d - 1 = d by omega] at s2
  have s3 := counter_timed src (pre.length + cw.length) cw d d le_rfl
  have s4 := rewind_timed src (pre.length + cw.length) cw (UnaryTemplate.tape d) cw.length
  have h := (((s0.trans s1).trans s2).trans s3).trans s4
  have e : 1 + (d + cw.length) + 1 + (d + 1) + (cw.length + 2) = budget d cw := by
    unfold budget; omega
  rw [e] at h
  have hstart : copying 6 src pre.length [] (UnaryTemplate.tape d) 0 =
      cfg 6 src pre.length [] 0 [] 0 (UnaryTemplate.tape d) 0 := rfl
  rw [hstart] at h
  exact h.run rfl

end NearCubicWires.RepairOrdinary.MatrixBatchColumnsCopy
