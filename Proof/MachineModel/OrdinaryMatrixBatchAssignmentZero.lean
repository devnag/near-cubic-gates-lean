import Proof.MachineModel.Basic

namespace NearCubicWires.RepairOrdinary.MatrixBatchAssignmentZero
open LocalBitMultitape RecoveryExecution SignedSortKey NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q bits =>
    if q.val = 0 then some (if bits 0 then ⟨1, fun _ => none, ![.right, .stay]⟩
      else ⟨2, fun _ => none, ![.stay, .left]⟩)
    else if q.val = 1 then some ⟨0, ![some false, none], ![.right, .right]⟩
    else if q.val = 2 then some (if bits 1 then ⟨3, fun _ => none, ![.left, .stay]⟩
      else ⟨4, fun _ => none, ![.stay, .right]⟩)
    else if q.val = 3 then some ⟨2, fun _ => none, ![.left, .left]⟩
    else none

def cfg (q : Fin 5) (tape : List Bool) (h0 : ℕ) (sentinel : List Bool) (h1 : ℕ) : Configuration 2 5 :=
  ⟨q, ![h0, h1], ![tape, sentinel]⟩

theorem write_prefix (pre tail : List Bool) (old bit : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length bit = pre ++ bit :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

/-- The zeroed pairs of the first `k` payload cells. -/
def zeroed (k : ℕ) : List Bool := Streaming.marks (List.replicate k false)

@[simp] theorem zeroed_length (k : ℕ) : (zeroed k).length = 2*k := by simp [zeroed]

theorem zeroed_succ (k : ℕ) : zeroed (k+1) = zeroed k ++ [true, false] := by
  simp [zeroed, Streaming.marks, List.replicate_succ']

theorem mark_step (k : ℕ) (b : Bool) (rest sentinel : List Bool) (h1 : ℕ) :
    step machine (cfg 0 (zeroed k ++ frame (b :: rest)) (2*k) sentinel h1) =
      some (cfg 1 (zeroed k ++ frame (b :: rest)) (2*k+1) sentinel h1) := by
  have hr : readTapeBit (zeroed k ++ frame (b :: rest)) (2*k) = true := by
    have h := Streaming.read_append (zeroed k) (b :: frame rest) true
    simpa [frame_cons] using h
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem payload_step (k : ℕ) (b : Bool) (rest sentinel : List Bool) (h1 : ℕ) :
    step machine (cfg 1 (zeroed k ++ frame (b :: rest)) (2*k+1) sentinel h1) =
      some (cfg 0 (zeroed (k+1) ++ frame rest) (2*(k+1)) sentinel (h1+1)) := by
  have hw : writeTapeBit (zeroed k ++ frame (b :: rest)) (2*k+1) false = zeroed (k+1) ++ frame rest := by
    have h := write_prefix (zeroed k ++ [true]) (frame rest) b false
    have e1 : zeroed k ++ [true] ++ b :: frame rest = zeroed k ++ frame (b :: rest) := by
      simp [frame_cons]
    have e2 : (zeroed k ++ [true]).length = 2*k+1 := by simp
    rw [e1, e2] at h
    rw [h, zeroed_succ]
    simp
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction, hw]

theorem forward_timed (rest sentinel : List Bool) :
    ∀ k, Timed machine (2*rest.length)
      (cfg 0 (zeroed k ++ frame rest) (2*k) sentinel (k+1))
      (cfg 0 (zeroed (k+rest.length) ++ frame []) (2*(k+rest.length)) sentinel (k+rest.length+1)) := by
  induction rest with
  | nil => intro k; simpa using Timed.refl (p := machine) _
  | cons b rest ih =>
    intro k
    have s1 := Timed.single (p := machine) (by rfl) (mark_step k b rest sentinel (k+1))
    have s2 := Timed.single (p := machine) (by rfl) (payload_step k b rest sentinel (k+1))
    have s3 := ih (k+1)
    have h := (s1.trans s2).trans s3
    have e1 : 1 + 1 + 2*rest.length = 2*(b :: rest).length := by simp; omega
    have e2 : k + 1 + rest.length = k + (b :: rest).length := by simp; omega
    rw [e1, e2] at h
    exact h

theorem end_step (k : ℕ) (sentinel : List Bool) (h1 : ℕ) :
    step machine (cfg 0 (zeroed k ++ frame []) (2*k) sentinel (h1+1)) =
      some (cfg 2 (zeroed k ++ frame []) (2*k) sentinel h1) := by
  have hr : readTapeBit (zeroed k ++ frame []) (2*k) = false := by
    have h := Streaming.read_append (zeroed k) [] false
    simpa [frame_nil] using h
  simp [step, machine, cfg, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> rfl

theorem back_timed (tape : List Bool) (w : ℕ) :
    ∀ j, j ≤ w → Timed machine (2*j+1) (cfg 2 tape (2*j) (UnaryTemplate.tape w) j)
      (cfg 4 tape 0 (UnaryTemplate.tape w) 1)
  | 0, _ => by
    have h : step machine (cfg 2 tape 0 (UnaryTemplate.tape w) 0) = some (cfg 4 tape 0 (UnaryTemplate.tape w) 1) := by
      simp [step, machine, cfg, Configuration.scanned, UnaryTemplate.tape_zero]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
      · funext i; fin_cases i <;> rfl
    simpa using Timed.single (p := machine) (by rfl) h
  | j+1, hj => by
    have hm : readTapeBit (UnaryTemplate.tape w) (j+1) = true := UnaryTemplate.tape_mark w j (by omega)
    have h1 : step machine (cfg 2 tape (2*(j+1)) (UnaryTemplate.tape w) (j+1)) =
        some (cfg 3 tape (2*j+1) (UnaryTemplate.tape w) (j+1)) := by
      simp [step, machine, cfg, Configuration.scanned, hm]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]; omega
      · funext i; fin_cases i <;> rfl
    have h2 : step machine (cfg 3 tape (2*j+1) (UnaryTemplate.tape w) (j+1)) =
        some (cfg 2 tape (2*j) (UnaryTemplate.tape w) j) := by
      simp [step, machine, cfg]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
      · rfl
    have h := ((Timed.single (p := machine) (by rfl) h1).trans (Timed.single (p := machine) (by rfl) h2)).trans
      (back_timed tape w j (by omega))
    have e : 1 + 1 + (2*j+1) = 2*(j+1)+1 := by omega
    rw [e] at h
    exact h

theorem zeroed_frame (k : ℕ) : zeroed k ++ frame [] = frame (List.replicate k false) := by
  rw [zeroed, ← Streaming.frame_append, List.append_nil]

/-- **The zeroing.** `frame bits` becomes `frame (List.replicate |bits| false)` in `4|bits| + 2` steps; both
heads return. -/
theorem zero_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (4*bits.length+2) (cfg 0 (frame bits) 0 (UnaryTemplate.tape bits.length) 1) = some r ∧
      r.final = cfg 4 (frame (List.replicate bits.length false)) 0 (UnaryTemplate.tape bits.length) 1 ∧
      r.steps = 4*bits.length+2 := by
  have s1 := forward_timed bits (UnaryTemplate.tape bits.length) 0
  simp only [Nat.zero_add, Nat.mul_zero] at s1
  have hz : zeroed 0 = [] := rfl
  rw [hz, List.nil_append] at s1
  have s2 := Timed.single (p := machine) (by rfl) (end_step bits.length (UnaryTemplate.tape bits.length) bits.length)
  have s3 := back_timed (zeroed bits.length ++ frame []) bits.length bits.length le_rfl
  have h := (s1.trans s2).trans s3
  rw [zeroed_frame] at h
  have e : 2*bits.length + 1 + (2*bits.length+1) = 4*bits.length+2 := by omega
  rw [e] at h
  exact h.run rfl

theorem binary_zero (w : ℕ) : binary w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [binary, ih, List.replicate_succ]

/-- The assignment form: `frame (binary w x)` becomes `frame (binary w 0)`. -/
theorem assignment_run (w x : ℕ) :
    ∃ r : ExecutionReceipt 2 5,
      runFrom machine (4*w+2) (cfg 0 (frame (binary w x)) 0 (UnaryTemplate.tape w) 1) = some r ∧
      r.final = cfg 4 (frame (binary w 0)) 0 (UnaryTemplate.tape w) 1 ∧ r.steps = 4*w+2 := by
  have h := zero_run (binary w x)
  simp only [binary_length] at h
  rwa [binary_zero]

end NearCubicWires.RepairOrdinary.MatrixBatchAssignmentZero
