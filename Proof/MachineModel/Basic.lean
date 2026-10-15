import Proof.MachineModel.OrdinaryUnaryTemplate
import Proof.Foundations.OrdinaryStreaming
import Proof.Amplification.RecoveryTimedExecution
import Proof.Foundations.OrdinaryRewindCarrier

/-! P25 outside project (`ExtDecompositionBatch`): shared local tape lemmas for
the bespoke frame workers. Nothing here depends on the source or on a layout. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem read_prefix (l rest : List Bool) (j : ℕ) (hj : j < l.length) :
    readTapeBit (l ++ rest) j = readTapeBit l j := by
  simp only [readTapeBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

theorem read_suffix (l rest : List Bool) (j : ℕ) :
    readTapeBit (l ++ rest) (l.length + j) = readTapeBit rest j := by
  simp only [readTapeBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem read_shift (pre mid rest : List Bool) (j : ℕ) (hj : j < mid.length) :
    readTapeBit (pre ++ mid ++ rest) (pre.length + j) = readTapeBit mid j := by
  rw [List.append_assoc, read_suffix, read_prefix _ _ j hj]

theorem read_at (pre rest : List Bool) (b : Bool) :
    readTapeBit (pre ++ b :: rest) pre.length = b := Streaming.read_append pre rest b

theorem read_start (pre mid rest : List Bool) (hm : 0 < mid.length) :
    readTapeBit (pre ++ mid ++ rest) pre.length = readTapeBit mid 0 := by
  have h := read_shift pre mid rest 0 hm
  rwa [Nat.add_zero] at h

/-- Appending one cell at the end of a tape. -/
theorem write_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] :=
  Streaming.write_append l b

theorem write_end_replicate (c : ℕ) (b : Bool) :
    writeTapeBit (List.replicate c b) c b = List.replicate (c+1) b := by
  rw [List.replicate_succ']
  have h := Streaming.write_append (List.replicate c b) b
  rwa [List.length_replicate] at h

theorem read_replicate_true (n j : ℕ) (hj : j < n) : readTapeBit (List.replicate n true) j = true := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, hj]

theorem read_replicate_end (n : ℕ) (b : Bool) : readTapeBit (List.replicate n b) n = false := by
  simp [readTapeBit, List.getD_eq_getElem?_getD]

theorem read_frame_mark (w : List Bool) (b : Bool) : readTapeBit (frame (b :: w)) 0 = true := rfl
theorem read_frame_end : readTapeBit (frame []) 0 = false := rfl

theorem frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl
theorem frame_nil : frame [] = [false] := rfl

@[simp] theorem frame_length' (w : List Bool) : (frame w).length = 2*w.length+1 := frame_length w

theorem frame_pos (w : List Bool) : 1 ≤ (frame w).length := by
  rw [frame_length']; omega

/-- A `Timed` run whose final control is halted is a `runFrom` receipt. -/
theorem timed_run {t s : ℕ} {p : Machine t s} {n : ℕ} {c d : Configuration t s}
    (h : Timed p n c d) (hd : p.halted d.control = true) :
    ∃ r : ExecutionReceipt t s, runFrom p n c = some r ∧ r.final = d ∧ r.steps = n :=
  h.run hd

end NearCubicWires.ExtDecompositionBatch
