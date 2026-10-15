import Proof.Supplier.RowTupleOutputLoop

/-! The complete binary subset enumerator starts at zero and stops at the
first out-of-range counter. Its stream lists every selected occurrence once. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumeration
open LocalBitMultitape RowTupleFilterParts RowTupleFilterMeaning RowTupleOutputParts
open RowTupleOutputBody RowTupleOutputMeaning RowTupleDigits RowTupleSubsets SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def start (w k M : ℕ) := initial (frame (binary (w*k+1) 0)) M
def result (w k M : ℕ) := iterated w k 0 (2^(w*k)) (start w k M)
def word (w k M : ℕ) := (selected w M k).flatMap
  (fun ds=>frame (binary (w*k+1) (encode w ds)))
def time (w k : ℕ) := 2^(w*k)*(k*(52*w+68)+40)+1

theorem iterated_fields (w k n count : ℕ) (x : Data)
    (hx : x.source=frame (binary (w*k+1) n)) (hp : x.previous<2^w) :
    (iterated w k n count x).source=frame (binary (w*k+1) (n+count)) ∧
    (iterated w k n count x).bound=x.bound ∧ (iterated w k n count x).previous<2^w := by
  induction count generalizing n x with
  | zero => exact ⟨by simpa only [iterated,Nat.add_zero] using hx,rfl,hp⟩
  | succ count ih =>
    have hf := updated_fields w k n x hp
    obtain ⟨hs,hb,hp'⟩ := ih (n+1) (updated w k n x) hf.1 hf.2.2
    exact ⟨by simpa [iterated,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs,
      hb.trans hf.2.1,hp'⟩

theorem enumerate_run (w k M : ℕ) (out : List Bool) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,runFrom RowTupleOutputLoop.machine (time w k)
      (cfg RowTupleOutputLoop.machine.start w k (start w k M) true out)=some r ∧
      r.final.heads=(cfg RowTupleOutputLoop.machine.start w k (result w k M) false (out++word w k M)).heads ∧
      r.final.tapes=(cfg RowTupleOutputLoop.machine.start w k (result w k M) false (out++word w k M)).tapes ∧
      r.final.tapes 0=frame (binary (w*k+1) (2^(w*k))) ∧
      r.final.tapes 17=out++word w k M ∧ r.steps≤time w k := by
  obtain ⟨r,hr,rh,rt,rs⟩ := RowTupleOutputLoop.loop_run w k M 0 (2^(w*k)) (start w k M) out
    (by omega) hM hMw rfl rfl (by change 0<2^w; positivity)
  have hn : decide (0<2^(w*k))=true := by simp
  have ht : RowTupleOutputLoop.budget w k (2^(w*k))=time w k := by
    unfold RowTupleOutputLoop.budget RowTupleOutputBody.budget time
    ring
  rw [ht,hn] at hr
  rw [ht] at rs
  rw [full_output] at rh rt
  refine ⟨r,hr,rh,rt,?_,?_,rs⟩
  · rw [rt]
    change (iterated w k 0 (2^(w*k)) (start w k M)).source=_
    simpa only [Nat.zero_add] using (iterated_fields w k 0 (2^(w*k)) (start w k M) rfl (by change 0<2^w; positivity)).1
  · rw [rt]; rfl

theorem time_bound (M k : ℕ) :
    time (digitWidth M) k≤(2*max 1 M)^k*(k*(52*digitWidth M+68)+40)+1 := by
  unfold time
  rw [pow_mul]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (digit_capacity M) k)) 1

theorem occurrence_order (w k M : ℕ) (hM : M≤2^w) :
    (selected w M k).Perm ((List.range M).sublistsLen k) := selected_perm w M k hM

end NearCubicWires.RepairOrdinary.RowTupleEnumeration
