import Proof.MachineModel.OrdinaryMatrixPayloadCountBodies

namespace NearCubicWires.RepairOrdinary.MatrixPayloadCount
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 4 → ℕ := ![2,12,2,5]
noncomputable def programs : (j : Fin 4) → Machine 3 (sizes j)
  | ⟨0,_⟩ => gate
  | ⟨1,_⟩ => skip
  | ⟨2,_⟩ => emit
  | ⟨3,_⟩ => finish
  | ⟨n+4,h⟩ => False.elim (by omega)
def next (j : Fin 4) (_ : Fin (sizes j)) (bits : Fin 3 → Bool) : Option (Fin 4) :=
  if j=0 then if bits 1 then some 1 else some 3
  else if j=1 then some 2 else if j=2 then some 0 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (j : Fin 4) (u : ℕ) (source : List Bool) (pos count : ℕ) :=
  controlConfig (RecoveryCalls.code sizes j) (config (programs j).start u source pos count)
noncomputable def result (u : ℕ) (source : List Bool) (pos count : ℕ) :=
  RecoveryCalls.stopped sizes (finished (s:=5) 4 u source pos count).heads
    (finished (s:=5) 4 u source pos count).tapes

theorem gate_continue (u : ℕ) (source : List Bool) (pos count : ℕ)
    (hm : readTapeBit source pos=true) :
    ∃ time≤2, Timed machine time (boundary 0 u source pos count) (boundary 1 u source pos count) := by
  obtain ⟨r,hr,hf,_⟩ := gate_run u source pos count
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 0 1 1
    (config (programs 0).start u source pos count) r hr (by rw [hf]; simpa [next,Configuration.scanned,config] using hm)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem gate_finish (u : ℕ) (source : List Bool) (pos count : ℕ)
    (hm : readTapeBit source pos=false) :
    ∃ time≤2, Timed machine time (boundary 0 u source pos count) (boundary 3 u source pos count) := by
  obtain ⟨r,hr,hf,_⟩ := gate_run u source pos count
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 0 3 1
    (config (programs 0).start u source pos count) r hr (by rw [hf]; simp [next,Configuration.scanned,config,hm])
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem skip_call (u : ℕ) (source : List Bool) (pos count : ℕ) :
    ∃ time≤6*u+10, Timed machine time (boundary 1 u source pos count)
      (boundary 2 u source (pos+4*u) count) := by
  obtain ⟨r,hr,hf,_⟩ := skip_run u source pos count
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 1 2 (6*u+9)
    (config (programs 1).start u source pos count) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem emit_call (u : ℕ) (source : List Bool) (pos count : ℕ) :
    ∃ time≤2, Timed machine time (boundary 2 u source pos count) (boundary 0 u source pos (count+1)) := by
  obtain ⟨r,hr,hf,_⟩ := emit_run u source pos count
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 2 0 1
    (config (programs 2).start u source pos count) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem finish_call (u : ℕ) (source : List Bool) (pos count : ℕ) :
    ∃ time≤count+5, Timed machine time (boundary 3 u source pos count) (result u source pos count) := by
  obtain ⟨r,hr,hf,_⟩ := finish_run u source pos count
  obtain ⟨time,hbound,ht⟩ := stop_receipt sizes programs 0 next 3 (count+4)
    (config (programs 3).start u source pos count) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem loop_timed (u : ℕ) (source : List Bool) (pos count i remaining : ℕ)
    (hm : ∀ j≤count, readTapeBit source (pos+4*u*j)=decide (j<count)) (hi : i+remaining=count) :
    ∃ time≤remaining*(6*u+14)+count+7,
      Timed machine time (boundary 0 u source (pos+4*u*i) i)
        (result u source (pos+4*u*count) count) := by
  induction remaining generalizing i with
  | zero =>
    have he : i=count := by omega
    subst i
    obtain ⟨t0,h0,p0⟩ := gate_finish u source (pos+4*u*count) count (by simpa using hm count (by omega))
    obtain ⟨t1,h1,p1⟩ := finish_call u source (pos+4*u*count) count
    exact ⟨t0+t1,by omega,p0.trans p1⟩
  | succ remaining ih =>
    have hlt : i<count := by omega
    obtain ⟨t0,h0,p0⟩ := gate_continue u source (pos+4*u*i) i (by simpa [hlt] using hm i (by omega))
    obtain ⟨t1,h1,p1⟩ := skip_call u source (pos+4*u*i) i
    obtain ⟨t2,h2,p2⟩ := emit_call u source (pos+4*u*i+4*u) i
    have he : pos+4*u*i+4*u=pos+4*u*(i+1) := by ring
    rw [he] at p1 p2
    obtain ⟨t3,h3,p3⟩ := ih (i+1) (by omega)
    refine ⟨t0+(t1+(t2+t3)),?_,p0.trans (p1.trans (p2.trans p3))⟩
    nlinarith

theorem frame_marker (pre bits : List Bool) (k : ℕ) (hk : k≤bits.length) :
    readTapeBit (pre++frame bits) (pre.length+2*k)=decide (k<bits.length) := by
  induction k generalizing pre bits with
  | zero =>
    cases bits <;> simp [frame,Streaming.read_append]
  | succ k ih =>
    cases bits with
    | nil => simp at hk
    | cons bit bits =>
      have h := ih (pre++[true,bit]) bits (by simp only [List.length_cons] at hk; omega)
      simpa [frame,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem payload_markers (pre bits : List Bool) (u count : ℕ) (hu : 0<u)
    (hbits : bits.length=2*u*count) :
    ∀ j≤count, readTapeBit (pre++frame bits) (pre.length+4*u*j)=decide (j<count) := by
  intro j hj
  have hb : 2*u*j≤bits.length := by rw [hbits]; exact Nat.mul_le_mul_left _ hj
  have hm := frame_marker pre bits (2*u*j) hb
  have he : pre.length+2*(2*u*j)=pre.length+4*u*j := by ring
  rw [he,hbits] at hm
  have hiff : 2*u*j<2*u*count ↔ j<count := Nat.mul_lt_mul_left (by omega : 0<2*u)
  simpa only [hiff] using hm

theorem count_run (pre bits : List Bool) (u count : ℕ) (hu : 0<u)
    (hbits : bits.length=2*u*count) :
    ∃ r : ExecutionReceipt 3 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine (count*(6*u+15)+7) (boundary 0 u (pre++frame bits) pre.length 0)=some r ∧
      r.final=result u (pre++frame bits) (pre.length+2*bits.length) count ∧
      r.steps≤count*(6*u+15)+7 := by
  obtain ⟨time,hbound,ht⟩ := loop_timed u (pre++frame bits) pre.length count 0 count
    (payload_markers pre bits u count hu hbits) (by omega)
  have he : pre.length+4*u*count=pre.length+2*bits.length := by rw [hbits]; ring
  rw [he] at ht
  simp only [Nat.mul_zero,Nat.add_zero] at ht
  obtain ⟨r,hr,hf,hs⟩ := ht.run (by simp [machine,result,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : time≤count*(6*u+15)+7 := by nlinarith
  have hm := runFrom_moreFuel machine time (count*(6*u+15)+7-time) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hf,hs.trans_le hb⟩

end NearCubicWires.RepairOrdinary.MatrixPayloadCount
