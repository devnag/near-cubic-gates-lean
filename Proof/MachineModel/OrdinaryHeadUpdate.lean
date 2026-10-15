import Proof.MachineModel.OrdinaryHeadUpdateTapes

/-! One actual head-update program dispatches on the two physical move bits.
Left at zero saturates, positive left subtracts and copies, right increments,
and stay preserves the head. Every branch restores the retained local tapes. -/
namespace NearCubicWires.RepairOrdinary.HeadUpdate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 5 → ℕ := ![2,7,7,6,5]
noncomputable def programs : (j : Fin 5) → Machine 8 (sizes j)
  | ⟨0,_⟩ => clearMachine
  | ⟨1,_⟩ => compareProgram
  | ⟨2,_⟩ => subtractProgram
  | ⟨3,_⟩ => copyProgram
  | ⟨4,_⟩ => incrementProgram
  | ⟨n+5,h⟩ => False.elim (by omega)

def next (j : Fin 5) (_ : Fin (sizes j)) (bits : Fin 8 → Bool) : Option (Fin 5) :=
  if j.val=0 then
    if bits 7 then some 4 else if bits 6 then none else some 1
  else if j.val=1 then if bits 3 then some 2 else none
  else if j.val=2 then some 3
  else none

noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def finished (s : Store) (w : ℕ) : Store :=
  match s.move with
  | .left => if s.head=0 then compared s else copied (subtracted (compared s) w)
  | .stay => cleared s
  | .right => incremented (cleared s)

private theorem ready_of_path (s : Store) (w cap n : ℕ)
    (hp : Timed machine n (initialConfiguration machine (s.tapes w cap))
      (RecoveryCalls.stopped sizes (fun _ => 0) ((finished s w).tapes w cap))) :
    ReadyRun machine n (s.tapes w cap) ((finished s w).tapes w cap) := by
  obtain ⟨r,hr,hf,hs⟩ := hp.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],
    by intro i; simp [hf,RecoveryCalls.stopped],hs⟩

theorem update_ready (s : Store) (w cap : ℕ) (ha : s.head+1<2^w)
    (hb : s.difference.length≤2*w+1) (hc : 4*w+3≤cap) :
    ∃ n≤20*(w+2), ReadyRun machine n (s.tapes w cap) ((finished s w).tapes w cap) := by
  have ha' : s.head<2^w := by omega
  have hw : 1<2^w := by omega
  have hc' : 2*w+1≤cap := by omega
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs 0) (s.tapes w cap)) =
      initialConfiguration machine (s.tapes w cap) := by rfl
  cases hm : s.move with
  | left =>
    have hclear := (clear_ready s w cap).call sizes programs 0 next 0 1
      (by intro q; simp [next,Store.tapes,cleared,hm,low,high,readTapeBit,List.getD])
    have hcompare := compare_layout s w cap ha' hw hc'
    by_cases hz : s.head=0
    · have hlast := hcompare.stop sizes programs 0 next 1
        (by intro q; simp [next,Store.tapes,compared,hz,readTapeBit,List.getD])
      have h := hclear.trans hlast
      rw [hin] at h
      have hp : Timed machine (4*w+7) (initialConfiguration machine (s.tapes w cap))
          (RecoveryCalls.stopped sizes (fun _ => 0) ((finished s w).tapes w cap)) := by
        have ht : (1+1)+(4*w+4+1)=4*w+7 := by omega
        rw [ht] at h
        simpa only [finished,hm,hz,↓reduceIte,machine] using h
      exact ⟨4*w+7,by omega,ready_of_path s w cap _ hp⟩
    · have hpos : 1 ≤ s.head := by omega
      have hcomp := hcompare.call sizes programs 0 next 1 2
        (by intro q; simp [next,Store.tapes,compared,hpos,readTapeBit,List.getD])
      have hsub := (subtract_layout (compared s) w cap ha' hpos hb hc').call
        sizes programs 0 next 2 3 (by intro q; rfl)
      have hcopy := (copy_layout (compared s) w cap hc).stop
        sizes programs 0 next 3 (by intro q; rfl)
      have h := ((hclear.trans hcomp).trans hsub).trans hcopy
      rw [hin] at h
      have hp : Timed machine (16*w+21) (initialConfiguration machine (s.tapes w cap))
          (RecoveryCalls.stopped sizes (fun _ => 0) ((finished s w).tapes w cap)) := by
        have ht : (((1+1)+(4*w+4+1))+(4*w+4+1))+(8*w+8+1)=16*w+21 := by omega
        rw [ht] at h
        simpa only [finished,hm,hz,↓reduceIte,machine] using h
      exact ⟨16*w+21,by omega,ready_of_path s w cap _ hp⟩
  | stay =>
    have h := (clear_ready s w cap).stop sizes programs 0 next 0
      (by intro q; simp [next,Store.tapes,cleared,hm,low,high,readTapeBit,List.getD])
    rw [hin] at h
    have hp : Timed machine 2 (initialConfiguration machine (s.tapes w cap))
        (RecoveryCalls.stopped sizes (fun _ => 0) ((finished s w).tapes w cap)) := by
      simpa only [finished,hm,machine] using h
    exact ⟨2,by omega,ready_of_path s w cap _ hp⟩
  | right =>
    have hclear := (clear_ready s w cap).call sizes programs 0 next 0 4
      (by intro q; simp [next,Store.tapes,cleared,hm,low,high,readTapeBit,List.getD])
    obtain ⟨n,hn,hi⟩ := increment_layout (cleared s) w cap ha (by omega)
    have h := hclear.trans (hi.stop sizes programs 0 next 4 (by intro q; rfl))
    rw [hin] at h
    have hp : Timed machine (n+3) (initialConfiguration machine (s.tapes w cap))
        (RecoveryCalls.stopped sizes (fun _ => 0) ((finished s w).tapes w cap)) := by
      have ht : (1+1)+(n+1)=n+3 := by omega
      rw [ht] at h
      simpa only [finished,hm,machine] using h
    exact ⟨n+3,by omega,ready_of_path s w cap _ hp⟩

theorem finished_head (s : Store) (w : ℕ) :
    (finished s w).head=HeadMove.apply s.move s.head := by
  cases hm : s.move <;> simp [finished,hm,compared,copied,subtracted,cleared,incremented,HeadMove.apply]
  split <;> simp_all

theorem finished_difference_bound (s : Store) (w : ℕ) (hb : s.difference.length≤2*w+1) :
    (finished s w).difference.length≤2*w+1 := by
  cases hm : s.move <;> simp only [finished,hm,cleared,incremented] <;> try exact hb
  split
  · exact hb
  · simp [copied,subtracted,SignedSortKey.binary_length]

theorem update_run (s : Store) (w cap : ℕ) (ha : s.head+1<2^w)
    (hb : s.difference.length≤2*w+1) (hc : 4*w+3≤cap) :
    ∃ r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)),
      run machine (20*(w+2)) (s.tapes w cap)=some r ∧
      r.final.tapes=(finished s w).tapes w cap ∧ (∀ i,r.final.heads i=0) ∧
      r.steps≤20*(w+2) := by
  obtain ⟨n,hn,r,hr,ht,hh,hs⟩ := update_ready s w cap ha hb hc
  have h := run_moreFuel machine n (20*(w+2)-n) _ r hr
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨r,h,ht,hh,by omega⟩

end NearCubicWires.RepairOrdinary.HeadUpdate
