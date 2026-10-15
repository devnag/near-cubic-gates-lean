import Proof.MachineModel.OrdinaryMatrixUnaryBodies

/-! The finite numeric-dimension expansion loop. The binary comparison
chooses the branch; each unsuccessful round executes one increment and
physically appends one unary mark. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 4 → ℕ := ![7,5,2,5]
noncomputable def programs (j : Fin 4) : Machine 5 (sizes j) := by
  refine Fin.cases compare ?_ j
  intro k
  refine Fin.cases increment ?_ k
  intro l
  refine Fin.cases emit ?_ l
  intro last
  have he : last=0 := Subsingleton.elim _ _
  subst last
  exact finish
def next (j : Fin 4) (_ : Fin (sizes j)) (bits : Fin 5 → Bool) : Option (Fin 4) :=
  if j=0 then if bits 2 then some 3 else some 1
  else if j=1 then some 2 else if j=2 then some 0 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (j : Fin 4) (w n a k : ℕ) (flag : Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (config (programs j).start w n a k flag)
noncomputable def result (w n : ℕ) :=
  RecoveryCalls.stopped sizes (finished (s:=5) 4 w n).heads (finished (s:=5) 4 w n).tapes

theorem compare_continue (w n a k : ℕ) (hn : n<2^w) (ha : a<n) :
    ∃ time≤4*w+5, Timed machine time (boundary 0 w n a k false) (boundary 1 w n a k false) := by
  obtain ⟨r,hr,hf,_⟩ := compare_run w n a k hn (by omega)
  have he : decide (n≤a)=false := by simp [show ¬n≤a by omega]
  rw [he] at hf
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 0 1 (4*w+4)
    (config (programs 0).start w n a k false) r hr (by rw [hf]; rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem compare_finish (w n : ℕ) (hn : n<2^w) :
    ∃ time≤4*w+5, Timed machine time (boundary 0 w n n n false) (boundary 3 w n n n true) := by
  obtain ⟨r,hr,hf,_⟩ := compare_run w n n n hn hn
  have he : decide (n≤n)=true := by simp
  rw [he] at hf
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 0 3 (4*w+4)
    (config (programs 0).start w n n n false) r hr (by rw [hf]; rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem increment_call (w n a k : ℕ) (ha : a+1<2^w) :
    ∃ time≤4*w+3, Timed machine time (boundary 1 w n a k false) (boundary 2 w n (a+1) k false) := by
  obtain ⟨r,hr,hf,_⟩ := increment_run w n a k false ha
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 1 2 (4*w+2)
    (config (programs 1).start w n a k false) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem emit_call (w n a k : ℕ) :
    ∃ time≤2, Timed machine time (boundary 2 w n a k false) (boundary 0 w n a (k+1) false) := by
  obtain ⟨r,hr,hf,_⟩ := emit_run w n a k false
  obtain ⟨time,hbound,ht⟩ := call_receipt sizes programs 0 next 2 0 1
    (config (programs 2).start w n a k false) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem finish_call (w n : ℕ) :
    ∃ time≤n+5, Timed machine time (boundary 3 w n n n true) (result w n) := by
  obtain ⟨r,hr,hf,_⟩ := finish_run w n
  obtain ⟨time,hbound,ht⟩ := stop_receipt sizes programs 0 next 3 (n+4)
    (config (programs 3).start w n n n true) r hr (by rfl)
  rw [hf] at ht
  exact ⟨time,by omega,ht⟩

theorem round_timed (w n a : ℕ) (hn : n<2^w) (ha : a<n) :
    ∃ time≤8*w+10, Timed machine time (boundary 0 w n a a false)
      (boundary 0 w n (a+1) (a+1) false) := by
  obtain ⟨t0,h0,p0⟩ := compare_continue w n a a hn ha
  obtain ⟨t1,h1,p1⟩ := increment_call w n a a (by omega)
  obtain ⟨t2,h2,p2⟩ := emit_call w n (a+1) a
  exact ⟨t0+(t1+t2),by omega,p0.trans (p1.trans p2)⟩

theorem loop_timed (w n a remaining : ℕ) (hn : n<2^w) (he : a+remaining=n) :
    ∃ time≤remaining*(8*w+10)+4*w+n+10,
      Timed machine time (boundary 0 w n a a false) (result w n) := by
  induction remaining generalizing a with
  | zero =>
    have ha : a=n := by omega
    subst a
    obtain ⟨t0,h0,p0⟩ := compare_finish w n hn
    obtain ⟨t1,h1,p1⟩ := finish_call w n
    exact ⟨t0+t1,by omega,p0.trans p1⟩
  | succ remaining ih =>
    obtain ⟨t0,h0,p0⟩ := round_timed w n a hn (by omega)
    obtain ⟨t1,h1,p1⟩ := ih (a+1) (by omega)
    refine ⟨t0+t1,?_,p0.trans p1⟩
    nlinarith

theorem loop_run (w n : ℕ) (hn : n<2^w) :
    ∃ r : ExecutionReceipt 5 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine (n*(8*w+10)+4*w+n+10) (boundary 0 w n 0 0 false)=some r ∧
      r.final=result w n ∧ r.steps≤n*(8*w+10)+4*w+n+10 := by
  obtain ⟨time,hbound,ht⟩ := loop_timed w n 0 n hn (by omega)
  obtain ⟨r,hr,hf,hs⟩ := ht.run (by simp [machine,result,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel machine time ((n*(8*w+10)+4*w+n+10)-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at hm
  exact ⟨r,hm,hf,hs.trans_le hbound⟩

end NearCubicWires.RepairOrdinary.MatrixUnary
