import Proof.MachineModel.OrdinaryMatrixBatchBucketBudget

/-! The actual positive-budget predecessor. Overwriting the first mark
creates the leading sentinel; the end scan allocates its false terminator. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketPredecessor
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => some false,fun _ => .right⟩
    else if q.val=1 then some (if bits 0 then
      ⟨1,fun _ => none,fun _ => .right⟩
      else ⟨2,fun _ => some false,fun _ => .left⟩)
    else if q.val=2 then some (if bits 0 then
      ⟨2,fun _ => none,fun _ => .left⟩
      else ⟨3,fun _ => none,fun _ => .stay⟩)
    else none
def cfg (q : Fin 4) (bits : List Bool) (pos : ℕ) : Configuration 1 4 :=
  ⟨q,fun _ => pos,fun _ => bits⟩
def short (c : ℕ) := false::List.replicate c true

theorem boot (c : ℕ) : step machine (cfg 0 (List.replicate (c+1) true) 0)=
    some (cfg 1 (short c) 1) := by
  simp [step,machine,cfg,List.replicate_succ,short]
  rfl
theorem forward (c pos : ℕ) (hp : pos<c) :
    step machine (cfg 1 (short c) (pos+1))=some (cfg 1 (short c) (pos+2)) := by
  have h : readTapeBit (short c) (pos+1)=true := by
    simp [short,readTapeBit,List.getD,hp]
  simp [step,machine,cfg,Configuration.scanned,h]
  rfl
theorem terminator (c : ℕ) : step machine (cfg 1 (short c) (c+1))=
    some (cfg 2 (UnaryTemplate.tape c) c) := by
  have hz : readTapeBit (short c) (c+1)=false := by simp [short,readTapeBit,List.getD]
  have hw : writeTapeBit (short c) (c+1) false=UnaryTemplate.tape c := by
    have hlen : (short c).length=c+1 := by simp [short]
    rw [←hlen,Streaming.write_append]
    rfl
  simp [step,machine,cfg,Configuration.scanned,hz]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · funext i; simp [applyAction,hw]
theorem backward (c pos : ℕ) (hp : pos<c) :
    step machine (cfg 2 (UnaryTemplate.tape c) (pos+1))=some (cfg 2 (UnaryTemplate.tape c) pos) := by
  have h := UnaryTemplate.tape_mark c pos hp
  simp [step,machine,cfg,Configuration.scanned,h]
  rfl
theorem stop (c : ℕ) : step machine (cfg 2 (UnaryTemplate.tape c) 0)=
    some (cfg 3 (UnaryTemplate.tape c) 0) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape]
  rfl
theorem scan (c pos remaining : ℕ) (h : pos+remaining≤c) :
    Timed machine remaining (cfg 1 (short c) (pos+1)) (cfg 1 (short c) (pos+remaining+1)) := by
  induction remaining generalizing pos with
  | zero => simp only [Nat.add_zero]; exact Timed.refl _ _
  | succ remaining ih =>
    have ht := ih (pos+1) (by omega)
    have hs := Timed.single (by rfl) (forward c pos (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 remaining] using hs.trans ht
theorem rewind (c pos : ℕ) (hp : pos≤c) :
    Timed machine (pos+1) (cfg 2 (UnaryTemplate.tape c) pos) (cfg 3 (UnaryTemplate.tape c) 0) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (stop c)
  | succ pos ih =>
    simpa only [Nat.add_comm 1] using
      (Timed.single (by rfl) (backward c pos (by omega))).trans (ih (by omega))

theorem predecessor_run (q : ℕ) (hq : 0<q) : RecoveryRootRound.ReadyRun machine (2*q+1)
    (fun _ => List.replicate q true) (fun _ => UnaryTemplate.tape (q-1)) := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  have h0 := Timed.single (by rfl) (boot c)
  have h1 := scan c 0 c (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := Timed.single (by rfl) (terminator c)
  have h3 := rewind c c (by omega)
  have hall := ((h0.trans h1).trans h2).trans h3
  have ht : ((1+c)+1)+(c+1)=2*(c+1)+1 := by omega
  rw [ht] at hall
  obtain ⟨actual,ha,hf,hs⟩ := hall.run (by rfl)
  exact ⟨actual,ha,by rw [hf]; rfl,by intro i; rw [hf]; rfl,hs⟩

end NearCubicWires.RepairOrdinary.MatrixBucketPredecessor
