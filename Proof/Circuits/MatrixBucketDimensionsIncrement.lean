import Proof.Circuits.MatrixBucketDimensionsBounds

/-! The unary candidate is advanced in place, including allocation of its
new false terminator and physical return to head zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Increment
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bits => if q.val=0 then some ⟨1,fun _ => none,fun _ => .right⟩
    else if q.val=1 then some (if bits 0 then ⟨1,fun _ => none,fun _ => .right⟩
      else ⟨2,fun _ => some true,fun _ => .right⟩)
    else if q.val=2 then some ⟨3,fun _ => some false,fun _ => .left⟩
    else if q.val=3 then some (if bits 0 then ⟨3,fun _ => none,fun _ => .left⟩
      else ⟨4,fun _ => none,fun _ => .stay⟩)
    else none
def cfg (q : Fin 5) (bits : List Bool) (pos : ℕ) : Configuration 1 5 :=
  ⟨q,fun _ => pos,fun _ => bits⟩
def grown (c : ℕ) := false::List.replicate (c+1) true

theorem boot (c : ℕ) : step machine (cfg 0 (UnaryTemplate.tape c) 0)=
    some (cfg 1 (UnaryTemplate.tape c) 1) := by rfl
theorem forward (c pos : ℕ) (hp : pos<c) :
    step machine (cfg 1 (UnaryTemplate.tape c) (pos+1))=
      some (cfg 1 (UnaryTemplate.tape c) (pos+2)) := by
  have h := UnaryTemplate.tape_mark c pos hp
  simp [step,machine,cfg,Configuration.scanned,h]
  rfl
theorem grow_write (c : ℕ) : writeTapeBit (UnaryTemplate.tape c) (c+1) true=grown c := by
  unfold UnaryTemplate.tape grown
  simp only [writeTapeBit]
  congr 1
  induction c with
  | zero => rfl
  | succ c ih => simpa [List.replicate_succ,writeTapeBit] using congrArg (List.cons true) ih
theorem grow_step (c : ℕ) : step machine (cfg 1 (UnaryTemplate.tape c) (c+1))=
    some (cfg 2 (grown c) (c+2)) := by
  have hz := UnaryTemplate.tape_end c
  simp [step,machine,cfg,Configuration.scanned,hz]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; simp [applyAction,grow_write]
theorem terminator (c : ℕ) : step machine (cfg 2 (grown c) (c+2))=
    some (cfg 3 (UnaryTemplate.tape (c+1)) (c+1)) := by
  have hw : writeTapeBit (grown c) (c+2) false=UnaryTemplate.tape (c+1) := by
    have hlen : (grown c).length=c+2 := by simp [grown]
    rw [← hlen,Streaming.write_append]
    rfl
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · funext i; simp [applyAction,hw]
theorem backward (c pos : ℕ) (hp : pos<c) : step machine (cfg 3 (UnaryTemplate.tape c) (pos+1))=
    some (cfg 3 (UnaryTemplate.tape c) pos) := by
  have h := UnaryTemplate.tape_mark c pos hp
  simp [step,machine,cfg,Configuration.scanned,h]
  rfl
theorem stop (c : ℕ) : step machine (cfg 3 (UnaryTemplate.tape c) 0)=
    some (cfg 4 (UnaryTemplate.tape c) 0) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape]
  rfl

theorem scan (c pos remaining : ℕ) (h : pos+remaining≤c) :
    Timed machine remaining (cfg 1 (UnaryTemplate.tape c) (pos+1))
      (cfg 1 (UnaryTemplate.tape c) (pos+remaining+1)) := by
  induction remaining generalizing pos with
  | zero => simp; exact Timed.refl _ _
  | succ remaining ih =>
    have ht := ih (pos+1) (by omega)
    have hs := Timed.single (by rfl) (forward c pos (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans ht
theorem rewind (c pos : ℕ) (hp : pos≤c) :
    Timed machine (pos+1) (cfg 3 (UnaryTemplate.tape c) pos) (cfg 4 (UnaryTemplate.tape c) 0) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (stop c)
  | succ pos ih =>
    simpa only [Nat.add_comm 1] using
      (Timed.single (by rfl) (backward c pos (by omega))).trans (ih (by omega))

theorem increment_run (c : ℕ) : RecoveryRootRound.ReadyRun machine (2*c+5)
    (fun _ => UnaryTemplate.tape c) (fun _ => UnaryTemplate.tape (c+1)) := by
  have h0 := Timed.single (by rfl) (boot c)
  have h1 := scan c 0 c (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := Timed.single (by rfl) (grow_step c)
  have h3 := Timed.single (by rfl) (terminator c)
  have h4 := rewind (c+1) (c+1) (by omega)
  have hall := (((h0.trans h1).trans h2).trans h3).trans h4
  have ht : (((1+c)+1)+1)+(c+1+1)=2*c+5 := by omega
  rw [ht] at hall
  obtain ⟨r,hr,hf,hs⟩ := hall.run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,by intro i; rw [hf]; rfl,hs⟩

end NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Increment
