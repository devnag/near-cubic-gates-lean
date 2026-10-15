import Proof.MachineModel.OrdinaryMatrixMaskPad

/-! The AND-row consumer returns its mask and width sentinel together.
No fresh log or reset-capacity input is needed between rows; only these two
local heads move, preserving the global left/output cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskAndReturn
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (count dh mh : ℕ) (mask source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 4 s :=
  ⟨q,![dh,mh,pos,out.length],![UnaryTemplate.tape count,mask,source,out]⟩
def machine : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then some ⟨1,fun _ => none,![.left,.stay,.stay,.stay]⟩
    else if q.val=1 then some (if scan 0 then ⟨1,fun _ => none,![.left,.left,.stay,.stay]⟩
      else ⟨2,fun _ => none,![.right,.stay,.stay,.stay]⟩) else none

theorem start_step (count : ℕ) (mask source out : List Bool) (pos : ℕ) :
    step machine (cfg 0 count (count+1) count mask source pos out)=
      some (cfg 1 count count count mask source pos out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_step (count n : ℕ) (hn : n<count) (mask source out : List Bool) (pos : ℕ) :
    step machine (cfg 1 count (n+1) (n+1) mask source pos out)=
      some (cfg 1 count n n mask source pos out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark count n hn]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (count : ℕ) (mask source out : List Bool) (pos : ℕ) :
    step machine (cfg 1 count 0 0 mask source pos out)=some (cfg 2 count 1 0 mask source pos out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem return_prefix (count n : ℕ) (hn : n≤count) (mask source out : List Bool) (pos : ℕ) :
    Timed machine (n+1) (cfg 1 count n n mask source pos out) (cfg 2 count 1 0 mask source pos out) := by
  induction n with
  | zero => exact Timed.single (by rfl) (stop_step count mask source out pos)
  | succ n ih =>
    have h := (Timed.single (by rfl) (back_step count n (by omega) mask source out pos)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem reset_run (count : ℕ) (mask source out : List Bool) (pos : ℕ) : ∃ actual,
    runFrom machine (count+2) (cfg 0 count (count+1) count mask source pos out)=some actual ∧
    actual.final=cfg 2 count 1 0 mask source pos out ∧ actual.steps=count+2 := by
  have h := (Timed.single (by rfl) (start_step count mask source out pos)).trans
    (return_prefix count count le_rfl mask source out pos)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixMaskAndReturn
