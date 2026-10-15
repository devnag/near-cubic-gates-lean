import Proof.MachineModel.OrdinaryMatrixBatchBucketEndpoints

/-! Move back over one fixed-width ranked field using the actual H
sentinel. The source is never written, and the H driver is restored. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankFieldReverse
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 7 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==6
  rule := fun q bits => if q.val=0 then some ⟨1,fun _ => none,![.left,.right]⟩
    else if q.val=1 then some (if bits 1 then ⟨2,fun _ => none,![.left,.stay]⟩
      else ⟨5,fun _ => none,![.stay,.left]⟩)
    else if q.val=2 then some ⟨3,fun _ => none,![.left,.stay]⟩
    else if q.val=3 then some ⟨4,fun _ => none,![.left,.stay]⟩
    else if q.val=4 then some ⟨1,fun _ => none,![.left,.right]⟩
    else if q.val=5 then some (if bits 1 then ⟨5,fun _ => none,![.stay,.left]⟩
      else ⟨6,fun _ => none,fun _ => .stay⟩)
    else none
def cfg (q : Fin 7) (source : List Bool) (H pos k : ℕ) : Configuration 2 7 :=
  ⟨q,![pos,k],![source,UnaryTemplate.tape H]⟩
def distance (H : ℕ) := 4*H+1
def budget (H : ℕ) := 5*H+3

theorem boot (source : List Bool) (H pos : ℕ) :
    step machine (cfg 0 source H pos 0)=some (cfg 1 source H (pos-1) 1) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem first (source : List Bool) (H pos k : ℕ) (hk : k<H) :
    step machine (cfg 1 source H pos (k+1))=some (cfg 2 source H (pos-1) (k+1)) := by
  have h := UnaryTemplate.tape_mark H k hk
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem second (source : List Bool) (H pos k : ℕ) :
    step machine (cfg 2 source H pos k)=some (cfg 3 source H (pos-1) k) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem third (source : List Bool) (H pos k : ℕ) :
    step machine (cfg 3 source H pos k)=some (cfg 4 source H (pos-1) k) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem fourth (source : List Bool) (H pos k : ℕ) :
    step machine (cfg 4 source H pos (k+1))=some (cfg 1 source H (pos-1) (k+2)) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem cycle_timed (source : List Bool) (H pos k : ℕ) (hk : k<H) :
    Timed machine 4 (cfg 1 source H pos (k+1)) (cfg 1 source H (pos-4) (k+2)) := by
  have h0 := Timed.single (by rfl) (first source H pos k hk)
  have h1 := Timed.single (by rfl) (second source H (pos-1) (k+1))
  have h2 := Timed.single (by rfl) (third source H (pos-1-1) (k+1))
  have h3 := Timed.single (by rfl) (fourth source H (pos-1-1-1) k)
  simpa only [Nat.sub_sub] using ((h0.trans h1).trans h2).trans h3
theorem return_start (source : List Bool) (H pos : ℕ) :
    step machine (cfg 1 source H pos (H+1))=some (cfg 5 source H pos H) := by
  have h := UnaryTemplate.tape_end H
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem back (source : List Bool) (H pos k : ℕ) (hk : k<H) :
    step machine (cfg 5 source H pos (k+1))=some (cfg 5 source H pos k) := by
  have h := UnaryTemplate.tape_mark H k hk
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem stop (source : List Bool) (H pos : ℕ) :
    step machine (cfg 5 source H pos 0)=some (cfg 6 source H pos 0) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape]
  rfl
theorem scan (source : List Bool) (H pos k remaining : ℕ) (hk : k+remaining≤H) :
    Timed machine (4*remaining) (cfg 1 source H pos (k+1))
      (cfg 1 source H (pos-4*remaining) (k+remaining+1)) := by
  induction remaining generalizing pos k with
  | zero => simp only [Nat.mul_zero,Nat.sub_zero,Nat.add_zero]; exact Timed.refl _ _
  | succ remaining ih =>
    have ht := ih (pos-4) (k+1) (by omega)
    have head := cycle_timed source H pos k (by omega)
    simpa [Nat.mul_add,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using head.trans ht
theorem rewind (source : List Bool) (H pos k : ℕ) (hk : k≤H) :
    Timed machine (k+1) (cfg 5 source H pos k) (cfg 6 source H pos 0) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop source H pos)
  | succ k ih =>
    simpa only [Nat.add_comm 1] using
      (Timed.single (by rfl) (back source H pos k (by omega))).trans (ih (by omega))

theorem reverse_run (source : List Bool) (H pos : ℕ) :
    ∃ actual,runFrom machine (budget H) (cfg 0 source H pos 0)=some actual ∧
      actual.final=cfg 6 source H (pos-distance H) 0 ∧ actual.steps=budget H := by
  have h0 := Timed.single (by rfl) (boot source H pos)
  have h1 := scan source H (pos-1) 0 H (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := Timed.single (by rfl) (return_start source H (pos-1-4*H))
  have h3 := rewind source H (pos-1-4*H) H (by omega)
  have whole := ((h0.trans h1).trans h2).trans h3
  have ht : (1+4*H)+1+(H+1)=budget H := by unfold budget; omega
  have hp : pos-1-4*H=pos-distance H := by unfold distance; omega
  rw [ht,hp] at whole
  exact whole.run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixRankFieldReverse
