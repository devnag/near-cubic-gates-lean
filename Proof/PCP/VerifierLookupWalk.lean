import Proof.PCP.VerifierDecodingSequential
import Proof.MachineModel.OrdinaryTransitionArrayReuse

/-! A paid two-cell-per-mark source walk with its unary driver restored.
Left walks restore a retained witness cursor without resetting it to zero. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupWalk
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shift (move : HeadMove) (pos n : ℕ) : ℕ :=
  match move with | .left => pos-n | .stay => pos | .right => pos+n

theorem shift_zero (move : HeadMove) (pos : ℕ) : shift move pos 0=pos := by cases move <;> simp [shift]
theorem shift_one (move : HeadMove) (pos : ℕ) : shift move pos 1=HeadMove.apply move pos := by
  cases move <;> rfl
theorem shift_add (move : HeadMove) (pos a b : ℕ) : shift move (shift move pos a) b=shift move pos (a+b) := by
  cases move <;> simp [shift,Nat.sub_sub,Nat.add_assoc]

def machine (move : HeadMove) : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
    if bits 1 then some ⟨1,fun _ => none,![move,.right]⟩
    else some ⟨2,fun _ => none,![.stay,.left]⟩
    else if q.val=1 then some ⟨0,fun _ => none,![move,.stay]⟩
    else if q.val=2 then
      if bits 1 then some ⟨2,fun _ => none,![.stay,.left]⟩
      else some ⟨3,fun _ => none,![.stay,.right]⟩
    else none

def cfg (q : Fin 4) (source : List Bool) (pos total driver : ℕ) : Configuration 2 4 :=
  ⟨q,![pos,driver],![source,CompareMachine.word total]⟩

theorem first_step (move : HeadMove) (source : List Bool) (pos total done : ℕ) (h : done<total) :
    step (machine move) (cfg 0 source pos total (done+1))=
      some (cfg 1 source (HeadMove.apply move pos) total (done+2)) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.read_mark,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem second_step (move : HeadMove) (source : List Bool) (pos total driver : ℕ) :
    step (machine move) (cfg 1 source pos total driver)=
      some (cfg 0 source (HeadMove.apply move pos) total driver) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem stop_step (move : HeadMove) (source : List Bool) (pos total : ℕ) :
    step (machine move) (cfg 0 source pos total (total+1))=some (cfg 2 source pos total total) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem forward_prefix (move : HeadMove) (source : List Bool) (n total done pos : ℕ) (h : done+n=total) :
    Timed (machine move) (2*n+1) (cfg 0 source pos total (done+1))
      (cfg 2 source (shift move pos (2*n)) total total) := by
  induction n generalizing done pos with
  | zero =>
    have he : done=total := by omega
    subst done
    simpa [shift_zero] using Timed.single (by rfl : (machine move).halted (0 : Fin 4)=false)
      (stop_step move source pos total)
  | succ n ih =>
    have hfirst := Timed.single (by rfl : (machine move).halted (0 : Fin 4)=false)
      (first_step move source pos total done (by omega))
    have hsecond := Timed.single (by rfl : (machine move).halted (1 : Fin 4)=false)
      (second_step move source (HeadMove.apply move pos) total (done+2))
    have ht := ih (done+1) (HeadMove.apply move (HeadMove.apply move pos)) (by omega)
    have hp : shift move (HeadMove.apply move (HeadMove.apply move pos)) (2*n)=shift move pos (2*(n+1)) := by
      rw [←shift_one,←shift_one,shift_add,shift_add]
      congr 1
      omega
    rw [hp] at ht
    have hj := hfirst.trans (hsecond.trans ht)
    have htime : 1+(1+(2*n+1))=2*(n+1)+1 := by omega
    rw [htime] at hj
    exact hj

theorem rewind_step (move : HeadMove) (source : List Bool) (pos total k : ℕ) (h : k<total) :
    step (machine move) (cfg 2 source pos total (k+1))=some (cfg 2 source pos total k) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.read_mark,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem finish_step (move : HeadMove) (source : List Bool) (pos total : ℕ) :
    step (machine move) (cfg 2 source pos total 0)=some (cfg 3 source pos total 1) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.word,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem rewind_prefix (move : HeadMove) (source : List Bool) (pos total k : ℕ) (h : k≤total) :
    Timed (machine move) (k+1) (cfg 2 source pos total k) (cfg 3 source pos total 1) := by
  induction k with
  | zero => exact Timed.single (by rfl) (finish_step move source pos total)
  | succ k ih =>
    have hj := (Timed.single (by rfl : (machine move).halted (2 : Fin 4)=false)
      (rewind_step move source pos total k (by omega))).trans (ih (by omega))
    simpa only [Nat.add_comm 1] using hj

theorem walk_run (move : HeadMove) (source : List Bool) (pos n : ℕ) :
    ∃ r,runFrom (machine move) (3*n+2) (cfg 0 source pos n 1)=some r ∧
      r.final=cfg 3 source (shift move pos (2*n)) n 1 ∧ r.steps=3*n+2 := by
  have hj := (forward_prefix move source n n 0 pos (by omega)).trans
    (rewind_prefix move source (shift move pos (2*n)) n n (Nat.le_refl _))
  have htime : (2*n+1)+(n+1)=3*n+2 := by omega
  rw [htime] at hj
  exact hj.run (by rfl)

end NearCubicWires.RepairSource.VerifierDecoding.LookupWalk
