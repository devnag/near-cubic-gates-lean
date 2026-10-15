import Proof.MachineModel.UMemoryCloseChecker

/-! The fixed final branch: one actual control transition selects the
existing checker or a physical false write on the fresh result tape.
Every call return and final stop is charged. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def branchIdle (t : ℕ) : Machine ((t+1)+20) 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

def reject (t : ℕ) : Machine ((t+1)+20) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val=0 then some
    ⟨1,fun i => if i=resultSlot t then some false else none,fun _ => .stay⟩ else none

def rejected {t s : ℕ} (c : Configuration ((t+1)+20) s) : Configuration ((t+1)+20) 2 :=
  ⟨1,c.heads,fun i => if i=resultSlot t then writeTapeBit (c.tapes i) (c.heads i) false else c.tapes i⟩

theorem reject_run {t s : ℕ} (c : Configuration ((t+1)+20) s) :
    ∃ r,runFrom (reject t) 1 (Composition.restart c (reject t).start)=some r ∧
      r.final=rejected c ∧ r.steps=1 := by
  have hs : step (reject t) (Composition.restart c 0)=some (rejected c) := by
    simp only [step,reject,Composition.restart,Fin.val_zero,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      simp only [applyAction,HeadMove.apply,rejected]
    · funext i
      simp only [applyAction,rejected]
      split_ifs <;> rfl
  exact (Timed.single (by rfl : (reject t).halted (0 : Fin 2)=false) hs).run (by rfl)

def finishSizes : Fin 3 → ℕ := ![1,138,2]
noncomputable def finishPrograms {t : ℕ} (event : Fin t) : (j : Fin 3) → Machine ((t+1)+20) (finishSizes j)
  | 0 => branchIdle t
  | 1 => checkerProgram event
  | 2 => reject t
def finishNext {t : ℕ} (flag : Fin t) (j : Fin 3) (_ : Fin (finishSizes j))
    (bits : Fin ((t+1)+20) → Bool) : Option (Fin 3) :=
  if j.val=0 then if bits (oldSlot flag) then some 1 else some 2 else none
noncomputable def finishMachine {t : ℕ} (event flag : Fin t) :=
  RecoveryCalls.machine finishSizes (finishPrograms event) 0 (finishNext flag)

theorem finish_branch {t s : ℕ} (event flag : Fin t) (c : Configuration ((t+1)+20) s)
    (b : Bool) (hb : c.scanned (oldSlot flag)=b) :
    let node : Fin 3 := if b then 1 else 2
    Timed (finishMachine event flag) 1
      (Composition.restart c (finishMachine event flag).start)
      (controlConfig (RecoveryCalls.code finishSizes node)
        (Composition.restart c (finishPrograms event node).start)) := by
  dsimp only
  have hs := RecoveryCalls.return_step finishSizes (finishPrograms event) 0 (finishNext flag) 0
    (if b then 1 else 2) (Composition.restart c (0 : Fin 1)) (by rfl)
    (by
      change (if c.scanned (oldSlot flag) then some 1 else some 2)=
        some (if b then 1 else 2)
      rw [hb]
      cases b <;> rfl)
  exact Timed.single (by simp [finishMachine,RecoveryCalls.machine,RecoveryCalls.code,
    Composition.restart]) hs

theorem finish_stop {t : ℕ} (event flag : Fin t) (j : Fin 3) (hj : j ≠ 0)
    (fuel : ℕ) (c : Configuration ((t+1)+20) (finishSizes j))
    (r : ExecutionReceipt ((t+1)+20) (finishSizes j))
    (hr : runFrom (finishPrograms event j) fuel c=some r) :
    ∃ time≤fuel+1,Timed (finishMachine event flag) time
      (controlConfig (RecoveryCalls.code finishSizes j) c)
      (RecoveryCalls.stopped finishSizes r.final.heads r.final.tapes) := by
  apply RecoveryRootRound.stop_receipt finishSizes (finishPrograms event) 0 (finishNext flag) j fuel c r hr
  have hval : j.val ≠ 0 := by intro h; exact hj (Fin.ext h)
  simp only [finishNext,hval,↓reduceIte]

theorem finish_failure {t s : ℕ} (event flag : Fin t) (c : Configuration ((t+1)+20) s)
    (hflag : c.scanned (oldSlot flag)=false)
    (hresult : c.tapes (resultSlot t)=[]) (hhead : c.heads (resultSlot t)=0) :
    ∃ r,runFrom (finishMachine event flag) 3
      (Composition.restart c (finishMachine event flag).start)=some r ∧
      r.final.tapes (resultSlot t)=[false] ∧ r.final.heads (resultSlot t)=0 ∧
      (∀ i : Fin t, r.final.heads (oldSlot i)=c.heads (oldSlot i) ∧
        r.final.tapes (oldSlot i)=c.tapes (oldSlot i)) := by
  have hbranch := finish_branch event flag c false hflag
  obtain ⟨tail,ht,htf,_⟩ := reject_run c
  obtain ⟨time,htime,hpath⟩ := finish_stop event flag 2 (by decide) 1 _ tail ht
  have hp := hbranch.trans hpath
  obtain ⟨r,hr,hrf,_⟩ := hp.run (by simp [finishMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hmore := runFrom_moreFuel (finishMachine event flag) (1+time) (3-(1+time)) _ r hr
  rw [Nat.add_sub_of_le (by omega)] at hmore
  refine ⟨r,hmore,?_,?_,?_⟩
  · rw [hrf]
    change tail.final.tapes (resultSlot t)=[false]
    rw [htf]
    simp [rejected,hresult,hhead,writeTapeBit]
  · rw [hrf]
    change tail.final.heads (resultSlot t)=0
    rw [htf]
    exact hhead
  · intro i
    have hi : oldSlot i ≠ resultSlot t := by
      intro he
      have hv := congrArg (fun k : Fin ((t+1)+20) => k.val) he
      simp only [oldSlot,resultSlot,scratchSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
      have h := i.isLt
      omega
    rw [hrf]
    change tail.final.heads (oldSlot i)=_ ∧ tail.final.tapes (oldSlot i)=_
    rw [htf]
    simp [rejected,hi]

theorem finish_success {t s : ℕ} (event flag : Fin t) (req : MemoryChecker.Request)
    (c : Configuration ((t+1)+20) s) (hflag : c.scanned (oldSlot flag)=true)
    (hheads : ∀ j, c.heads (checkerSlots event j)=0)
    (htapes : ∀ j, c.tapes (checkerSlots event j)=SourceHandoff.sourceTapes req.input j) :
    ∃ r,runFrom (finishMachine event flag) (MemoryChecker.rawBudget req+2)
      (Composition.restart c (finishMachine event flag).start)=some r ∧
      r.final.tapes (resultSlot t)=[req.result] ∧ r.final.heads (resultSlot t)=0 ∧
      (∀ i : Fin t, i ≠ event → r.final.heads (oldSlot i)=c.heads (oldSlot i) ∧
        r.final.tapes (oldSlot i)=c.tapes (oldSlot i)) := by
  have hbranch := finish_branch event flag c true hflag
  obtain ⟨tail,ht,htt,hth,hother⟩ := checker_run event req c hheads htapes
  obtain ⟨time,htime,hpath⟩ := finish_stop event flag 1 (by decide) (MemoryChecker.rawBudget req) _ tail ht
  have hp := hbranch.trans hpath
  obtain ⟨r,hr,hrf,_⟩ := hp.run (by simp [finishMachine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hmore := runFrom_moreFuel (finishMachine event flag) (1+time)
    ((MemoryChecker.rawBudget req+2)-(1+time)) _ r hr
  rw [Nat.add_sub_of_le (by omega)] at hmore
  refine ⟨r,hmore,?_,?_,?_⟩
  · rw [hrf]
    exact htt
  · rw [hrf]
    exact hth
  · rw [hrf]
    exact hother

end NearCubicWires.RepairOrdinary.UMemoryClose
