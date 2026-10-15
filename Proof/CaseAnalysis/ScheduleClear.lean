import Proof.CaseAnalysis.CloseoutScheduleColdCapacity

/-! A paid initial sweep creates the schedule workspace, zero best field
and complete reset log from genuinely blank cells and the actual C driver. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def clearProgram (w : Nat) := RecoveryFocus.machine (clearSlots w) (RecoveryScratchErase.resetMachine (w+1))
def bestIndex (w : Nat) : Fin (w+3) := (((0 : Fin 1).natAdd w).castAdd 1).castAdd 1
def driverIndex (w : Nat) : Fin (w+3) := ((0 : Fin 1).natAdd (w+1)).castAdd 1
def logIndex (w : Nat) : Fin (w+3) := (0 : Fin 1).natAdd (w+2)
theorem clear_best (w : Nat) : clearSlots w (bestIndex w) = port w 2 := by
  apply Fin.ext; simp [clearSlots,bestIndex,port,core]
theorem clear_driver (w : Nat) : clearSlots w (driverIndex w) = port w 3 := by
  apply Fin.ext; simp [clearSlots,driverIndex,port,core]
theorem clear_log (w : Nat) : clearSlots w (logIndex w) = port w 4 := by
  apply Fin.ext; simp [clearSlots,logIndex,port,core]
theorem clear_retained (w : Nat) (i : Fin 6) (hi : i.val < 2 ∨ i.val=5) (j : Fin (w+3)) :
    clearSlots w j ≠ port w i := by
  intro h
  have hv := congrArg Fin.val h
  have := j.isLt
  by_cases hj : j.val < w <;> simp [clearSlots,hj,port,core] at hv <;> omega
theorem clear_extra (w : Nat) (i : Fin 30) (j : Fin (w+3)) : clearSlots w j ≠ extra w i := by
  intro h
  have hv := congrArg Fin.val h
  have := j.isLt
  by_cases hj : j.val < w <;> simp [clearSlots,hj,extra] at hv <;> omega

theorem clear_run (w C : Nat) (ambient : Fin (tapes w) → List Bool)
    (hw : ∀ i : Fin w, ambient (core w (i.castAdd 6)) = [])
    (hb : ambient (port w 2) = [])
    (hd : ambient (port w 3) = List.replicate C true)
    (hl : ambient (port w 4) = []) : ∃ out,
    ClockJoin.ReadyRun (clearProgram w) (2*C+4) ambient out ∧
    (∀ i : Fin w, out (core w (i.castAdd 6)) = List.replicate C false) ∧
    out (port w 2) = List.replicate C false ∧
    out (port w 3) = List.replicate C true ∧
    out (port w 4) = List.replicate (C+1) false ∧
    (∀ i : Fin 6, i.val < 2 ∨ i.val=5 → out (port w i) = ambient (port w i)) ∧
    (∀ i : Fin 30, out (extra w i) = ambient (extra w i)) := by
  have hbase := RecoveryScratchErase.erase_ready C 0 (fun _ : Fin (w+1) => ([] : List Bool))
    (by intro i; exact Nat.zero_le _)
  have h := hbase.focus (clearSlots w) (clear_injective w) ambient (by
    intro i
    refine Fin.addCases (m := w+2) (n := 1) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m := w+1) (n := 1) (fun a => ?_) (fun a => ?_) j
      · refine Fin.addCases (m := w) (n := 1) (fun b => ?_) (fun b => ?_) a
        · simp only [Fin.addCases_left]
          change ambient (clearSlots w (b.castAdd 3)) = []
          rw [clear_work]
          exact hw b
        · fin_cases b
          simp only [Fin.addCases_left]
          change ambient (clearSlots w (bestIndex w)) = []
          rw [clear_best]
          exact hb
      · fin_cases a
        simp only [Fin.addCases_left,Fin.addCases_right]
        change ambient (clearSlots w (driverIndex w)) = List.replicate C true
        rw [clear_driver]
        exact hd
    · fin_cases j
      simp only [Fin.addCases_right]
      change ambient (clearSlots w (logIndex w)) = []
      rw [clear_log]
      exact hl)
  simp only [Nat.zero_max] at h
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  refine ⟨_,⟨r,hr,ht,hh,hs.le⟩,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [←clear_work w i,install_slot _ (clear_injective w)]
    rw [show i.castAdd 3 = ((i.castAdd 1).castAdd 1).castAdd 1 by rfl]
    simp only [Fin.addCases_left]
  · rw [←clear_best,install_slot _ (clear_injective w)]
    simp only [bestIndex,Fin.addCases_left]
  · rw [←clear_driver,install_slot _ (clear_injective w)]
    simp only [driverIndex,Fin.addCases_left,Fin.addCases_right]
  · rw [←clear_log,install_slot _ (clear_injective w)]
    simp only [logIndex,Fin.addCases_right]
  · intro i hi
    exact install_other _ _ _ _ (clear_retained w i hi)
  · intro i
    exact install_other _ _ _ _ (clear_extra w i)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
