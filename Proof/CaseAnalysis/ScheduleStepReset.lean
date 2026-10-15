import Proof.CaseAnalysis.ScheduleStepLayout

/-! Complete paid return to the next schedule bank, retaining the selected
source length. The reset driver and its full log are physical retained data. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Step
open LocalBitMultitape RepairOrdinary RecoveryRootRound ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def driverIndex (sources : EightSources) (k D : Nat) : Fin (workTapes sources k D+2) :=
  ((0 : Fin 1).natAdd (workTapes sources k D)).castAdd 1
def logIndex (sources : EightSources) (k D : Nat) : Fin (workTapes sources k D+2) :=
  (0 : Fin 1).natAdd (workTapes sources k D+1)
theorem erase_work_slot (sources : EightSources) (k D : Nat) (i : Fin (workTapes sources k D)) :
    eraseSlots sources k D ((i.castAdd 1).castAdd 1)=work sources k D i := by
  apply Fin.ext
  simp [eraseSlots,work,i.isLt]
theorem erase_driver_slot (sources : EightSources) (k D : Nat) :
    eraseSlots sources k D (driverIndex sources k D)=port sources k D 3 := by
  apply Fin.ext
  simp [eraseSlots,driverIndex,port]
theorem erase_log_slot (sources : EightSources) (k D : Nat) :
    eraseSlots sources k D (logIndex sources k D)=port sources k D 4 := by
  apply Fin.ext
  simp [eraseSlots,logIndex,port]

theorem erase_run (sources : EightSources) (k D C s n best : Nat)
    (ambient : Fin (tapes sources k D)→List Bool)
    (hwork : ∀ i,(ambient (work sources k D i)).length≤C)
    (hp : ∀ i,ambient (port sources k D i)=persistent C s n best i) :
    ClockJoin.ReadyRun (eraseWork sources k D) (2*C+4) ambient (bank sources k D C s n best) := by
  have h:= (RecoveryScratchErase.erase_ready C (C+1) (fun i=>ambient (work sources k D i)) hwork).focus
    (eraseSlots sources k D) (erase_injective sources k D) ambient (by
      intro i
      refine Fin.addCases (m:=workTapes sources k D+1) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=workTapes sources k D) (n:=1) (fun a=>?_) (fun a=>?_) j
        · simp only [erase_work_slot,Fin.addCases_left]
        · fin_cases a
          simp only [Fin.addCases_left,Fin.addCases_right]
          change ambient (eraseSlots sources k D (driverIndex sources k D))=List.replicate C true
          rw [erase_driver_slot]
          exact hp 3
      · fin_cases j
        simp only [Fin.addCases_right]
        change ambient (eraseSlots sources k D (logIndex sources k D))=List.replicate (C+1) false
        rw [erase_log_slot]
        exact hp 4)
  simp only [Nat.max_self] at h
  have he : install (eraseSlots sources k D) ambient
      (Fin.addCases (m:=workTapes sources k D+1) (n:=1)
        (Fin.addCases (m:=workTapes sources k D) (n:=1) (fun _ : Fin (workTapes sources k D)=>List.replicate C false)
        (fun _ : Fin 1=>List.replicate C true)) (fun _ : Fin 1=>List.replicate (C+1) false))=
      bank sources k D C s n best := by
    apply HierarchyWidth.install_eq _ (erase_injective sources k D)
    · intro i
      refine Fin.addCases (m:=workTapes sources k D+1) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=workTapes sources k D) (n:=1) (fun a=>?_) (fun a=>?_) j
        · simp only [erase_work_slot,bank_work,Fin.addCases_left]
        · fin_cases a
          change bank sources k D C s n best (eraseSlots sources k D (driverIndex sources k D))=_
          rw [erase_driver_slot,bank_port]
          simp only [Fin.addCases_left,Fin.addCases_right]
          rfl
      · fin_cases j
        change bank sources k D C s n best (eraseSlots sources k D (logIndex sources k D))=_
        rw [erase_log_slot,bank_port]
        simp only [Fin.addCases_right]
        rfl
    · intro i
      refine Fin.addCases (m:=workTapes sources k D) (n:=5) (fun j=>?_) (fun j=>?_) i
      · intro hnone
        exact False.elim (hnone ((j.castAdd 1).castAdd 1) (erase_work_slot sources k D j))
      · intro hnone
        fin_cases j
        · exact (bank_port sources k D C s n best 0).trans (hp 0).symm
        · exact (bank_port sources k D C s n best 1).trans (hp 1).symm
        · exact (bank_port sources k D C s n best 2).trans (hp 2).symm
        · exact False.elim (hnone (driverIndex sources k D) (erase_driver_slot sources k D))
        · exact False.elim (hnone (logIndex sources k D) (erase_log_slot sources k D))
  rw [he] at h
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem increment_run (sources : EightSources) (k D C s n best : Nat) :
    ClockJoin.ReadyRun (increment sources k D) (2*s+5)
      (bank sources k D C s n best) (bank sources k D C (s+1) n best) := by
  have hinj : Function.Injective (incrementSlots sources k D) := by intro a b _;exact Subsingleton.elim a b
  have hi:=PCPPairReusable.padded_ready _ _ _
    (Reusable.increment 0 s) (fun _ : Fin 1=>0)
  simp only [ZeroPadding.pad_zero] at hi
  have h:=hi.focus (incrementSlots sources k D) hinj (bank sources k D C s n best)
    (by intro i;fin_cases i;exact bank_port sources k D C s n best 0)
  have he : install (incrementSlots sources k D) (bank sources k D C s n best)
      (fun _ : Fin 1=>UnaryTemplate.tape (s+1))=bank sources k D C (s+1) n best := by
    apply HierarchyWidth.install_eq _ hinj
    · intro i;fin_cases i;exact bank_port sources k D C (s+1) n best 0
    · intro i
      refine Fin.addCases (m:=workTapes sources k D) (n:=5) (fun j=>?_) (fun j=>?_) i
      · intro _
        simp only [bank,Fin.addCases_left]
      · intro hnone
        fin_cases j
        · exact False.elim (hnone 0 rfl)
        all_goals simp only [bank,Fin.addCases_right,persistent]
        all_goals rfl
  rw [he] at h
  exact h

end
end NearCubicWires.RepairSource.CloseoutSchedule.Step
