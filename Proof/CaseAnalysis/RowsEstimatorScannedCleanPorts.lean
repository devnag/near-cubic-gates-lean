import Proof.CaseAnalysis.RowsEstimatorScannedSupport
import Proof.CaseAnalysis.RowsEstimatorDriverCleanBank

/-! Route the actual fresh driver bank into the checked copy/cleanup
consumer, retaining every original scanner port. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def count (a : WilliamsAlgorithm) := 98+2*DriverLayout.e a
noncomputable def tapes (a : WilliamsAlgorithm) := ScannedDriver.tapes a+3
noncomputable def old (a : WilliamsAlgorithm) (i : Fin (ScannedDriver.tapes a)) : Fin (tapes a) := i.castAdd 3
noncomputable def driver (a : WilliamsAlgorithm) : Fin (tapes a) := old a (ScannedDriver.driver a)
noncomputable def fresh (a : WilliamsAlgorithm) (i : Fin 3) : Fin (tapes a) := i.natAdd (ScannedDriver.tapes a)
noncomputable def work (a : WilliamsAlgorithm) (i : Fin (count a)) : Fin (tapes a) :=
  if i.val<97+2*DriverLayout.e a then ⟨70+i.val,by dsimp [tapes,ScannedDriver.tapes,DriverLayout.tapes,count] at *;omega⟩
  else ⟨70+i.val+1,by have hi:=i.isLt;dsimp [tapes,ScannedDriver.tapes,DriverLayout.tapes,count] at *;omega⟩
noncomputable def slots (a : WilliamsAlgorithm) : Fin (4+count a) → Fin (tapes a) :=
  Fin.addCases (![driver a,fresh a 0,fresh a 1,fresh a 2] : Fin 4 → Fin (tapes a)) (work a)

theorem work_val (a : WilliamsAlgorithm) (i : Fin (count a)) :
    (work a i).val=if i.val<97+2*DriverLayout.e a then 70+i.val else 70+i.val+1 := by
  unfold work
  split_ifs <;> rfl
theorem work_bounds (a : WilliamsAlgorithm) (i : Fin (count a)) :
    70 ≤ (work a i).val ∧ (work a i).val<ScannedDriver.tapes a ∧ (work a i).val≠(driver a).val := by
  have hi:=i.isLt
  change 70 ≤ (work a i).val ∧ (work a i).val<ScannedDriver.tapes a ∧ (work a i).val≠(ScannedDriver.driver a).val
  rw [work_val,ScannedDriver.driver_val]
  dsimp [ScannedDriver.tapes,DriverLayout.tapes,count] at *
  split_ifs <;> omega
theorem work_injective (a : WilliamsAlgorithm) : Function.Injective (work a) := by
  intro i j he
  have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
  rw [work_val,work_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  revert he
  refine Fin.addCases (m:=4) (n:=count a) (fun k=>?_) (fun k=>?_) i <;>
    refine Fin.addCases (m:=4) (n:=count a) (fun l=>?_) (fun l=>?_) j
  · intro he
    have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
    have hd:=(ScannedDriver.driver a).isLt
    fin_cases k <;> fin_cases l <;> simp [slots,driver,old,fresh] at hv ⊢ <;> omega
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
    have hw:=work_bounds a l
    have hcast : ((ScannedDriver.driver a).castAdd 3).val=(ScannedDriver.driver a).val:=rfl
    simp only [driver,old,Fin.val_castAdd] at hw
    fin_cases k <;> simp [driver,old,fresh] at hv <;> omega
  · intro he
    simp only [slots,Fin.addCases_left,Fin.addCases_right] at he
    have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
    have hw:=work_bounds a k
    have hcast : ((ScannedDriver.driver a).castAdd 3).val=(ScannedDriver.driver a).val:=rfl
    simp only [driver,old,Fin.val_castAdd] at hw
    fin_cases l <;> simp [driver,old,fresh] at hv <;> omega
  · intro he
    simp only [slots,Fin.addCases_right] at he
    exact congrArg (Fin.natAdd 4) (work_injective a he)

theorem avoids_old (a : WilliamsAlgorithm) (i : Fin 70) :
    ∀ j,slots a j≠old a (i.castAdd (DriverLayout.tapes a)) := by
  intro j
  refine Fin.addCases (m:=4) (n:=count a) (fun k=>?_) (fun k=>?_) j
  · intro he
    have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
    have hi:=i.isLt
    fin_cases k <;> simp [slots,driver,old,fresh,ScannedDriver.driver_val] at hv
    all_goals have ht : 70 ≤ ScannedDriver.tapes a := by unfold ScannedDriver.tapes;omega
    all_goals omega
  · intro he
    have hv:=congrArg (fun z : Fin (tapes a) => z.val) he
    have hi:=i.isLt
    have hw:=work_bounds a k
    simp only [slots,Fin.addCases_right,old,Fin.val_castAdd] at hv
    omega

noncomputable def first (a : WilliamsAlgorithm) :=
  ClockJoin.lifted (Equiv.refl (Fin (tapes a))) (ScannedDriver.machine a)
noncomputable def last (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a)
  (DriverCleanBank.machine (count a) (DriverLayout.sweepCount a))
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last a)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
