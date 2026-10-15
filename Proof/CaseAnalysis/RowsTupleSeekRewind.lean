import Proof.CaseAnalysis.RowsTupleSeekReusableTerm
import Proof.MachineModel.CacheRewind

/-! Each requested original index may restart all three family cursors.
The same retained capacity driver pays every rewind; append outputs stay put. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rewindSlots (j : Fin 3) : Fin 3 → Fin 23 := ![(rawSourceSlots j).castAdd 3,21,22]
noncomputable def rewindOne (j : Fin 3) := RecoveryFocus.machine (rewindSlots j) CompetitorRecordRewind.machine
noncomputable def rewindMachine := Composition.machine (Composition.machine (rewindOne 0) (rewindOne 1)) (rewindOne 2)

theorem rewind_one (j : Fin 3) (C : ℕ) (src : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : Fin 4 → List Bool) (hp : pos j ≤ C) :
    Step (rewindOne j) (2*C+2) (reuseHeads (localHeads pos out)) (reuseData C (localData src out))
      (reuseHeads (localHeads (Function.update pos j 0) out)) (reuseData C (localData src out)) := by
  apply dock_exact (CacheRewind.rewind_step (src j) C (pos j) hp) (rewindSlots j)
    (by fin_cases j <;> decide)
  · intro i;fin_cases j <;> fin_cases i <;> simp [rewindSlots,rawSourceSlots,reuseHeads,localHeads,Fin.addCases]
  · intro i;fin_cases j <;> fin_cases i <;>
      simp [rewindSlots,rawSourceSlots,reuseData,cleanData,privateTapes,localData,Fin.addCases]
  · intro i;fin_cases j <;> fin_cases i <;>
      simp [rewindSlots,rawSourceSlots,reuseHeads,localHeads,Fin.addCases]
  · intro i;fin_cases j <;> fin_cases i <;>
      simp [rewindSlots,rawSourceSlots,reuseData,cleanData,privateTapes,localData,Fin.addCases]
  · intro i hi
    have target := hi 0
    fin_cases j <;> fin_cases i <;>
      simp_all [rewindSlots,rawSourceSlots,reuseHeads,localHeads,Fin.addCases]

theorem rewind_run (C : ℕ) (src : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : Fin 4 → List Bool) (hp : ∀ j,pos j ≤ C) :
    Step rewindMachine (6*C+8) (reuseHeads (localHeads pos out)) (reuseData C (localData src out))
      (reuseHeads (localHeads (fun _ => 0) out)) (reuseData C (localData src out)) := by
  have a := rewind_one 0 C src pos out (hp 0)
  have b := rewind_one 1 C src (Function.update pos 0 0) out (by simpa using hp 1)
  have c := rewind_one 2 C src (Function.update (Function.update pos 0 0) 1 0) out (by simpa using hp 2)
  have h := (a.seq b).seq c
  have finalPos : Function.update (Function.update (Function.update pos 0 0) 1 0) 2 0=(fun _ => 0) := by
    funext i;fin_cases i <;> simp
  rw [finalPos,show (2*C+2+1+(2*C+2))+1+(2*C+2)=6*C+8 by omega] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
