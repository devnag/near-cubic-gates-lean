import Proof.CaseAnalysis.RowsTupleSeekRewind

/-! Family restart capacity D is separate from the per-term parser capacity
C. D pays only traversal of the actual three logical family streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rewind_at {t : ℕ} (src driver log : Fin t) (hd : src≠driver) (hl : src≠log) (hdl : driver≠log)
    (D : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool) (hp : H src ≤ D)
    (hdh : H driver=0) (hlh : H log=0) (hda : A driver=List.replicate D true)
    (hla : A log=List.replicate (D+1) false) :
    Step (RecoveryFocus.machine ![src,driver,log] CompetitorRecordRewind.machine) (2*D+2)
      H A (Function.update H src 0) A := by
  apply dock_exact (CacheRewind.rewind_step (A src) D (H src) hp) ![src,driver,log]
    (by intro i j hij;fin_cases i <;> fin_cases j <;> simp_all)
  · intro i;fin_cases i <;> simp [hdh,hlh]
  · intro i;fin_cases i <;> simp [hda,hla]
  · intro i;fin_cases i <;> simp [hd.symm,hl.symm,hdh,hlh]
  · intro i;fin_cases i <;> simp [hda,hla]
  · intro i hi
    have hs : i≠src := (hi 0).symm
    simp [hs]

def familyHeads (pos : Fin 3 → ℕ) (out : Fin 4 → List Bool) : Fin 25 → ℕ :=
  Fin.addCases (m:=23) (n:=2) (motive:=fun _=>ℕ) (reuseHeads (localHeads pos out)) (fun _=>0)
def familyData (C D : ℕ) (src : Fin 3 → List Bool) (out : Fin 4 → List Bool) : Fin 25 → List Bool :=
  Fin.addCases (m:=23) (n:=2) (motive:=fun _=>List Bool) (reuseData C (localData src out))
    ![List.replicate D true,List.replicate (D+1) false]
def familySourceSlot (j : Fin 3) : Fin 25 := (rawSourceSlots j).castAdd 5
noncomputable def familyRewindOne (j : Fin 3) :=
  RecoveryFocus.machine ![familySourceSlot j,23,24] CompetitorRecordRewind.machine
noncomputable def familyRewind := Composition.machine
  (Composition.machine (familyRewindOne 0) (familyRewindOne 1)) (familyRewindOne 2)
noncomputable def familyTerm (keep : Bool) := TapeEmbedding.machine 2 (reusableMachine keep)

theorem family_head_update (j : Fin 3) (pos : Fin 3 → ℕ) (out : Fin 4 → List Bool) :
    Function.update (familyHeads pos out) (familySourceSlot j) 0=familyHeads (Function.update pos j 0) out := by
  funext i;fin_cases j <;> fin_cases i <;>
    simp [familyHeads,familySourceSlot,rawSourceSlots,reuseHeads,localHeads,Fin.addCases]

theorem family_rewind_one (j : Fin 3) (C D : ℕ) (src : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : Fin 4 → List Bool) (hp : pos j ≤ D) :
    Step (familyRewindOne j) (2*D+2) (familyHeads pos out) (familyData C D src out)
      (familyHeads (Function.update pos j 0) out) (familyData C D src out) := by
  have h := rewind_at (familySourceSlot j) 23 24
    (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by decide)
    D (familyHeads pos out) (familyData C D src out)
    (by fin_cases j <;> simpa [familyHeads,familySourceSlot,rawSourceSlots,reuseHeads,localHeads,Fin.addCases] using hp)
    (by rfl) (by rfl) (by rfl) (by rfl)
  rw [family_head_update] at h
  exact h

theorem family_rewind_run (C D : ℕ) (src : Fin 3 → List Bool) (pos : Fin 3 → ℕ)
    (out : Fin 4 → List Bool) (hp : ∀ j,pos j ≤ D) :
    Step familyRewind (6*D+8) (familyHeads pos out) (familyData C D src out)
      (familyHeads (fun _=>0) out) (familyData C D src out) := by
  have a := family_rewind_one 0 C D src pos out (hp 0)
  have b := family_rewind_one 1 C D src (Function.update pos 0 0) out (by simpa using hp 1)
  have c := family_rewind_one 2 C D src (Function.update (Function.update pos 0 0) 1 0) out (by simpa using hp 2)
  have h := (a.seq b).seq c
  have lastPos : Function.update (Function.update (Function.update pos 0 0) 1 0) 2 0=(fun _=>0) := by
    funext i;fin_cases i <;> simp
  rw [lastPos,show (2*D+2+1+(2*D+2))+1+(2*D+2)=6*D+8 by omega] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
