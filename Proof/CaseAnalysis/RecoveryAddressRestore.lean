import Proof.CaseAnalysis.RecoveryAddressReference

/-! Return either address branch to the same reusable unary input: erase
the spent index and flag, copy the retained index, and increment the value. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressRestore
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 4→Fin 7:=![0,2,5,6]
def copySlots : Fin 3→Fin 7:=![1,0,4]
def incrementSlots : Fin 2→Fin 7:=![3,4]
noncomputable def first:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def second:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def third:=RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def machine:=Composition.machine (Composition.machine first second) third
def data (index spent value C : ℕ) (flag : Bool) (stage : Fin 4) : Fin 7→List Bool:=
  ![if 2 ≤ stage.val then ZeroPadding.pad C (List.replicate index true)
    else if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate spent true),
    List.replicate index true,
    if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C [flag],
    ZeroPadding.pad C (List.replicate (value+if 3 ≤ stage.val then 1 else 0) true),
    List.replicate C false,List.replicate C true,List.replicate (C+1) false]

theorem erase_ready (index spent value C : ℕ) (flag : Bool) (hs : spent ≤ C) (hC : 1 ≤ C) :
    ReadyRun first (2*C+4) (data index spent value C flag 0) (data index spent value C flag 1) := by
  let backing : Fin 2→List Bool:=![ZeroPadding.pad C (List.replicate spent true),ZeroPadding.pad C [flag]]
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (List.replicate spent true)).length ≤ C
      simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
      omega
    · change (ZeroPadding.pad C [flag]).length ≤ C
      simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.length_singleton]
      omega
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus eraseSlots
    (by decide) (data index spent value C flag 0) (by intro j;fin_cases j <;> rfl)
  have he : install eraseSlots (data index spent value C flag 0)
      (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data index spent value C flag 1 := by
    apply HierarchyWidth.install_eq eraseSlots (by decide)
    · intro j;fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem copy_ready (index spent value C : ℕ) (flag : Bool) (hi : index+1 ≤ C) :
    ReadyRun second (2*index+4) (data index spent value C flag 1) (data index spent value C flag 2) := by
  have h:=PCPUnaryCopy.copy_ready index 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hi] at h
  have hf:=h.focus copySlots (by decide) (data index spent value C flag 1)
    (by intro j;fin_cases j <;> rfl)
  have he : install copySlots (data index spent value C flag 1)
      ![List.replicate index true,ZeroPadding.pad C (List.replicate index true),List.replicate C false]=
      data index spent value C flag 2 := by
    apply HierarchyWidth.install_eq copySlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at hf
  exact hf

theorem increment_ready (index spent value C : ℕ) (flag : Bool) (hv : value+1 ≤ C) :
    ReadyRun third (2*value+4) (data index spent value C flag 2) (data index spent value C flag 3) := by
  have hp:=RecoveryChildSelection.ReadyRun.pad
    (RepairSource.RecoveryTseitinRawIncrement.increment_ready value C hv) (![C,0] : Fin 2→ℕ)
  have h : ReadyRun RepairSource.RecoveryTseitinRawIncrement.machine (2*value+4)
      ![ZeroPadding.pad C (List.replicate value true),List.replicate C false]
      ![ZeroPadding.pad C (List.replicate (value+1) true),List.replicate C false] := by
    convert hp using 1 <;> funext i <;> fin_cases i
    all_goals first | rfl | exact ZeroPadding.pad_zero _ | exact (ZeroPadding.pad_zero _).symm
  have hf:=h.focus incrementSlots (by decide) (data index spent value C flag 2)
    (by intro j;fin_cases j <;> rfl)
  have he : install incrementSlots (data index spent value C flag 2)
      ![ZeroPadding.pad C (List.replicate (value+1) true),List.replicate C false]=data index spent value C flag 3 := by
    apply HierarchyWidth.install_eq incrementSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at hf
  exact hf

theorem restore_ready (index spent value C : ℕ) (flag : Bool)
    (hi : index+1 ≤ C) (hs : spent ≤ C) (hv : value+1 ≤ C) :
    ReadyRun machine (2*C+2*index+2*value+14)
      (data index spent value C flag 0) (data index spent value C flag 3) := by
  have h:=HierarchyMultiplyEntry.join_exact first second _ _ _ _ _
    (erase_ready index spent value C flag hs (by omega)) (copy_ready index spent value C flag hi)
  have full:=HierarchyMultiplyEntry.join_exact (Composition.machine first second) third _ _ _ _ _ h
    (increment_ready index spent value C flag hv)
  have he : (2*C+4+1+(2*index+4))+1+(2*value+4)=2*C+2*index+2*value+14 := by omega
  simpa only [machine,he] using full

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressRestore
