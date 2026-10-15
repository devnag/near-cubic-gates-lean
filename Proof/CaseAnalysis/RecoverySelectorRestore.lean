import Proof.CaseAnalysis.RecoverySelectorJoin

/-! Restore the actual next-selector inputs: erase the consumed reference
and flag, copy the retained shared description-field index, and increment
the value. Existing capacity and logs are returned for another call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorRestore
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 4→Fin 8:=![2,3,6,7]
def copySlots : Fin 3→Fin 8:=![1,0,5]
def incrementSlots : Fin 2→Fin 8:=![4,5]
noncomputable def first:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def second:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def third:=RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def machine:=Composition.machine (Composition.machine first second) third
def data (index ref value C : ℕ) (flag : Bool) (stage : Fin 4) : Fin 8→List Bool :=
  ![if 2 ≤ stage.val then ZeroPadding.pad C (List.replicate index true) else List.replicate C false,
    List.replicate index true,
    if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate ref true),
    if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C [flag],
    List.replicate (value+if 3 ≤ stage.val then 1 else 0) true,
    List.replicate C false,List.replicate C true,List.replicate (C+1) false]

theorem erase_ready (index ref value C : ℕ) (flag : Bool) (hr : ref≤C) (hC : 1≤C) :
    ReadyRun first (2*C+4) (data index ref value C flag 0) (data index ref value C flag 1) := by
  let backing : Fin 2→List Bool:=![ZeroPadding.pad C (List.replicate ref true),ZeroPadding.pad C [flag]]
  have hb : ∀ j,(backing j).length≤C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (List.replicate ref true)).length≤C
      simp only [ZeroPadding.pad,List.length_append,List.length_replicate]
      omega
    · change (ZeroPadding.pad C [flag]).length≤C
      simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.length_singleton]
      omega
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus eraseSlots
    (by decide) (data index ref value C flag 0) (by intro j; fin_cases j <;> rfl)
  have he : install eraseSlots (data index ref value C flag 0)
      (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data index ref value C flag 1 := by
    apply HierarchyWidth.install_eq eraseSlots (by decide)
    · intro j; fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at h
  exact h

theorem copy_ready (index ref value C : ℕ) (flag : Bool) (hi : index+1≤C) :
    ReadyRun second (2*index+4) (data index ref value C flag 1) (data index ref value C flag 2) := by
  have h:=(PCPUnaryCopy.copy_ready index 0 C C)
  rw [ZeroPadding.pad_zero,max_eq_left hi] at h
  have h':=h.focus copySlots (by decide) (data index ref value C flag 1)
    (by intro j; fin_cases j <;> rfl)
  have he : install copySlots (data index ref value C flag 1)
      ![List.replicate index true,ZeroPadding.pad C (List.replicate index true),List.replicate C false]=
      data index ref value C flag 2 := by
    apply HierarchyWidth.install_eq copySlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at h'
  exact h'

theorem increment_ready (index ref value C : ℕ) (flag : Bool) (hv : value+1≤C) :
    ReadyRun third (2*value+4) (data index ref value C flag 2) (data index ref value C flag 3) := by
  have h:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready value C hv).focus incrementSlots
    (by decide) (data index ref value C flag 2) (by intro j; fin_cases j <;> rfl)
  have he : install incrementSlots (data index ref value C flag 2)
      ![List.replicate (value+1) true,List.replicate C false]=data index ref value C flag 3 := by
    apply HierarchyWidth.install_eq incrementSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at h
  exact h

theorem restore_ready (index ref value C : ℕ) (flag : Bool)
    (hi : index+1≤C) (hr : ref≤C) (hv : value+1≤C) :
    ReadyRun machine (2*C+2*index+2*value+14)
      (data index ref value C flag 0) (data index ref value C flag 3) := by
  have h:=HierarchyMultiplyEntry.join_exact first second _ _ _ _ _
    (erase_ready index ref value C flag hr (by omega)) (copy_ready index ref value C flag hi)
  have full:=HierarchyMultiplyEntry.join_exact (Composition.machine first second) third _ _ _ _ _ h
    (increment_ready index ref value C flag hv)
  have he : (2*C+4+1+(2*index+4))+1+(2*value+4)=2*C+2*index+2*value+14 := by omega
  simpa only [machine,he] using full

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorRestore
