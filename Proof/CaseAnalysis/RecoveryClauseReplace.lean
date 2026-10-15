import Proof.CaseAnalysis.RecoveryClauseSelect

/-! Return a newly appended node as the actual live operand and advance the
graph count. Erase, raw copy and increment reuse the existing paid machines. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseReplace
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (node old C : ℕ) (stage : Fin 4) : Fin 5→List Bool:=
  ![List.replicate (node+if 3 ≤ stage.val then 1 else 0) true,
    if 2 ≤ stage.val then ZeroPadding.pad C (List.replicate node true)
      else if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate old true),
    List.replicate C false,List.replicate C true,List.replicate (C+1) false]
def clearSlots : Fin 3→Fin 5:=![1,3,4]
def copySlots : Fin 3→Fin 5:=![0,1,2]
def advanceSlots : Fin 2→Fin 5:=![0,2]
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copy:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def advance:=RecoveryFocus.machine advanceSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def localMachine:=Composition.machine (Composition.machine clear copy) advance
def budget (node C : ℕ):=2*C+4*node+14

theorem clear_ready (node old C : ℕ) (ho : old ≤ C) :
    ReadyRun clear (2*C+4) (data node old C 0) (data node old C 1) := by
  let backing : Fin 1→List Bool:=fun _=>ZeroPadding.pad C (List.replicate old true)
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    change (ZeroPadding.pad C (List.replicate old true)).length ≤ C
    rw [ZeroPadding.pad_length,List.length_replicate,max_eq_left ho]
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus clearSlots (by decide)
    (data node old C 0) (by intro j;fin_cases j <;> rfl)
  have he : install clearSlots (data node old C 0)
      (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data node old C 1 := by
    apply HierarchyWidth.install_eq clearSlots (by decide)
    · intro j;fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at h
  exact h

theorem copy_ready (node old C : ℕ) (hC : node+1 ≤ C) :
    ReadyRun copy (2*node+4) (data node old C 1) (data node old C 2) := by
  have h:=PCPUnaryCopy.copy_ready node 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus copySlots (by decide) (data node old C 1) (by intro j;fin_cases j <;> rfl)
  have he : install copySlots (data node old C 1)
      ![List.replicate node true,ZeroPadding.pad C (List.replicate node true),List.replicate C false]=data node old C 2 := by
    apply HierarchyWidth.install_eq copySlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl)
  rw [he] at run
  exact run

theorem advance_ready (node old C : ℕ) (hC : node+1 ≤ C) :
    ReadyRun advance (2*node+4) (data node old C 2) (data node old C 3) := by
  have h:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready node C hC).focus advanceSlots (by decide)
    (data node old C 2) (by intro j;fin_cases j <;> rfl)
  have he : install advanceSlots (data node old C 2)
      ![List.replicate (node+1) true,List.replicate C false]=data node old C 3 := by
    apply HierarchyWidth.install_eq advanceSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  rw [he] at h
  exact h

theorem replace_ready (node old C : ℕ) (ho : old ≤ C) (hC : node+1 ≤ C) :
    ReadyRun localMachine (budget node C) (data node old C 0) (data node old C 3) := by
  have hfirst:=HierarchyMultiplyEntry.join_exact clear copy _ _ _ _ _
    (clear_ready node old C ho) (copy_ready node old C hC)
  have whole:=HierarchyMultiplyEntry.join_exact (Composition.machine clear copy) advance _ _ _ _ _
    hfirst (advance_ready node old C hC)
  have he : ((2*C+4)+1+(2*node+4))+1+(2*node+4)=budget node C := by unfold budget;omega
  simpa only [localMachine,he] using whole

def slots (second : Bool) : Fin 5→Fin 61:=![25,RecoveryBoundedClauseSelect.target second,32,22,23]
theorem slots_injective (second : Bool) : Function.Injective (slots second) := by cases second <;> decide
noncomputable def machine (second : Bool):=RecoveryFocus.machine (slots second) localMachine
def output (A : Fin 61→List Bool) (second : Bool) (node C : ℕ):=
  Function.update (Function.update A (RecoveryBoundedClauseSelect.target second) (ZeroPadding.pad C (List.replicate node true)))
    25 (List.replicate (node+1) true)

theorem replace_run (second : Bool) (H : Fin 61→ℕ) (A : Fin 61→List Bool) (node old C : ℕ)
    (hH : ∀ j,H (slots second j)=0) (hA : ∀ j,A (slots second j)=data node old C 0 j)
    (ho : old ≤ C) (hC : node+1 ≤ C) :
    ∃ r,runFrom (machine second) (budget node C) ⟨(machine second).start,H,A⟩=some r ∧
      r.steps=budget node C ∧ r.final.heads=H ∧ r.final.tapes=output A second node C := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(replace_ready node old C ho hC).focus_at
    (slots second) (slots_injective second) H A hA hH
  have he : install (slots second) A (data node old C 3)=output A second node C := by
    apply HierarchyWidth.install_eq (slots second) (slots_injective second)
    · intro j
      have h:=hA j
      fin_cases j <;> cases second <;> first | rfl | exact h
    · intro i hi
      have h25 : i≠25:=fun h=>hi 0 h.symm
      have htarget : i≠RecoveryBoundedClauseSelect.target second:=fun h=>hi 1 h.symm
      simp only [output,Function.update_of_ne h25,Function.update_of_ne htarget]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseReplace
