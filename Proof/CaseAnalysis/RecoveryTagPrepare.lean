import Proof.CaseAnalysis.RecoveryTagPacketBank

/-! Prepare the original five-tag selector from the retained actual tag
index. Its cold/table producer advances this scalar with both field indices. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagPrepare
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fixedData (tag C : ℕ) : Fin 7→List Bool:=
  ![List.replicate tag true,[],[],[],List.replicate C false,
    List.replicate C true,List.replicate (C+1) false]
def data (tag index value C : ℕ) (stage : Fin 4) (i : Fin 7):=
  if i=1 then if 2 ≤ stage.val then ZeroPadding.pad C (List.replicate tag true)
    else if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate index true)
  else if i=2 then if 3 ≤ stage.val then ZeroPadding.pad C (List.replicate tag true)
    else if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate index true)
  else if i=3 then if 1 ≤ stage.val then List.replicate C false else ZeroPadding.pad C (List.replicate value true)
  else fixedData tag C i
def clearSlots : Fin 5→Fin 7:=![1,2,3,5,6]
def firstSlots : Fin 3→Fin 7:=![0,1,4]
def lastSlots : Fin 3→Fin 7:=![0,2,4]
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def first:=RecoveryFocus.machine firstSlots PCPUnaryCopy.machine
noncomputable def last:=RecoveryFocus.machine lastSlots PCPUnaryCopy.machine
noncomputable def machine:=Composition.machine (Composition.machine clear first) last
def budget (tag C : ℕ):=2*C+4*tag+14

theorem clear_ready (tag index value C : ℕ) (hi : index ≤ C) (hv : value ≤ C) :
    ReadyRun clear (2*C+4) (data tag index value C 0) (data tag index value C 1) := by
  let backing : Fin 3→List Bool:=![ZeroPadding.pad C (List.replicate index true),
    ZeroPadding.pad C (List.replicate index true),ZeroPadding.pad C (List.replicate value true)]
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    fin_cases j
    all_goals change (ZeroPadding.pad C (List.replicate _ true)).length ≤ C
    all_goals rw [ZeroPadding.pad_length,List.length_replicate];omega
  have h:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus clearSlots (by decide)
    (data tag index value C 0) (by intro j;fin_cases j <;> rfl)
  have he : install clearSlots (data tag index value C 0)
      (Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data tag index value C 1 := by
    apply HierarchyWidth.install_eq clearSlots (by decide)
    · intro j;fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      have h1 : i≠1:=fun h=>hi 0 h.symm
      have h2 : i≠2:=fun h=>hi 1 h.symm
      have h3 : i≠3:=fun h=>hi 2 h.symm
      simp only [data,if_neg h1,if_neg h2,if_neg h3]
  rw [he] at h
  exact h

theorem first_ready (tag index value C : ℕ) (hC : tag+1 ≤ C) :
    ReadyRun first (2*tag+4) (data tag index value C 1) (data tag index value C 2) := by
  have h:=PCPUnaryCopy.copy_ready tag 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus firstSlots (by decide) (data tag index value C 1) (by intro j;fin_cases j <;> rfl)
  have he : install firstSlots (data tag index value C 1)
      ![List.replicate tag true,ZeroPadding.pad C (List.replicate tag true),List.replicate C false]=data tag index value C 2 := by
    apply HierarchyWidth.install_eq firstSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have h1 : i≠1:=fun h=>hi 1 h.symm
      simp only [data,if_neg h1]
      rfl
  rw [he] at run
  exact run

theorem last_ready (tag index value C : ℕ) (hC : tag+1 ≤ C) :
    ReadyRun last (2*tag+4) (data tag index value C 2) (data tag index value C 3) := by
  have h:=PCPUnaryCopy.copy_ready tag 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  have run:=h.focus lastSlots (by decide) (data tag index value C 2) (by intro j;fin_cases j <;> rfl)
  have he : install lastSlots (data tag index value C 2)
      ![List.replicate tag true,ZeroPadding.pad C (List.replicate tag true),List.replicate C false]=data tag index value C 3 := by
    apply HierarchyWidth.install_eq lastSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      have h2 : i≠2:=fun h=>hi 1 h.symm
      simp only [data,if_neg h2]
      rfl
  rw [he] at run
  exact run

theorem prepare_ready (tag index value C : ℕ) (hi : index ≤ C) (hv : value ≤ C) (ht : tag+1 ≤ C) :
    ReadyRun machine (budget tag C) (data tag index value C 0) (data tag index value C 3) := by
  have hfirst:=HierarchyMultiplyEntry.join_exact clear first _ _ _ _ _
    (clear_ready tag index value C hi hv) (first_ready tag index value C ht)
  have whole:=HierarchyMultiplyEntry.join_exact (Composition.machine clear first) last _ _ _ _ _ hfirst
    (last_ready tag index value C ht)
  have he : ((2*C+4)+1+(2*tag+4))+1+(2*tag+4)=budget tag C := by unfold budget;omega
  simpa only [machine,he] using whole

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagPrepare
