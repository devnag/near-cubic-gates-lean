import Proof.CaseAnalysis.RecoveryQueryClear

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryScalar
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots : Fin 7→Fin 60:=![56,1,41,34,32,22,23]
noncomputable def first:=RecoveryFocus.machine firstSlots RecoveryBoundedTagPrepare.machine
def firstOutput (A : Fin 60→List Bool) (C : ℕ) (i : Fin 60):=
  if i=1∨i=41 then ZeroPadding.pad C (List.replicate 6 true)
  else if i=34 then List.replicate C false else A i

theorem first_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (index value C : ℕ)
    (hH : ∀ j,H (firstSlots j)=0)
    (hA : ∀ j,A (firstSlots j)=RecoveryBoundedTagPrepare.data 6 index value C 0 j)
    (hi : index ≤ C) (hv : value ≤ C) (hC : 7 ≤ C) :
    ∃ r,runFrom first (RecoveryBoundedTagPrepare.budget 6 C) ⟨first.start,H,A⟩=some r ∧
      r.steps=RecoveryBoundedTagPrepare.budget 6 C ∧ r.final.heads=H ∧ r.final.tapes=firstOutput A C := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedTagPrepare.prepare_ready 6 index value C hi hv hC).focus_at
    firstSlots (by decide) H A hA hH
  have he : install firstSlots A (RecoveryBoundedTagPrepare.data 6 index value C 3)=firstOutput A C := by
    apply HierarchyWidth.install_eq firstSlots (by decide)
    · intro j
      have h:=hA j
      fin_cases j <;> first | rfl | exact h
    · intro i hi
      have h1 : i≠1:=fun h=>hi 1 h.symm
      have h41 : i≠41:=fun h=>hi 2 h.symm
      have h34 : i≠34:=fun h=>hi 3 h.symm
      simp only [firstOutput,h1,h41,or_self,if_false,if_neg h34]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

def source (second : Bool) : Fin 60:=if second then 57 else 56
def target (second : Bool) : Fin 60:=if second then 44 else 46
def copySlots (second : Bool) : Fin 3→Fin 60:=![source second,target second,32]
theorem copySlots_injective (second : Bool) : Function.Injective (copySlots second) := by cases second <;> decide
noncomputable def copy (second : Bool):=RecoveryFocus.machine (copySlots second) PCPUnaryCopy.machine
def copyOutput (A : Fin 60→List Bool) (second : Bool) (n C : ℕ):=
  Function.update A (target second) (ZeroPadding.pad C (List.replicate n true))

theorem copy_run (second : Bool) (H : Fin 60→ℕ) (A : Fin 60→List Bool) (n C : ℕ)
    (hH : ∀ j,H (copySlots second j)=0)
    (hA : ∀ j,A (copySlots second j)=
      (![List.replicate n true,List.replicate C false,List.replicate C false] : Fin 3→List Bool) j)
    (hC : n+1 ≤ C) :
    ∃ r,runFrom (copy second) (2*n+4) ⟨(copy second).start,H,A⟩=some r ∧
      r.steps=2*n+4 ∧ r.final.heads=H ∧ r.final.tapes=copyOutput A second n C := by
  have h:=PCPUnaryCopy.copy_ready n 0 C C
  rw [ZeroPadding.pad_zero,max_eq_left hC] at h
  obtain ⟨r,hr,rh,rt,rs⟩:=h.focus_at (copySlots second) (copySlots_injective second) H A hA hH
  have he : install (copySlots second) A
      ![List.replicate n true,ZeroPadding.pad C (List.replicate n true),List.replicate C false]=copyOutput A second n C := by
    apply HierarchyWidth.install_eq (copySlots second) (copySlots_injective second)
    · intro j
      have hj:=hA j
      fin_cases j
      · cases second <;> exact hj
      · cases second <;> rfl
      · cases second <;> exact hj
    · intro i hi
      have ht : i≠target second:=fun h=>hi 1 h.symm
      simp only [copyOutput,Function.update_of_ne ht]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

def graphSlots : Fin 2→Fin 60:=![25,32]
noncomputable def graph:=RecoveryFocus.machine graphSlots RepairSource.RecoveryTseitinRawIncrement.machine
def graphOutput (A : Fin 60→List Bool) (node : ℕ):=Function.update A 25 (List.replicate (node+1) true)

theorem graph_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (node C : ℕ)
    (h25 : H 25=0) (h32 : H 32=0) (a25 : A 25=List.replicate node true) (a32 : A 32=List.replicate C false)
    (hC : node+1 ≤ C) :
    ∃ r,runFrom graph (2*node+4) ⟨graph.start,H,A⟩=some r ∧
      r.steps=2*node+4 ∧ r.final.heads=H ∧ r.final.tapes=graphOutput A node := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready node C hC).focus_at
    graphSlots (by decide) H A
    (by intro j;fin_cases j;exact a25;exact a32) (by intro j;fin_cases j;exact h25;exact h32)
  have he : install graphSlots A ![List.replicate (node+1) true,List.replicate C false]=graphOutput A node := by
    apply HierarchyWidth.install_eq graphSlots (by decide)
    · intro j
      fin_cases j
      · rfl
      · exact a32
    · intro i hi
      have h25 : i≠25:=fun h=>hi 0 h.symm
      simp only [graphOutput,Function.update_of_ne h25]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryScalar
