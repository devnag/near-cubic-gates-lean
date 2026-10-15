import Proof.CaseAnalysis.RecoveryQueryOutput

/-! Append each original query output at the retained stream cursor. Its
source scalar and all framing/reset scratch are returned for reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedQueryAppend
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7→Fin 60:=![25,31,30,32,59,22,23]
theorem slots_injective : Function.Injective slots:=by decide
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedTagReferenceAppend.machine
def heads (H : Fin 60→ℕ) (refs : List Bool):=Function.update H 59 refs.length
def output (A : Fin 60→List Bool) (refs : List Bool):=Function.update A 59 refs
def input (node C : ℕ) (refs : List Bool) : Fin 7→List Bool:=
  ![List.replicate node true,List.replicate C false,List.replicate C false,
    List.replicate C false,refs,List.replicate C true,List.replicate (C+1) false]
theorem input_eq (node C : ℕ) (refs : List Bool) :
    input node C refs=RecoveryBoundedTagReferenceAppend.data node 0 C refs false := by
  funext j
  fin_cases j
  · change List.replicate node true=ZeroPadding.pad 0 (List.replicate node true)
    rw [ZeroPadding.pad_zero]
  all_goals rfl

theorem append_run (H : Fin 60→ℕ) (A : Fin 60→List Bool) (node C : ℕ) (refs : List Bool)
    (hH : ∀ j,H (slots j)=RecoveryBoundedTagReferenceAppend.heads refs j)
    (hA : ∀ j,A (slots j)=input node C refs j) (hC : 2*node+1 ≤ C) :
    ∃ r,runFrom machine (RecoveryBoundedTagReferenceAppend.budget node C) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedTagReferenceAppend.budget node C ∧
      r.final.heads=heads H (refs++frame (List.replicate node true)) ∧
      r.final.tapes=output A (refs++frame (List.replicate node true)) := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTagReferenceAppend.reference_run node 0 C refs hC
  rw [←input_eq] at pr pt
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedTagReferenceAppend.machine _ H A
    ⟨RecoveryBoundedTagReferenceAppend.machine.start,RecoveryBoundedTagReferenceAppend.heads refs,input node C refs⟩ hH hA p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      all_goals first | rfl | exact (hH 0).symm | exact (hH 1).symm |
        exact (hH 2).symm | exact (hH 3).symm | exact (hH 5).symm | exact (hH 6).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h59 : i≠59:=fun h=>hi ⟨4,h.symm⟩
      simp only [heads,Function.update_of_ne h59]
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      all_goals first | rfl | exact (hA 0).symm | exact (hA 1).symm |
        exact (hA 2).symm | exact (hA 3).symm | exact (hA 5).symm | exact (hA 6).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      have h59 : i≠59:=fun h=>hi ⟨4,h.symm⟩
      simp only [output,Function.update_of_ne h59]

end NearCubicWires.RepairOrdinary.RecoveryBoundedQueryAppend
