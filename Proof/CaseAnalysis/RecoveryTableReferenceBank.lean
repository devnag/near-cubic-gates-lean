import Proof.CaseAnalysis.RecoveryTableReferenceReset

/-! Pay the original table's live-reference append and source rewind inside
the retained 55-tape bank. Only the actual prior-reference bytes change. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceBank
open LocalBitMultitape RepairRepresentation
open RepairSource.VerifierDecoding RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 9→Fin 55:=![25,31,30,32,37,22,23,42,39]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedTableReferenceReset.machine
def input (refs : List ℕ) (node C D : ℕ) : Fin 9→List Bool:=
  ![List.replicate node true,List.replicate C false,List.replicate C false,List.replicate C false,
    ZeroPadding.pad C (sourceWord refs),List.replicate C true,List.replicate (C+1) false,
    CompareMachine.word refs.length,List.replicate D false]
def output (A : Fin 55→List Bool) (refs : List ℕ) (node C : ℕ):=
  Function.update A 37 (ZeroPadding.pad C (sourceWord (refs++[node])))

theorem input_tapes (refs : List ℕ) (node C D : ℕ) :
    (RecoveryBoundedTableReferenceReset.entry refs node C D).tapes=input refs node C D := by
  rw [RecoveryBoundedTableReferenceReset.entry_tapes]
  funext i
  fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _

theorem output_slot (A : Fin 55→List Bool) (refs : List ℕ) (node C D : ℕ)
    (hA : ∀ j,A (slots j)=input refs node C D j) (j : Fin 9) :
    output A refs node C (slots j)=RecoveryBoundedTableReferenceReset.finalData refs node C D j := by
  have hj:=hA j
  fin_cases j
  all_goals first | rfl | exact hj | exact hj.trans (ZeroPadding.pad_zero _).symm

theorem reference_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (refs : List ℕ) (node C D : ℕ)
    (hH : ∀ j,H (slots j)=RecoveryBoundedTableReferenceReset.finalHeads j)
    (hA : ∀ j,A (slots j)=input refs node C D j) (hC : 2*node+1 ≤ C)
    (hD : RecoveryBoundedTableReferenceAppend.budget refs node C ≤ D) :
    ∃ r,runFrom machine (RecoveryBoundedTableReferenceReset.budget refs node C) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedTableReferenceReset.budget refs node C ∧
      r.final.heads=H ∧ r.final.tapes=output A refs node C := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedTableReferenceReset.reset_run refs node C D hC hD
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective RecoveryBoundedTableReferenceReset.machine _ H A
    (RecoveryBoundedTableReferenceReset.entry refs node C D)
    (by rw [RecoveryBoundedTableReferenceReset.entry_heads];exact hH) (by rw [input_tapes];exact hA) p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (hH j).symm
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).1
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      exact (output_slot A refs node C D hA j).symm
    · have h37 : i≠37:=fun h=>hi ⟨4,h.symm⟩
      rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      simp only [output,Function.update_of_ne h37]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableReferenceBank
