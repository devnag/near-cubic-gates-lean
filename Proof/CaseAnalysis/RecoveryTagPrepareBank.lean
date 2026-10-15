import Proof.CaseAnalysis.RecoveryTagPrepare

/-! The paid tag-index handoff preserves the packet and every original
graph/source field in the retained 55-tape bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeTagPrepare
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7→Fin 55:=![52,1,41,34,32,22,23]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine:=RecoveryFocus.machine slots RecoveryBoundedTagPrepare.machine
def output (A : Fin 55→List Bool) (tag C : ℕ) (i : Fin 55):=
  if i=1 ∨ i=41 then ZeroPadding.pad C (List.replicate tag true)
  else if i=34 then List.replicate C false else A i

theorem output_slot (A : Fin 55→List Bool) (tag index value C : ℕ)
    (hA : ∀ j,A (slots j)=RecoveryBoundedTagPrepare.data tag index value C 0 j) (j : Fin 7) :
    output A tag C (slots j)=RecoveryBoundedTagPrepare.data tag index value C 3 j := by
  have hj:=hA j
  fin_cases j <;> first | rfl | exact hj

theorem prepare_run (H : Fin 55→ℕ) (A : Fin 55→List Bool) (tag index value C : ℕ)
    (hH : ∀ j,H (slots j)=0) (hA : ∀ j,A (slots j)=RecoveryBoundedTagPrepare.data tag index value C 0 j)
    (hi : index ≤ C) (hv : value ≤ C) (ht : tag+1 ≤ C) :
    ∃ r,runFrom machine (RecoveryBoundedTagPrepare.budget tag C) ⟨machine.start,H,A⟩=some r ∧
      r.steps=RecoveryBoundedTagPrepare.budget tag C ∧ r.final.heads=H ∧ r.final.tapes=output A tag C := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedTagPrepare.prepare_ready tag index value C hi hv ht).focus_at
    slots slots_injective H A hA hH
  have he : install slots A (RecoveryBoundedTagPrepare.data tag index value C 3)=output A tag C := by
    apply HierarchyWidth.install_eq slots slots_injective
    · exact output_slot A tag index value C hA
    · intro i hi
      have h1 : i≠1:=fun h=>hi 1 h.symm
      have h41 : i≠41:=fun h=>hi 2 h.symm
      have h34 : i≠34:=fun h=>hi 3 h.symm
      simp only [output,h1,h41,or_self,if_false,if_neg h34]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

theorem packet_unchanged (A : Fin 55→List Bool) (constant current C : ℕ) (j : Fin 7) :
    RecoveryBoundedNodeTagPacket.output A constant current C (slots j)=A (slots j) := by
  fin_cases j <;> rfl

theorem budget_quadratic (tag W : ℕ) (ht : tag ≤ W) :
    RecoveryBoundedTagPrepare.budget tag (RecoveryBoundedSelectorLoop.capacity W) ≤ 65536*(W+1)^2 := by
  unfold RecoveryBoundedTagPrepare.budget RecoveryBoundedSelectorLoop.capacity
  nlinarith [Nat.zero_le (W^2)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeTagPrepare
