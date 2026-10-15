import Proof.CaseAnalysis.RecoveryUniversalGates

/-! Append the original NOT/AND/OR nodes directly from the saved left/right
outputs, preserving the current graph counter and every other retained field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def gateSlots (j : Fin 29) : Fin 51:=if j=1 then 45 else if j=25 then 47 else j.castAdd 22
theorem gate_injective : Function.Injective gateSlots := by decide
noncomputable def gates:=RecoveryFocus.machine gateSlots RecoveryBoundedUniversalGates.machine

theorem gate_heads (out : List Bool) (j : Fin 29) :
    heads out (gateSlots j)=PCPPNativeClauseBank.heads out j := by
  fin_cases j <;> rfl

theorem gate_tapes (index base C D value limit total L left right : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedConstant address : List Bool) (count : ℕ) (j : Fin 29) :
    data index base C D value limit total L out source secondIndex
      (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count (gateSlots j)=
      RecoveryBoundedUniversalGates.data left right C out j := by
  fin_cases j <;> first
  | rfl
  | exact (ZeroPadding.pad_zero _).symm

theorem gate_install (index base C D value limit total L left right : ℕ) (out result source : List Bool) (secondIndex : ℕ)
    (savedConstant address : List Bool) (count : ℕ) :
    install gateSlots (data index base C D value limit total L out source secondIndex
      (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count)
      (RecoveryBoundedUniversalGates.data left right C result)=
      data index base C D value limit total L result source secondIndex
        (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count := by
  apply HierarchyWidth.install_eq gateSlots gate_injective
  · exact gate_tapes index base C D value limit total L left right result source secondIndex savedConstant address count
  · intro i hi
    have h20 : i≠20:=fun h=>hi 20 h.symm
    simp only [run_data_override,if_neg h20]

theorem gates_run (index base C D value limit total L left right W : ℕ) (out source : List Bool) (secondIndex : ℕ)
    (savedConstant address : List Bool) (count : ℕ) (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom gates (RecoveryBoundedUniversalGates.budget left right C)
      ⟨gates.start,heads out,data index base C D value limit total L out source secondIndex
        (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count⟩=some r ∧
      r.steps ≤ RecoveryBoundedUniversalGates.budget left right C ∧
      r.final.heads=heads (out++RecoveryBoundedUniversalGates.emitted left right) ∧
      r.final.tapes=data index base C D value limit total L (out++RecoveryBoundedUniversalGates.emitted left right) source secondIndex
        (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count := by
  obtain ⟨p,hp,ps,ph,pt⟩:=RecoveryBoundedUniversalGates.padded_run left right W C out hl hr hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock gateSlots gate_injective RecoveryBoundedUniversalGates.machine _
    (heads out) (data index base C D value limit total L out source secondIndex
      (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count)
    ⟨RecoveryBoundedUniversalGates.machine.start,PCPPNativeClauseBank.heads out,RecoveryBoundedUniversalGates.data left right C out⟩
    (gate_heads out) (gate_tapes index base C D value limit total L left right out source secondIndex savedConstant address count) p hp
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,gateSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (gate_heads _ j).symm
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      have h20 : i≠20:=fun h=>hi ⟨20,h.symm⟩
      simp only [heads_override,if_neg h20]
  · have he:=HierarchyWidth.install_eq gateSlots gate_injective
      (data index base C D value limit total L out source secondIndex
        (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true)) savedConstant address count)
      r.final.tapes _ (by intro j;rw [rt j,pt]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    exact gate_install _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedNodeAddress
