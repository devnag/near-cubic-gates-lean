import Proof.CaseAnalysis.RecoverySuppliersPrepared

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem hierarchy_value (k d : ℕ) : (hierarchyPort source k d).val=158:=by
  simp only [hierarchyPort,countSlots,RecoveryBoundedColdHierarchyDock.Count.prior,
    RecoveryBoundedColdHierarchyDock.inputPort,original_fresh,RecoveryBoundedColdHierarchyDock.fresh,
    Fin.val_castAdd,Fin.val_natAdd]
  rfl

theorem bits_above (k d : ℕ) :
    158 < (rBitsPort source k d).val ∧ 158 < (qBitsPort source k d).val:=by
  have hr : 0 < (HierarchyStreams.bitsR source k).val:=HierarchyStreams.slot_positive source k _
  have hq : 0 < (HierarchyStreams.bitsQ source k).val:=HierarchyStreams.slot_positive source k _
  constructor
  all_goals
    simp only [rBitsPort,qBitsPort,countSlots,RecoveryBoundedColdHierarchyDock.Count.prior,
      RecoveryBoundedColdHierarchyDock.rBitsPort,RecoveryBoundedColdHierarchyDock.qBitsPort,
      original_fresh,RecoveryBoundedColdHierarchyDock.fresh,
      Fin.val_castAdd,Fin.val_natAdd]
    simp only [HierarchyStreams.old,Fin.val_castAdd]
    omega

theorem final_inner (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool)
    (i : Fin (tapes source k d)) (hlo : 158 ≤ i.val) (hhi : i.val < base source k+1)
    (hr : i≠rBitsPort source k d) (hq : i≠qBitsPort source k d) :
    fullData source k d A C P F i=capacityData source k d A C i:=by
  have hn (j : Fin 158) : i≠old source k d j:=by
    intro he
    have hj:=j.isLt
    have hv:=congrArg Fin.val he
    change i.val=j.val at hv
    omega
  exact (install_other _ _ _ _ (full_away source k d i
    (hn 153) (hn 155) (hn 152) (by omega))).trans
    (install_other _ _ _ _ (projection_away source k d i (Or.inr (by omega)) hr hq
      (hn 76) (hn 115) (hn 153) (hn 156) (Or.inl (by omega))))

theorem final_hierarchy (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool) :
    fullData source k d A C P F (hierarchyPort source k d)=A (hierarchyPort source k d):=by
  have hv:=hierarchy_value source k d
  have hb:=base_large source k
  obtain ⟨hr,hq⟩:=bits_above source k d
  rw [final_inner source k d A C P F _ (by omega) (by omega)
    (by intro he;have hh:=congrArg Fin.val he;omega)
    (by intro he;have hh:=congrArg Fin.val he;omega)]
  exact capacity_inner source k d A C _ (by omega) (by omega)

theorem final_w (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool) :
    fullData source k d A C P F (wPort source k d)=C 0:=by
  have hv : (wPort source k d).val=base source k:=rfl
  have hb:=base_large source k
  obtain ⟨_,hr,_,hq⟩:=bits_range source k d
  rw [final_inner source k d A C P F _ (by omega) (by omega)
    (by intro he;have hh:=congrArg Fin.val he;omega)
    (by intro he;have hh:=congrArg Fin.val he;omega)]
  exact install_slot _ (capacity_injective source k d) _ _ 0

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
