import Proof.CaseAnalysis.RecoverySuppliersProjection

/-! Exact projector outputs and the retained old/full-bound input fields.
Only the original projector bank and named scalar destinations are changed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem projection_old (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (i : Fin 158)
    (hbank : i.val<78 ∨ 115 ≤ i.val) (h76 : i≠76) (h115 : i≠115) (h153 : i≠153) (h156 : i≠156) :
    projectionData source k d A C P (old source k d i)=capacityData source k d A C (old source k d i):=by
  have hi:=i.isLt
  have hb:=base_large source k
  obtain ⟨hrlo,_hrhi,hqlo,_hqhi⟩:=bits_range source k d
  exact install_other _ _ _ _ (projection_away source k d _ hbank
    (by intro he;have hv:=congrArg Fin.val he;change i.val=(rBitsPort source k d).val at hv;omega)
    (by intro he;have hv:=congrArg Fin.val he;change i.val=(qBitsPort source k d).val at hv;omega)
    (fun he=>h76 (old_injective source k d he)) (fun he=>h115 (old_injective source k d he))
    (fun he=>h153 (old_injective source k d he)) (fun he=>h156 (old_injective source k d he))
    (Or.inl (by change i.val<base source k+1+49;omega)))

theorem projection_far (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (i : Fin (tapes source k d))
    (hi : base source k+1+49+113 ≤ i.val) : projectionData source k d A C P i=A i:=by
  have hb:=base_large source k
  obtain ⟨_hrlo,hrhi,_hqlo,hqhi⟩:=bits_range source k d
  have hn (j : Fin 158) : i≠old source k d j:=by
    intro he
    have hj:=j.isLt
    have hv:=congrArg Fin.val he
    change i.val=j.val at hv
    omega
  exact (install_other _ _ _ _ (projection_away source k d i (Or.inr (by omega))
    (by intro he;have hv:=congrArg Fin.val he;omega)
    (by intro he;have hv:=congrArg Fin.val he;omega)
    (hn 76) (hn 115) (hn 153) (hn 156) (Or.inr hi))).trans
      (capacity_far source k d A C i (by omega))

theorem projection_bank_data (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (i : Fin 37) :
    projectionData source k d A C P (old source k d ⟨78+i.val,by omega⟩)=P (RecoveryProjectionCold.bankSlots i):=by
  rw [←projection_bank source k d i]
  exact install_slot _ (projection_injective source k d) _ _ _

theorem projection_rows (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) :
    projectionData source k d A C P (old source k d 115)=P 106:=
  install_slot _ (projection_injective source k d) _ _ 106
theorem projection_raw_r (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) :
    projectionData source k d A C P (old source k d 153)=P 109:=
  install_slot _ (projection_injective source k d) _ _ 109
theorem projection_raw_q (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) :
    projectionData source k d A C P (old source k d 156)=P 111:=
  install_slot _ (projection_injective source k d) _ _ 111
theorem projection_backing (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) :
    projectionData source k d A C P (old source k d 76)=P 104:=
  install_slot _ (projection_injective source k d) _ _ 104

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
