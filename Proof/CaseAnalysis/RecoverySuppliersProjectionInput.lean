import Proof.CaseAnalysis.RecoverySuppliersCapacityKeep

/-! The original projector receives exactly the retained R/Q frames, actual
normalized queries and newly paid B driver. All other inputs remain empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem projection_input (k d R Q B : ℕ) (word queries : List Bool) (W : ℕ)
    (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool)
    (hr : A (rBitsPort source k d)=frame R.bits) (hq : A (qBitsPort source k d)=frame Q.bits)
    (hquery : A (old source k d 106)=queries) (hB : O 45=List.replicate B true)
    (hblank : ∀ i : Fin 158,i≠70→i≠106→i≠157→ A (old source k d i)=[])
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ A i=input source k d word W i)
    (j : Fin 113) : capacityData source k d A O (projectionSlots source k d j)=
      RecoveryProjectionCold.input R Q B queries j:=by
  obtain ⟨hrlo,hrhi,hqlo,hqhi⟩:=bits_range source k d
  by_cases hbank : j.val<37
  · have hj37 : j≠37:=by intro he;have hv:=congrArg Fin.val he;change j.val=37 at hv;omega
    have hj65 : j≠65:=by intro he;have hv:=congrArg Fin.val he;change j.val=65 at hv;omega
    have hj104 : j≠104:=by intro he;have hv:=congrArg Fin.val he;change j.val=104 at hv;omega
    simp only [projectionSlots,dif_pos hbank,RecoveryProjectionCold.input,if_neg hj37,if_neg hj65]
    rw [capacity_old source k d A O ⟨78+j.val,by omega⟩
      (by intro he;have hv:=congrArg Fin.val he;change 78+j.val=154 at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;change 78+j.val=76 at hv;omega)
      (by intro he;have hv:=congrArg Fin.val he;change 78+j.val=77 at hv;omega)]
    by_cases hj28 : j=28
    · subst j
      simp only [if_pos]
      exact hquery
    · simp only [if_neg hj28,if_neg hj104]
      apply hblank ⟨78+j.val,by omega⟩
      · intro he;have hv:=congrArg Fin.val he;change 78+j.val=70 at hv;omega
      · intro he
        have hv:=congrArg Fin.val he
        change 78+j.val=106 at hv
        exact hj28 (Fin.ext (by omega))
      · intro he;have hv:=congrArg Fin.val he;change 78+j.val=157 at hv;omega
  by_cases hj37 : j.val=37
  · have he : j=37:=Fin.ext hj37
    subst j
    exact (capacity_inner source k d A O _ hrlo hrhi).trans hr
  by_cases hj65 : j.val=65
  · have he : j=65:=Fin.ext hj65
    subst j
    exact (capacity_inner source k d A O _ hqlo hqhi).trans hq
  by_cases hj104 : j.val=104
  · have he : j=104:=Fin.ext hj104
    subst j
    exact (capacity_b source k d A O).trans hB
  by_cases hj106 : j.val=106
  · have he : j=106:=Fin.ext hj106
    subst j
    exact (capacity_old source k d A O 115 (by decide) (by decide) (by decide)).trans
      (hblank 115 (by decide) (by decide) (by decide))
  by_cases hj109 : j.val=109
  · have he : j=109:=Fin.ext hj109
    subst j
    exact (capacity_old source k d A O 153 (by decide) (by decide) (by decide)).trans
      (hblank 153 (by decide) (by decide) (by decide))
  by_cases hj111 : j.val=111
  · have he : j=111:=Fin.ext hj111
    subst j
    exact (capacity_old source k d A O 156 (by decide) (by decide) (by decide)).trans
      (hblank 156 (by decide) (by decide) (by decide))
  · have h37 : j≠37:=fun he=>hj37 (congrArg Fin.val he)
    have h65 : j≠65:=fun he=>hj65 (congrArg Fin.val he)
    have h104 : j≠104:=fun he=>hj104 (congrArg Fin.val he)
    have h28 : j≠28:=by intro he;have hv:=congrArg Fin.val he;change j.val=28 at hv;omega
    simp only [projectionSlots,dif_neg hbank,if_neg hj37,if_neg hj65,if_neg hj104,
      if_neg hj106,if_neg hj109,if_neg hj111,RecoveryProjectionCold.input,
      if_neg h37,if_neg h65,if_neg h28,if_neg h104]
    have hf : base source k+1+49 ≤ (projectionWork source k d j).val:=by
      change base source k+1+49≤base source k+1+49+j.val
      omega
    rw [capacity_far source k d A O _ hf]
    exact (hfar _ (by omega)).trans (input_fresh source k d word W _ (by omega))

theorem projection_heads (k d : ℕ) (H : Fin (tapes source k d)→ℕ)
    (hold : ∀ i : Fin 158,H (old source k d i)=0)
    (hr : H (rBitsPort source k d)=0) (hq : H (qBitsPort source k d)=0)
    (hfar : ∀ i : Fin (tapes source k d),base source k ≤ i.val→ H i=0)
    (j : Fin 113) : H (projectionSlots source k d j)=0:=by
  dsimp only [projectionSlots]
  split_ifs
  · exact hold _
  · exact hr
  · exact hq
  · exact hold 76
  · exact hold 115
  · exact hold 153
  · exact hold 156
  · exact hfar _ (by change base source k≤base source k+1+49+j.val;omega)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
