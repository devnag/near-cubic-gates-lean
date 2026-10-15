import Proof.CaseAnalysis.RecoverySuppliersFull

/-! The FULL-cap worker changes only its source, two outputs, and fresh work.
These coordinates retain the exact original prepared graph bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem full_old (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool)
    (i : Fin 158) (h153 : i≠153) (h155 : i≠155) (h152 : i≠152) :
    fullData source k d A C P F (old source k d i)=projectionData source k d A C P (old source k d i):=by
  have hi:=i.isLt
  have hb:=base_large source k
  exact install_other _ _ _ _ (full_away source k d _
    (fun he=>h153 (old_injective source k d he))
    (fun he=>h155 (old_injective source k d he))
    (fun he=>h152 (old_injective source k d he))
    (by change i.val < base source k+1+49+113;omega))

theorem full_r (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool) :
    fullData source k d A C P F (old source k d 153)=F (RecoveryFullBound.sourceSlot d):=by
  rw [←full_source source k d]
  exact install_slot _ (full_injective source k d) _ _ _
theorem full_raw_data (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool) :
    fullData source k d A C P F (old source k d 155)=F (RecoveryFullBound.rawSlot d):=by
  rw [←full_raw source k d]
  exact install_slot _ (full_injective source k d) _ _ _
theorem full_compare_data (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool) :
    fullData source k d A C P F (old source k d 152)=F (RecoveryFullBound.compareSlot d):=by
  rw [←full_compare source k d]
  exact install_slot _ (full_injective source k d) _ _ _

theorem final_original (k d : ℕ) (A : Fin (tapes source k d)→List Bool)
    (C : Fin 49→List Bool) (P : Fin 113→List Bool) (F : Fin (RecoveryFullBound.tapes d)→List Bool)
    (i : Fin 158) (hbank : i.val < 78 ∨ 115 ≤ i.val)
    (h76 : i≠76) (h77 : i≠77) (h115 : i≠115) (h152 : i≠152)
    (h153 : i≠153) (h154 : i≠154) (h155 : i≠155) (h156 : i≠156) :
    fullData source k d A C P F (old source k d i)=A (old source k d i):=by
  rw [full_old source k d A C P F i h153 h155 h152,
    projection_old source k d A C P i hbank h76 h115 h153 h156,
    capacity_old source k d A C i h154 h76 h77]

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
