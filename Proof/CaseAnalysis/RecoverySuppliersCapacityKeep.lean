import Proof.CaseAnalysis.RecoverySuppliersCapacity

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def capacityData (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool):=
  install (capacitySlots source k d) A O

theorem capacity_old (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool)
    (i : Fin 158) (h154 : i≠154) (h76 : i≠76) (h77 : i≠77) :
    capacityData source k d A O (old source k d i)=A (old source k d i):=by
  have hi:=i.isLt
  have hb:=base_large source k
  exact install_other _ _ _ _ (capacity_away source k d _
    (by intro he;have hv:=congrArg Fin.val he;change i.val=base source k at hv;omega)
    (fun he=>h154 (old_injective source k d he))
    (fun he=>h76 (old_injective source k d he))
    (fun he=>h77 (old_injective source k d he))
    (Or.inl (by change i.val<base source k+1;omega)))

theorem capacity_inner (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool)
    (i : Fin (tapes source k d)) (hlo : 158 ≤ i.val) (hhi : i.val<base source k) :
    capacityData source k d A O i=A i:=by
  have hn (j : Fin 158) : i≠old source k d j:=by
    intro he
    have hj:=j.isLt
    have hv:=congrArg Fin.val he
    change i.val=j.val at hv
    omega
  exact install_other _ _ _ _ (capacity_away source k d i
    (by intro he;have hv:=congrArg Fin.val he;change i.val=base source k at hv;omega)
    (hn 154) (hn 76) (hn 77) (Or.inl (by omega)))

theorem capacity_far (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool)
    (i : Fin (tapes source k d)) (hi : base source k+1+49 ≤ i.val) :
    capacityData source k d A O i=A i:=by
  have hb:=base_large source k
  have hn (j : Fin 158) : i≠old source k d j:=by
    intro he
    have hj:=j.isLt
    have hv:=congrArg Fin.val he
    change i.val=j.val at hv
    omega
  exact install_other _ _ _ _ (capacity_away source k d i
    (by intro he;have hv:=congrArg Fin.val he;change i.val=base source k at hv;omega)
    (hn 154) (hn 76) (hn 77) (Or.inr hi))

theorem capacity_c (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool) :
    capacityData source k d A O (old source k d 154)=O 7:=
  install_slot _ (capacity_injective source k d) _ _ 7
theorem capacity_b (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool) :
    capacityData source k d A O (old source k d 76)=O 45:=
  install_slot _ (capacity_injective source k d) _ _ 45
theorem capacity_log (k d : ℕ) (A : Fin (tapes source k d)→List Bool) (O : Fin 49→List Bool) :
    capacityData source k d A O (old source k d 77)=O 48:=
  install_slot _ (capacity_injective source k d) _ _ 48

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
