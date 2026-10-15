import Proof.CaseAnalysis.CommonProgramPorts

/-! Recovery's canonical description and raw R/B lie in its unchanged
private bank, beyond the shared header. B is scalar2; scalar1 is capacity. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovery_old_large (p : Parameters) :
    1664≤RecoveryBoundedCold.oldTapes (source p) p.k p.degree:=Nat.le_add_right _ _

theorem scalar_bank_value (p : Parameters) (j : Fin 5) :
    (scalarBank p j).val=n0 p+(1659+j.val):=by
  let source':=source p
  let G:=RecoveryBoundedCold.oldTapes source' p.k p.degree
  have hh : 1664≤(RecoveryBoundedColdSourceGraph.hierarchyPort source' p.k p.degree).val:=by
    rw [RecoveryBoundedColdSourceGraph.hierarchy_fresh]
    exact Nat.le_add_right _ _
  have hw : 1664≤(RecoveryBoundedColdSourceGraph.wPort source' p.k p.degree).val:=by
    rw [RecoveryBoundedColdSourceGraph.w_fresh]
    exact Nat.le_add_right _ _
  have hG : 1664≤G:=recovery_old_large p
  have hj:=j.isLt
  have fresh : ∀ i,RecoveryBoundedCold.sharedLocal source' p.k p.degree i≠
      (RecoveryBoundedColdSourceGraph.graphSlots source' p.k p.degree (j.natAdd 1659)).castAdd 790:=by
    intro i he
    fin_cases i
    · have hv:=congrArg Fin.val he
      change (RecoveryBoundedColdSourceGraph.hierarchyPort source' p.k p.degree).val=1659+j.val at hv
      omega
    · have hv:=congrArg Fin.val he
      change (RecoveryBoundedColdSourceGraph.wPort source' p.k p.degree).val=1659+j.val at hv
      omega
    · have hv:=congrArg Fin.val he
      change G+356=1659+j.val at hv
      omega
  change (CloseoutCommonPortBank.slot _ _ _).val=_
  rw [CloseoutCommonPortBank.fresh_slot _ _ _ fresh]
  rfl

theorem description_bank_value (p : Parameters) :
    (descriptionBank p).val=n0 p+(RecoveryBoundedCold.oldTapes (source p) p.k p.degree+787):=by
  let G:=RecoveryBoundedCold.oldTapes (source p) p.k p.degree
  have hh : (RecoveryBoundedColdSourceGraph.hierarchyPort (source p) p.k p.degree).val<G:=
    (RecoveryBoundedColdSourceGraph.hierarchyPort (source p) p.k p.degree).isLt
  have hw : (RecoveryBoundedColdSourceGraph.wPort (source p) p.k p.degree).val<G:=
    (RecoveryBoundedColdSourceGraph.wPort (source p) p.k p.degree).isLt
  have fresh : ∀ i,RecoveryBoundedCold.sharedLocal (source p) p.k p.degree i≠
      (787 : Fin 790).natAdd G:=by
    intro i he
    fin_cases i
    · have hv:=congrArg Fin.val he
      change (RecoveryBoundedColdSourceGraph.hierarchyPort (source p) p.k p.degree).val=G+787 at hv
      omega
    · have hv:=congrArg Fin.val he
      change (RecoveryBoundedColdSourceGraph.wPort (source p) p.k p.degree).val=G+787 at hv
      omega
    · have hv:=congrArg Fin.val he
      change G+356=G+787 at hv
      omega
  change (CloseoutCommonPortBank.slot _ _ _).val=_
  rw [CloseoutCommonPortBank.fresh_slot _ _ _ fresh]
  rfl

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
