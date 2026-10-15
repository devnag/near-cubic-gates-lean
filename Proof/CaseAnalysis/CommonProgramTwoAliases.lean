import Proof.CaseAnalysis.CommonProgramTwoPorts
import Proof.CaseAnalysis.CommonProgramRecoveryInput

/-! The actual Case2 input aliases are the same retained hierarchy word,
canonical description, final address, and original raw R/B recovery fields. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovery_inputs (p : Parameters) (j : Fin 3) :
    recoverySlot p (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree j)=
      prefixSlot p (prefixRecoveryFields p j):=by
  exact (congrArg (lift1 p) (CloseoutCommonPortBank.shared_slot _ _
    (RecoveryBoundedCold.sharedLocal_injective (source p) p.k p.degree) j)).trans
      (recovery_shared_prefix p j)

theorem two_hierarchy_alias (p : Parameters) :
    twoSlot p (twoLocal p 0)=
      recoverySlot p (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0):=by
  exact (two_inputs p 0).trans (recovery_inputs p 0).symm

theorem two_description_alias (p : Parameters) :
    twoSlot p (twoLocal p 1)=lift1 p (descriptionBank p):=two_inputs p 1
theorem two_address_alias (p : Parameters) :
    twoSlot p (twoLocal p 2)=lift0 p (address0 p):=two_inputs p 2
theorem two_r_alias (p : Parameters) :
    twoSlot p (twoLocal p 3)=lift1 p (scalarBank p 0):=two_inputs p 3
theorem two_b_alias (p : Parameters) :
    twoSlot p (twoLocal p 4)=lift1 p (scalarBank p 2):=two_inputs p 4

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
