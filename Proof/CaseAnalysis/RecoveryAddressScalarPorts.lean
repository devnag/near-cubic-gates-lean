import Proof.CaseAnalysis.RecoveryAddressPorts

/-! The common address tail changes only five named scalar/stack cells.
This literal identity lets its caller preserve the remaining bank directly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fixedData (C D limit : ℕ) (out source : List Bool) (retained : ℕ):=
  data 0 0 C D 0 limit false out source [] retained

theorem data_override (index base C D value limit : ℕ) (flag : Bool)
    (out source stack : List Bool) (retained : ℕ) :
    data index base C D value limit flag out source stack retained=
      fun i=>if i=1 then ZeroPadding.pad C (List.replicate index true)
        else if i=25 then List.replicate base true
        else if i=29 then ZeroPadding.pad C [flag]
        else if i=34 then ZeroPadding.pad C (List.replicate value true)
        else if i=38 then stack else fixedData C D limit out source retained i := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
