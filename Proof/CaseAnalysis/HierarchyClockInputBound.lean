import Proof.CaseAnalysis.HierarchyClockInput
import Proof.Hierarchy.HierarchyReductionTime

/-! Sufficient fixed polynomial bound for the actual recovery clock field.
The existing short arithmetic bound implies this C.12 envelope directly. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyClock.Input
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (k C : Nat):=
  HierarchyReduction.runtimeCoefficient k C 0 []+8*(k+2+C.bits.length+3)+12

theorem budget_bound (k C : Nat) (bits : List Bool) :
    budget (k+2) C bits≤coefficient k C*(bits.length+1)^3:=by
  have hraw : HierarchyFromInput.budget (k+2) C bits≤HierarchyReduction.budget k C 0 [] bits:=by
    unfold HierarchyReduction.budget
    omega
  have hb:=hraw.trans (HierarchyReduction.budget_bound k C 0 [] bits)
  have hl:=HierarchyBinary.ell_linear bits.length
  have hpoly : HierarchyFromInput.budget (k+2) C bits≤
      HierarchyReduction.runtimeCoefficient k C 0 []*(bits.length+1)^3:=by
    apply hb.trans
    calc
      _≤HierarchyReduction.runtimeCoefficient k C 0 []*(bits.length+1)*(bits.length+1)^2:=by gcongr
      _=_:=by ring
  have hw : HierarchyBinary.width C (k+2) bits.length≤(k+2+C.bits.length+3)*(bits.length+1):=by
    unfold HierarchyBinary.width
    nlinarith
  have hx : bits.length+1≤(bits.length+1)^3:=Nat.le_self_pow (by decide) _
  have h1 : 1≤(bits.length+1)^3:=Nat.one_le_pow _ _ (by omega)
  have hw3:=hw.trans (Nat.mul_le_mul_left (k+2+C.bits.length+3) hx)
  unfold budget coefficient
  nlinarith

end NearCubicWires.RepairSource.CloseoutHierarchyClock.Input
