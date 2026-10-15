import Proof.CaseAnalysis.HierarchyRequest
import Proof.CaseAnalysis.HierarchyClockInputBound

/-! The whole genuine-input request builder has a sufficient fixed cubic
bound. This includes the canonical clock field and both paid field copies;
the common recovery program can use the original Case1 request directly. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyRequest
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient (k C : Nat) :=
  CloseoutHierarchyClock.Input.coefficient k C +
    8 * (k + 2 + C.bits.length + 4) + 17

theorem budget_bound (k C : Nat) (bits : List Bool) :
    budget k C bits ≤ coefficient k C * (bits.length + 1)^3 := by
  have hc := CloseoutHierarchyClock.Input.budget_bound k C bits
  have hl := HierarchyBinary.ell_linear bits.length
  have hw : HierarchyBinary.width C (k + 2) bits.length ≤
      (k + 2 + C.bits.length + 3) * (bits.length + 1) := by
    unfold HierarchyBinary.width
    nlinarith
  have ht := CanonicalPositiveOutput.nat_bits_length_le
    (HierarchyBinary.width C (k + 2) bits.length)
    (C * (bits.length^(k + 2) + 1))
    (HierarchyBinary.bound_fits C (k + 2) bits.length)
  have hx : bits.length + 1 ≤ (bits.length + 1)^3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ (bits.length + 1)^3 := Nat.one_le_pow _ _ (by omega)
  have ht3 := ht.trans (hw.trans
    (Nat.mul_le_mul_left (k + 2 + C.bits.length + 3) hx))
  unfold budget RecoveryCaseOneEntryPair.budget
    RecoveryPCPFormulaResumeSearchPair.budget coefficient
  nlinarith

end NearCubicWires.RepairSource.CloseoutHierarchyRequest
