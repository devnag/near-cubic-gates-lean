import Proof.CaseAnalysis.CaseTwoNativeConverter

/-! One fixed unary polynomial in the paid R and full size bound supplies
the whole canonical traversal. Its exponent is deliberately coarse. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdFits
open RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (R B : ℕ):=1048576*(R+B+1)^4

theorem allocation_le (R B : ℕ) :
    Traversal.allocation (boundedCircuitFieldLimit R B) (boundedCircuitDescriptionWidth R B) B≤capacity R B:=by
  let F:=R+B+1
  have hp : 1≤F:=by dsimp [F];omega
  have hB : B+1≤F:=by dsimp [F];omega
  have hF : F≤F^2:=by nlinarith
  have hw : (B+1)*(6+2*F)≤8*F^2:=by
    have ht : 6+2*F≤8*F:=by omega
    have hm:=Nat.mul_le_mul hB ht
    nlinarith only [hm]
  have hs : (B+1)*(6+2*F)+F+B+7≤32*F^2:=by nlinarith
  change 1024*((B+1)*(6+2*F)+F+B+7)^2≤1048576*F^4
  calc
    _≤1024*(32*F^2)^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
    _=1048576*F^4:=by ring

theorem fits_mono {C D F S M : ℕ} (h : Traversal.Fits C F S M) (hc : C≤D) : Traversal.Fits D F S M:=
  ⟨h.source.trans hc,h.offset.trans hc,h.count.trans hc,h.nine.trans hc,
    fun a b c ha hb hd=>(h.field a b c ha hb hd).trans hc⟩

theorem fits {R B : ℕ} (c : BooleanCircuit R) (hc : c.size≤B) :
    Traversal.Fits (capacity R B) (boundedCircuitFieldLimit R B)
      (canonicalBoundedCircuitDescription B c).length B:=by
  rw [canonicalBoundedCircuitDescription_length c hc]
  exact fits_mono (Traversal.allocation_fits _ _ _) (allocation_le R B)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.ColdFits
