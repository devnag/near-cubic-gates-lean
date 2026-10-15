import Proof.CaseAnalysis.CommonPrepare

/-! The common preparation is polynomial in the explicit final table length.
All parameters are fixed before the address and refuter answer are supplied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
open LocalBitMultitape RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def coefficient (k CH A B0 : ℕ):=
  CloseoutCapacity.coefficient A B0+CloseoutHierarchyRequest.coefficient k CH+1
def degree (A : ℕ):=A+4

theorem coefficient_pos (k CH A B0 : ℕ) : 1≤coefficient k CH A B0:=by
  unfold coefficient
  omega

theorem budget_bound (k CH A B0 : ℕ) (address answer : List Bool)
    (hanswer : answer.length≤2^address.length) :
    budget k CH A B0 address answer≤
      coefficient k CH A B0*(2^address.length+1)^(degree A):=by
  let x:=2^address.length+1
  have hx : 1≤x:=by dsimp [x];omega
  have hcapPower : x^(A+1)≤x^(degree A):=
    Nat.pow_le_pow_right hx (by unfold degree;omega)
  have hrequestPower : (answer.length+1)^3≤x^(degree A):=
    (Nat.pow_le_pow_left (by dsimp [x];omega) 3).trans
      (Nat.pow_le_pow_right hx (by unfold degree;omega))
  have hcap:=(CloseoutCapacity.budget_bound A B0 address).trans
    (Nat.mul_le_mul_left (CloseoutCapacity.coefficient A B0) hcapPower)
  have hreq:=(CloseoutHierarchyRequest.budget_bound k CH answer).trans
    (Nat.mul_le_mul_left (CloseoutHierarchyRequest.coefficient k CH) hrequestPower)
  have h1 : 1≤x^(degree A):=Nat.one_le_pow _ _ hx
  change budget k CH A B0 address answer≤coefficient k CH A B0*x^(degree A)
  unfold budget coefficient
  nlinarith

theorem polynomial_run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (A B0 : ℕ)
    (address answer : List Bool) (hanswer : answer.length≤2^address.length) : ∃ out,
    ClockJoin.ReadyRun (machine k H.coefficient A B0)
      (coefficient k H.coefficient A B0*(2^address.length+1)^(degree A))
      (input k address answer) out ∧
    out (addressSlot k)=frame address ∧
    out (capacitySlot k)=List.replicate (CloseoutCapacity.capacity A B0 address.length) true ∧
    out (hierarchySlot k)=frame answer++frame (H.time answer.length).bits:=by
  obtain ⟨out,hr,haddress,hW,hword⟩:=run H A B0 address answer
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr
    (budget_bound k H.coefficient A B0 address answer hanswer),haddress,hW,hword⟩

end
end NearCubicWires.RepairOrdinary.CloseoutCommonPrepare
