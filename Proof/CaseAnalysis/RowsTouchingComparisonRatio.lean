import Proof.CaseAnalysis.RowsTouchingComplement

/-! For feasible nontrivial choices, cancel the common positive binomial
factor. The exact original comparison needs only the small remaining
coordinate counts as multipliers; no denominator table lookups. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Complement
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem adjacent_comparison (r t A B : ℕ) (ht:t≤r):
    (A*Nat.choose r t≤B*Nat.choose r (t+1)) ↔ (A*(t+1)≤B*(r-t)):=by
  have hp:0<Nat.choose r t:=Nat.choose_pos ht
  have hk:0<t+1:=by omega
  rw [←Nat.mul_le_mul_right_iff hk]
  rw [Nat.mul_assoc B,Nat.choose_succ_right_eq]
  rw [show A*Nat.choose r t*(t+1)=A*(t+1)*Nat.choose r t by ring]
  rw [show B*(Nat.choose r t*(r-t))=B*(r-t)*Nat.choose r t by ring]
  exact Nat.mul_le_mul_right_iff hp

theorem feasible_comparison (r k A B : ℕ) (hk:0<k) (hr:k≤r+1):
    (A*Nat.choose r (k-1)≤B*Nat.choose r k) ↔ (A*k≤B*(r+1-k)):=by
  have he:k-1+1=k:=by omega
  have hs:r-(k-1)=r+1-k:=by omega
  simpa only [he,hs] using adjacent_comparison r (k-1) A B (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Complement
