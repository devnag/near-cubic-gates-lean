import Proof.Amplification.RecoveryTseitinReferenceCold

/-! A single cubic bound covers all four physically generated references. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_budget_bound (arity index left right : Nat) :
    coldBudget arity index left right≤34359738368*(arity+index+left+right+1)^3 := by
  let n:=arity+index+left+right+1
  have h (m : Nat) (hm : m+1≤n) : RecoveryTseitinTautology.Cold.budget m≤4294967296*n^3 :=
    (RecoveryTseitinTautology.Cold.budget_bound m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 3))
  have h0:=h (arity+index) (by dsimp [n]; omega)
  have h1:=h left (by dsimp [n]; omega)
  have h2:=h (arity+left) (by dsimp [n]; omega)
  have h3:=h (arity+right) (by dsimp [n]; omega)
  have hn : 1≤n := by dsimp [n]; omega
  have hn3 : n≤n^3 := by nlinarith [sq_nonneg (n-1 : Int)]
  change (6*arity+2*index+2*left+2*right+20)+1+
    (RecoveryTseitinTautology.Cold.budget (arity+index)+1+
    (RecoveryTseitinTautology.Cold.budget left+1+
    (RecoveryTseitinTautology.Cold.budget (arity+left)+1+
    (RecoveryTseitinTautology.Cold.budget (arity+right)+1+0))))≤34359738368*n^3
  have hs : 6*arity+2*index+2*left+2*right+25≤32*n := by dsimp [n]; omega
  omega

end NearCubicWires.RepairSource.RecoveryTseitinReferences
