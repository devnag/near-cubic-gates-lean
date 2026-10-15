import Proof.MachineModel.CountIndexPadded

/-! The already produced native capacity pays the actual index conversion.
The raw count is squared only within the subexponential mode preparation;
the table-sized capacity itself is never squared. -/
namespace NearCubicWires.ExtIncidence.CountIndex
open RepairOrdinary CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fits (n p F w N Q M : ℕ) (hQ : 1≤Q) (hM : M≤2^w) :
    budget w M+1≤capacity n p F w N Q := by
  let S:=scale n p F w N Q
  let U:=2^(w*(Q+1))
  have hS : 1≤S:=by dsimp [S,scale];omega
  have hw : w≤S:=by dsimp [S,scale];omega
  have hpow : S≤S^4:=by simpa only [pow_one] using Nat.pow_le_pow_right hS (by decide : 1≤4)
  have hU : 1≤U:=Nat.one_le_two_pow
  have hM2 : M^2≤U:=by
    calc
      M^2≤(2^w)^2:=Nat.pow_le_pow_left hM 2
      _=2^(w*2):=by rw [pow_mul]
      _≤U:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w (by omega))
  have hMU : M≤U:=by
    exact hM.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hUP : U≤S^4*U:=by nlinarith
  have hSP : S^4≤S^4*U:=by nlinarith
  change 16*M^2+72*M+8*w+42+1≤4096*S^4*U
  nlinarith

end NearCubicWires.ExtIncidence.CountIndex
