import Proof.Gates.CellsGatherE.Emit5

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

/-- The widths the emission needs, from `wdNeed ≤ Wd`. -/
theorem emit_widths {cT B1 B2 : ℕ} (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (w : List Bool)
    (hs : Spec cT (header c) p) (hw : decodeWitness c p w = some wt) (hadm : c.Admitted B1 B2)
    (hWd : wdNeed c p wt Big ≤ C.Wd) :
    2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) < 2 ^ C.Wd ∧
    2 ^ valueWidth c p * 2 ^ keyW c p < 2 ^ C.Wd ∧
    2 * p.hE + roleCount c.kind * (p.J + 1) < 2 ^ C.Wd ∧
    (reqIds c p).length < 2 ^ C.Wd ∧ (CounterMachine.cellN c p wt).length < 2 ^ C.Wd ∧
    p.J ≤ c.n + 1 ∧ p.hE ≤ c.n := by
  have hwd : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hrw : recWidth c p wt = cellBits wt.I + keyW c p + valueWidth c p := rfl
  have hJ : p.J ≤ c.n + 1 := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hP := P_le_n c p hs
  have hE : p.hE ≤ c.n := by rw [hs.hE_eq]; omega
  have hrc : roleCount c.kind ≤ 2 := by cases c.kind <;> decide
  have hn : 256 * (c.n + 16) ≤ 256 * (p.J + 4) * (Big + c.n + 16) := by nlinarith
  have hA : 2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) < 2 ^ C.Wd := by
    rw [show 2 * (2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p) = 2 ^ (valueWidth c p + 2 * keyW c p + 1) by ring]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hK1 : 1 ≤ 2 ^ keyW c p := Nat.one_le_two_pow
  have hB : 2 ^ valueWidth c p * 2 ^ keyW c p ≤ 2 ^ valueWidth c p * 2 ^ keyW c p * 2 ^ keyW c p :=
    Nat.le_mul_of_pos_right _ hK1
  have hlt : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hrc2 : roleCount c.kind * (p.J + 1) ≤ 2 * (p.J + 1) := Nat.mul_le_mul_right _ hrc
  refine ⟨hA, by omega, by omega, reqIds_lt_pow c p wt hs Big C.Wd hWd, ?_, hJ, hE⟩
  exact lt_of_lt_of_le (cellN_len_lt c p wt hadm hs w hw) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The arithmetic of the cost bound. -/
theorem cost_arith (R N P BW Rv n d q S0 : ℕ) (hP : P ≤ N) (hN : N ≤ 70 * (n + 1) ^ 5) (hd : d ≤ 2 * n + 4)
    (hRv : Rv ≤ 2 * (BW * n ^ 3)) (hS : S0 ≤ R + Rv + N) :
    20 + (P * (6 * N + 7 * d + 40) + 30) + (S0 + 1) + (R * 25 + 10) + q + (N * 5 + 12) + 5 ≤
      100000 * (R + BW + 1) * (n + 2) ^ 10 + q := by
  set X5 := (n + 2) ^ 5 with hX5
  have hX10 : (n + 2) ^ 10 = X5 * X5 := by rw [hX5, ← pow_add]
  have h15 : 1 ≤ X5 := Nat.one_le_pow _ _ (by omega)
  have hn5 : n ≤ X5 := by
    calc n ≤ n + 2 := by omega
      _ = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ X5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN' : N ≤ 70 * X5 := hN.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hn3 : n ^ 3 ≤ X5 * X5 := by
    calc n ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + 2) ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = X5 * X5 := hX10
  rw [hX10]
  have h1 : P * (6 * N + 7 * d + 40) ≤ (70 * X5) * (502 * X5) :=
    Nat.mul_le_mul (hP.trans hN') (by omega)
  have h2 : Rv ≤ 2 * (BW * (X5 * X5)) := hRv.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hn3))
  have h3 : 1 ≤ X5 * X5 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h4 : R ≤ R * (X5 * X5) := Nat.le_mul_of_pos_right _ h3
  have h5 : X5 ≤ X5 * X5 := Nat.le_mul_of_pos_right _ h15
  have e1 : (70 * X5) * (502 * X5) = 35140 * (X5 * X5) := by ring
  have e2 : 100000 * (R + BW + 1) * (X5 * X5) = 100000 * (R * (X5 * X5)) + 100000 * (BW * (X5 * X5)) +
      100000 * (X5 * X5) := by ring
  rw [e2]; rw [e1] at h1
  omega

end NearCubicGates.Close.Cells.RecordEmission
