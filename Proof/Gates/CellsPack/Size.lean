import Proof.Gates.CellsPack.Lang
import Proof.Gates.CellsPack.Bounds
import Proof.Gates.CellsSys.Final

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CellsPack

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.SystemsPhase (M1_lt A_lt factor_lt factors_sum_le n4p)

theorem size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

section R
variable {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT)

theorem spec_r : Spec cT (header r.c) r.p := selectParams_spec cT (header r.c) r.p r.hp

theorem J_le_r : r.p.J ≤ r.c.n + 1 := (J_le_Jmax r.c r.p (spec_r r)).trans (Jmax_le r.c r.p r.adm (spec_r r))

theorem deltaBound_lt : deltaBound r.c r.p < 2 ^ (bigOf B1 B2 r.c.n + 5 * r.c.n + 8) := by
  have hb := cellN_bits_le r
  set Bg := bigOf B1 B2 r.c.n
  have hM := M1_lt hb
  have hA := A_lt hb
  have hf := factors_sum_le hb (factors_length (spec_r r))
  have hJ := J_le_r r
  have hW : r.c.W ≤ 2 * r.c.n ^ 4 := r.adm.2.2.2.2.2.2.1
  have h4 := n4p r.c.n
  have hJ2 : r.p.J + 3 ≤ 2 ^ (r.c.n + 3) := by
    have := Nat.lt_two_pow_self (n := r.c.n + 3); omega
  have e1 : r.p.M1 + r.p.A + r.p.factors.sum + 1 ≤ 2 ^ Bg * 2 ^ (r.c.n + 3) := by
    have : r.p.factors.sum ≤ r.p.J * 2 ^ Bg := hf
    have h1 : 1 ≤ 2 ^ Bg := Nat.one_le_two_pow
    have : (r.p.J + 3) * 2 ^ Bg ≤ 2 ^ (r.c.n + 3) * 2 ^ Bg := Nat.mul_le_mul_right _ hJ2
    nlinarith
  have e2 : r.c.W + 1 ≤ 2 ^ (4 * r.c.n + 3) := by omega
  unfold deltaBound
  calc 2 * (r.p.M1 + r.p.A + r.p.factors.sum + 1) * (r.c.W + 1) ≤ 2 * (2 ^ Bg * 2 ^ (r.c.n + 3)) * 2 ^ (4 * r.c.n + 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
    _ = 2 ^ (Bg + 5 * r.c.n + 7) := by
        rw [show Bg + 5 * r.c.n + 7 = 1 + Bg + (r.c.n + 3) + (4 * r.c.n + 3) by ring, pow_add, pow_add, pow_add]; ring
    _ < 2 ^ (Bg + 5 * r.c.n + 8) := Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem recWidth_le : recWidth r.c r.p r.wt ≤
    r.c.n + (2 * r.c.n + 4) * (2 * r.c.n + 7) + (r.c.n + 2 * r.c.n * (bigOf B1 B2 r.c.n + 5 * r.c.n + 8) + 1) := by
  have hs := spec_r r
  obtain ⟨w, hw⟩ := r.hw
  have hk : r.p.k ≤ r.c.n := k_le_n r.c r.p hs
  have hJ := J_le_r r
  have hP := P_le_n r.c r.p hs
  have hrc := roleCount_le_two r.c
  have hcb : cellBits r.wt.I ≤ r.c.n := by
    unfold cellBits outerCoords; rw [Finset.length_sort]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hkb : keyBits r.p ≤ 2 * r.c.n + 4 := (size_le_self _).trans (by omega)
  have hkl : keyLen r.c r.p ≤ 2 * r.c.n + 7 := by
    unfold keyLen
    have : roleCount r.c.kind * (r.p.J + 1) ≤ 2 * (r.c.n + 2) := Nat.mul_le_mul hrc (by omega)
    omega
  have hsz : Nat.size (deltaBound r.c r.p) ≤ bigOf B1 B2 r.c.n + 5 * r.c.n + 8 := Nat.size_le.mpr (deltaBound_lt r)
  have hvw : valueWidth r.c r.p ≤ r.c.n + 2 * r.c.n * (bigOf B1 B2 r.c.n + 5 * r.c.n + 8) + 1 := by
    unfold valueWidth
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hk) hsz
    omega
  unfold recWidth
  have := Nat.mul_le_mul hkb hkl
  omega

theorem wdNeed_le : wdNeed r.c r.p r.wt (bigOf B1 B2 r.c.n) ≤ 2 ^ 22 * (r.c.n + 1) ^ (B1 + B2 + 10) := by
  have hJ := J_le_r r
  have hR := recWidth_le r
  set Y := r.c.n + 1 with hY
  set Q := Y ^ (B1 + B2 + 8) with hQ
  have hY1 : 1 ≤ Y := by omega
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ hY1
  have hBg : bigOf B1 B2 r.c.n = 2 ^ 10 * Q := rfl
  have hQ10 : Y ^ (B1 + B2 + 10) = Q * Y ^ 2 := by rw [hQ, ← pow_add]
  have hYQ : Y ≤ Q * Y := Nat.le_mul_of_pos_left _ hQ1
  have hY2 : Y * Y = Y ^ 2 := (pow_two Y).symm
  rw [hBg] at hR ⊢
  unfold wdNeed
  rw [hQ10]
  have hn : r.c.n ≤ Y := by omega
  have a1 : (r.p.J + 4) * (2 ^ 10 * Q + r.c.n + 16) ≤ 5 * Y * (2 ^ 10 * Q + 17 * Q * Y) := by
    apply Nat.mul_le_mul (by omega)
    have : r.c.n + 16 ≤ 17 * Q * Y := by nlinarith
    omega
  have a2 : 2 * r.c.n * (2 ^ 10 * Q + 5 * r.c.n + 8) ≤ 2 * Y * (2 ^ 10 * Q + 13 * Q * Y) := by
    apply Nat.mul_le_mul (by omega)
    have : 5 * r.c.n + 8 ≤ 13 * Q * Y := by nlinarith
    omega
  have a3 : (2 * r.c.n + 4) * (2 * r.c.n + 7) ≤ 63 * (Q * Y ^ 2) := by
    have : (2 * r.c.n + 4) * (2 * r.c.n + 7) ≤ (4 * Y) * (7 * Y) := Nat.mul_le_mul (by omega) (by omega)
    have : Y ^ 2 ≤ Q * Y ^ 2 := Nat.le_mul_of_pos_left _ hQ1
    nlinarith
  have a4 : Y ≤ Q * Y ^ 2 := by nlinarith
  have e1 : 5 * Y * (2 ^ 10 * Q + 17 * Q * Y) = 5120 * (Q * Y) + 85 * (Q * Y ^ 2) := by ring
  have e2 : 2 * Y * (2 ^ 10 * Q + 13 * Q * Y) = 2048 * (Q * Y) + 26 * (Q * Y ^ 2) := by ring
  have e3 : Q * Y ≤ Q * Y ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  have e4 : 256 * (r.p.J + 4) * (2 ^ 10 * Q + r.c.n + 16) = 256 * ((r.p.J + 4) * (2 ^ 10 * Q + r.c.n + 16)) := by ring
  rw [e4]
  omega

end R

end NearCubicGates.Close.CellsPack
