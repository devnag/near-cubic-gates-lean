import Proof.Gates.CounterMachine.CellTablesPack1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

section Block
variable {ns nr : ℕ} (cap : ℕ) (R : Fin 12 ↪ Fin nr) (I : Fin (ns + 1)) (G B : Fin nr)

def bkCCost (L f : ℕ) : ℕ := 23 * L * f + 25 * L + 3 * f + 20

theorem bkC_spec (hRG : ∀ j, R j ≠ G) (σ : WState ns nr) (L f n0 : ℕ) (hG : σ.val G = L) (h9 : σ.val (R 9) = f)
    (h2 : σ.val (R 2) = n0) (h6 : σ.val (R 6) = 0) (h10 : σ.val (R 10) = 0) (h11 : σ.val (R 11) = 0)
    (hcap : (L + 1) * f + L + n0 + 10 ≤ cap) :
    WXExec cap (bkC R G) σ ((σ.setv (R 9) 0).setv (R 2) (n0 - f * (L - 1))) (bkCCost L f) := by
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have c1 := addR_spec cap (A := G) (B := R 11) (T := R 6) (hRG 11).symm (hRG 6).symm (hR (by decide)) σ h6
    (by rw [h11, hG]; omega)
  rw [h11, hG, zero_add] at c1
  have c2 := WXExec.dec cap (R 11) (σ.setv (R 11) L) (by simp; omega)
  have e2 : (σ.setv (R 11) L).setv (R 11) ((σ.setv (R 11) L).val (R 11) - 1) = σ.setv (R 11) (L - 1) := by
    refine WState.eq rfl rfl ?_ rfl; funext r
    by_cases hr : r = R 11
    · subst hr; simp
    · simp [Function.update_of_ne hr]
  rw [e2] at c2
  have n119 := hR (show (11 : Fin 12) ≠ 9 by decide)
  have n1110 := hR (show (11 : Fin 12) ≠ 10 by decide)
  have n116 := hR (show (11 : Fin 12) ≠ 6 by decide)
  have n910 := hR (show (9 : Fin 12) ≠ 10 by decide)
  have n92 := hR (show (9 : Fin 12) ≠ 2 by decide)
  have n102 := hR (show (10 : Fin 12) ≠ 2 by decide)
  have n112 := hR (show (11 : Fin 12) ≠ 2 by decide)
  have hLf : (L - 1) * f ≤ (L + 1) * f := Nat.mul_le_mul_right _ (by omega)
  have c3 := mulL_spec cap (R 11) (R 9) (R 10) (R 6) n119 n1110 n116 n910 (hR (by decide)) (hR (by decide)) (L - 1)
    (σ.setv (R 11) (L - 1)) (by simp) (by simp [Function.update_of_ne n116.symm, h6]) (by omega)
    (by simp [Function.update_of_ne n1110.symm, Function.update_of_ne n119.symm, h10, h9]; omega)
  have v9 : (σ.setv (R 11) (L - 1)).val (R 9) = f := by simp [Function.update_of_ne n119.symm, h9]
  have v10 : (σ.setv (R 11) (L - 1)).val (R 10) = 0 := by simp [Function.update_of_ne n1110.symm, h10]
  rw [v9, v10, zero_add] at c3
  set ρ := ((σ.setv (R 11) (L - 1)).setv (R 11) 0).setv (R 10) ((L - 1) * f) with hρ
  have c4 := Cells.clearR_spec cap (R 9) f ρ (by simp [ρ, Function.update_of_ne n910, Function.update_of_ne n119.symm,
    h9]) (by nlinarith)
  have c5 := subL_spec cap (R 10) (R 2) n102 ((L - 1) * f) (ρ.setv (R 9) 0)
    (by simp [ρ, Function.update_of_ne n910.symm]) (by omega)
    (by simp [ρ, Function.update_of_ne n92.symm, Function.update_of_ne n102.symm, Function.update_of_ne n112.symm, h2];
        omega)
  have v2 : (ρ.setv (R 9) 0).val (R 2) = n0 := by
    simp [ρ, Function.update_of_ne n92.symm, Function.update_of_ne n102.symm, Function.update_of_ne n112.symm, h2]
  rw [v2] at c5
  refine (WXExec.seq c1 (WXExec.seq c2 (WXExec.seq c3 (WXExec.seq c4 c5)))).cast cap ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [ρ, WState.setv_val, Function.update_apply]
    by_cases r2 : r = R 2
    · subst r2; simp [n92.symm, n102.symm, n112.symm]; ring_nf
    · by_cases r9 : r = R 9
      · subst r9; simp [n92, n910, n119.symm]
      · by_cases r10 : r = R 10
        · subst r10; simp [n102, n910.symm, n1110.symm, h10]
        · by_cases r11 : r = R 11
          · subst r11; simp [n112, n119, n1110, h11]
          · simp [r2, r9, r10, r11]
  · simp only [bkCCost]
    have : (L - 1) * (18 * f + 7) ≤ L * (18 * f + 7) := Nat.mul_le_mul_right _ (by omega)
    have : 5 * ((L - 1) * f) ≤ 5 * (L * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    nlinarith

theorem bkD_spec (hRB : ∀ j, R j ≠ B) (σ : WState ns nr) (b m : ℕ) (hB : σ.val B = b) (h2 : σ.val (R 2) = m)
    (h1 : σ.val (R 1) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (hcap : 2 ^ m * b ≤ cap)
    (hcap2 : 2 * m ≤ cap) :
    WXExec cap (bkD R B) σ ((σ.setv B (2 ^ m * b)).setv (R 2) 0) (m * (60 * (2 ^ m * b) + 19) + 10 * m + 5) := by
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have hnd : [B, R 4, R 3, R 2, R 1].Nodup := by
    simp [List.nodup_cons, Ne.symm (hRB 4), Ne.symm (hRB 3), Ne.symm (hRB 2), Ne.symm (hRB 1)]
  have d1 := Cells.pw2_spec cap (X := B) (Y := R 4) (T := R 3) (G := R 2) (G2 := R 1) hnd 1 σ h4 h3 h1
    (by rw [h2, hB, one_mul]; exact hcap) (by rw [h2]; exact hcap2)
  rw [h2, hB, one_mul] at d1
  have d2 := Cells.clearR_spec cap (R 2) m (σ.setv B (2 ^ m * b)) (by simp [Function.update_of_ne (hRB 2), h2])
    (by omega)
  have e : m * (60 * (2 ^ m * b) + 11 * 1 + 8) = m * (60 * (2 ^ m * b) + 19) := by ring
  exact (WXExec.seq d1 d2).cast cap rfl (by omega)

/-- The whole block's cost (`f` = the factor `2 + c_T + 3·size(L − 2)`, `m = n₀ − k'`, `b` the call bound). -/
def bkBlkCost (L cT n0 b : ℕ) : ℕ :=
  bkACost L + 1 + (bkBCost L cT + 1 + (bkCCost L (2 + cT + 3 * Nat.size (L - 2)) + 1 +
    ((n0 - kLow cT L) * (60 * (2 ^ (n0 - kLow cT L) * b) + 19) + 10 * (n0 - kLow cT L) + 5)))

/-- **The block**: `B := 2^{n₀ − k'}·B`, everything else as found. -/
theorem bkBlk_spec (hRG : ∀ j, R j ≠ G) (hRB : ∀ j, R j ≠ B) (hGB : G ≠ B) (cT : ℕ) (σ : WState ns nr) (n0 b : ℕ)
    (rest : List Bool) (hI : σ.st I = RepairOrdinary.frame (natWord n0 ++ rest)) (hh : σ.sh I = 0)
    (hG : σ.val G = natBitLength n0) (hB : σ.val B = b) (hz : ∀ j, σ.val (R j) = 0)
    (hcap : 2 ^ (natBitLength n0 + 2) + 8 * natBitLength n0 + 10 ≤ cap)
    (hcap2 : (natBitLength n0 + 1) * (2 + cT + 3 * natBitLength n0) + 4 * natBitLength n0 + cT + 2 * n0 + 30 ≤ cap)
    (hcap3 : 2 ^ (n0 - kLow cT (natBitLength n0)) * b ≤ cap) :
    WXExec cap (bkBlk R I G B cT) σ (σ.setv B (2 ^ (n0 - kLow cT (natBitLength n0)) * b))
      (bkBlkCost (natBitLength n0) cT n0 b) := by
  set L := natBitLength n0 with hL
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have sA := bkA_spec cap R I G hRG σ n0 rest hI hh hG hz hcap
  rw [← hL] at sA
  set σ1 := σ.setv (R 2) n0 with hσ1
  have z1 : ∀ j, j ≠ 2 → σ1.val (R j) = 0 := fun j hj => by simp [σ1, Function.update_of_ne (hR hj), hz]
  have g1 : σ1.val G = L := by simp [σ1, Function.update_of_ne (hRG 2).symm, hG]
  set S := Nat.size (L - 2) with hS
  have hSL : S ≤ L - 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have sB := bkB_spec cap R G hRG cT σ1 L g1 (z1 6 (by decide)) (z1 7 (by decide)) (z1 8 (by decide))
    (z1 9 (by decide)) (by omega)
  set σ2 := σ1.setv (R 9) (2 + cT + 3 * S) with hσ2
  have hf : 2 + cT + 3 * S ≤ 2 + cT + 3 * L := by omega
  have hfL : (L + 1) * (2 + cT + 3 * S) ≤ (L + 1) * (2 + cT + 3 * L) := Nat.mul_le_mul_left _ hf
  have sC := bkC_spec cap R G hRG σ2 L (2 + cT + 3 * S) n0 (by simp [σ2, Function.update_of_ne (hRG 9).symm, g1])
    (by simp [σ2]) (by simp [σ2, σ1, Function.update_of_ne (hR (show (2 : Fin 12) ≠ 9 by decide))])
    (by simp [σ2, Function.update_of_ne (hR (show (6 : Fin 12) ≠ 9 by decide)), z1 6 (by decide)])
    (by simp [σ2, Function.update_of_ne (hR (show (10 : Fin 12) ≠ 9 by decide)), z1 10 (by decide)])
    (by simp [σ2, Function.update_of_ne (hR (show (11 : Fin 12) ≠ 9 by decide)), z1 11 (by decide)])
    (by omega)
  have hk : (2 + cT + 3 * S) * (L - 1) = kLow cT L := by unfold kLow; rw [hS]
  rw [show (2 + cT + 3 * S) * (L - 1) = kLow cT L from hk] at sC
  set σ3 := (σ2.setv (R 9) 0).setv (R 2) (n0 - kLow cT L) with hσ3
  have sD := bkD_spec cap R B hRB σ3 b (n0 - kLow cT L)
    (by simp [σ3, σ2, σ1, Function.update_of_ne (hRB 2).symm, Function.update_of_ne (hRB 9).symm, hB]) (by simp [σ3])
    (by simp [σ3, σ2, Function.update_of_ne (hR (show (1 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (hR (show (1 : Fin 12) ≠ 9 by decide)), z1 1 (by decide)])
    (by simp [σ3, σ2, Function.update_of_ne (hR (show (3 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (hR (show (3 : Fin 12) ≠ 9 by decide)), z1 3 (by decide)])
    (by simp [σ3, σ2, Function.update_of_ne (hR (show (4 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (hR (show (4 : Fin 12) ≠ 9 by decide)), z1 4 (by decide)])
    hcap3 (by omega)
  refine (WXExec.seq sA (WXExec.seq sB (WXExec.seq sC sD))).cast cap ?_ (by simp only [bkBlkCost, ← hS]; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [σ3, σ2, σ1, WState.setv_val, Function.update_apply]
  by_cases rB : r = B
  · subst rB; simp [(hRB 2).symm, (hRB 9).symm]
  · by_cases r2 : r = R 2
    · subst r2; simp [hRB 2, hz]
    · by_cases r9 : r = R 9
      · subst r9; simp [hRB 9, hR (show (9 : Fin 12) ≠ 2 by decide), hz]
      · simp [rB, r2, r9]

end Block

end NearCubicGates.Close.CounterMachine.CellTablesProg
