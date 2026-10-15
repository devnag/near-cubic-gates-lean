import Proof.Gates.CounterMachine.CellTablesSet

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

section Block
variable {ns nr : ℕ} (cap : ℕ) (R : Fin 12 ↪ Fin nr) (I : Fin (ns + 1)) (G B : Fin nr)

def bkBCost (L cT : ℕ) : ℕ := 200 * L + 4 * cT + 100

/-- The second half of `bkB`: `R 9 := 2 + c_T + 3·R 8`, then `R 8 := 0`. -/
theorem bkB2_spec (cT : ℕ) (σ : WState ns nr) (S : ℕ) (h6 : σ.val (R 6) = 0) (h8 : σ.val (R 8) = S)
    (h9 : σ.val (R 9) = 0) (hcap : 3 * S + cT + 10 ≤ cap) :
    WXExec cap (.seq (Cells.incN (R 9) (2 + cT)) (.seq (addR (R 8) (R 9) (R 6)) (.seq (addR (R 8) (R 9) (R 6))
      (.seq (addR (R 8) (R 9) (R 6)) (Cells.clearR (R 8)))))) σ
      ((σ.setv (R 9) (2 + cT + 3 * S)).setv (R 8) 0) (4 * (2 + cT) + 3 * (18 * S + 3) + (3 * S + 1) + 4) := by
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have n89 := hR (show (8 : Fin 12) ≠ 9 by decide)
  have n69 := hR (show (6 : Fin 12) ≠ 9 by decide)
  have a5 := Cells.incN_spec cap (R 9) (2 + cT) σ (by rw [h9]; omega)
  rw [h9, zero_add] at a5
  have v6 : ∀ x, (σ.setv (R 9) x).val (R 6) = 0 := fun x => by simp [Function.update_of_ne n69, h6]
  have v8 : ∀ x, (σ.setv (R 9) x).val (R 8) = S := fun x => by simp [Function.update_of_ne n89, h8]
  have v9 : ∀ x, (σ.setv (R 9) x).val (R 9) = x := fun x => by simp
  have ss : ∀ x y, (σ.setv (R 9) x).setv (R 9) y = σ.setv (R 9) y := fun x y => by
    refine WState.eq rfl rfl ?_ rfl; funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl
  have step : ∀ x, x + S ≤ cap → WXExec cap (addR (R 8) (R 9) (R 6)) (σ.setv (R 9) x) (σ.setv (R 9) (x + S))
      (18 * S + 3) := fun x hx => by
    have := addR_spec cap (A := R 8) (B := R 9) (T := R 6) (hR (by decide)) (hR (by decide)) (hR (by decide))
      (σ.setv (R 9) x) (v6 x) (by rw [v8, v9]; exact hx)
    rwa [v8, v9, ss] at this
  have a9 := Cells.clearR_spec cap (R 8) S (σ.setv (R 9) (2 + cT + S + S + S)) (v8 _) (by omega)
  refine (WXExec.seq a5 (WXExec.seq (step _ (by omega)) (WXExec.seq (step _ (by omega))
    (WXExec.seq (step _ (by omega)) a9)))).cast cap (by congr 2; ring) (by omega)

theorem bkB_spec (hRG : ∀ j, R j ≠ G) (cT : ℕ) (σ : WState ns nr) (L : ℕ) (hG : σ.val G = L)
    (h6 : σ.val (R 6) = 0) (h7 : σ.val (R 7) = 0) (h8 : σ.val (R 8) = 0) (h9 : σ.val (R 9) = 0)
    (hcap : 4 * L + cT + 20 ≤ cap) :
    WXExec cap (bkB R G cT) σ (σ.setv (R 9) (2 + cT + 3 * Nat.size (L - 2))) (bkBCost L cT) := by
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  set S := Nat.size (L - 2) with hS
  have hSL : S ≤ L - 2 := Nat.size_le.mpr Nat.lt_two_pow_self
  have a1 := addR_spec cap (A := G) (B := R 7) (T := R 6) (hRG 7).symm (hRG 6).symm (hR (by decide)) σ h6
    (by rw [h7, hG]; omega)
  rw [h7, hG, zero_add] at a1
  have a2 := WXExec.dec cap (R 7) (σ.setv (R 7) L) (by simp; omega)
  have a3 := WXExec.dec cap (R 7) ((σ.setv (R 7) L).setv (R 7) ((σ.setv (R 7) L).val (R 7) - 1)) (by simp; omega)
  have e3 : (((σ.setv (R 7) L).setv (R 7) ((σ.setv (R 7) L).val (R 7) - 1)).setv (R 7)
      (((σ.setv (R 7) L).setv (R 7) ((σ.setv (R 7) L).val (R 7) - 1)).val (R 7) - 1)) = σ.setv (R 7) (L - 2) := by
    refine WState.eq rfl rfl ?_ rfl; funext r
    by_cases hr : r = R 7
    · subst hr; simp; omega
    · simp [Function.update_of_ne hr]
  rw [e3] at a3
  have n67 := hR (show (6 : Fin 12) ≠ 7 by decide)
  have n87 := hR (show (8 : Fin 12) ≠ 7 by decide)
  have n97 := hR (show (9 : Fin 12) ≠ 7 by decide)
  have n98 := hR (show (9 : Fin 12) ≠ 8 by decide)
  have n68 := hR (show (6 : Fin 12) ≠ 8 by decide)
  have a4 := sizeL_spec cap (R 7) (R 6) (R 8) (hR (by decide)) (hR (by decide)) (hR (by decide)) (L - 2)
    (σ.setv (R 7) (L - 2)) (by simp) (by simp [Function.update_of_ne n67, h6]) (by omega)
    (by simp [Function.update_of_ne n87, h8]; omega)
  have e4 : (σ.setv (R 7) (L - 2)).val (R 8) = 0 := by simp [Function.update_of_ne n87, h8]
  rw [e4, zero_add, ← hS] at a4
  set ρ := ((σ.setv (R 7) (L - 2)).setv (R 7) 0).setv (R 8) S with hρ
  have b := bkB2_spec cap R cT ρ S (by simp [ρ, Function.update_of_ne n68, Function.update_of_ne n67, h6])
    (by simp [ρ]) (by simp [ρ, Function.update_of_ne n98, Function.update_of_ne n97, h9]) (by omega)
  refine (WXExec.seq a1 (WXExec.seq a2 (WXExec.seq a3 (WXExec.seq a4 b)))).cast cap ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [ρ, WState.setv_val, Function.update_apply]
    by_cases r8 : r = R 8
    · subst r8; simp [n98.symm, h8]
    · by_cases r9 : r = R 9
      · subst r9; simp [n98]
      · by_cases r7 : r = R 7
        · subst r7; simp [n97.symm, n87, h7]
        · simp [r7, r8, r9]
  · simp only [bkBCost]; omega

end Block

end NearCubicGates.Close.CounterMachine.CellTablesProg
