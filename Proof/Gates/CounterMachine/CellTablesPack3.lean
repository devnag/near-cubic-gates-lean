import Proof.Gates.CounterMachine.CellTablesPack2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

variable {V M : ℕ} (K : Callee)

/-- The register numbers of the block's scratch. -/
def blockRegTbl : List ℕ := [0, 1, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]

theorem blockRegTbl_lt (j : Fin 12) : blockRegTbl.getD j.val 0 ≤ 15 := by fin_cases j <;> decide

theorem blockRegTbl_inj : ∀ a b : Fin 12, blockRegTbl.getD a.val 0 = blockRegTbl.getD b.val 0 → a = b := by decide

theorem blockRegTbl_ne : ∀ j : Fin 12, blockRegTbl.getD j.val 0 ≠ 2 ∧ blockRegTbl.getD j.val 0 ≠ 9 ∧ blockRegTbl.getD j.val 0 ≠ 3 ∧
    blockRegTbl.getD j.val 0 ≠ 4 := by decide

/-- The twelve free registers (`M ≥ 5`). -/
def blockRegs (hM : 5 ≤ M) : Fin 12 ↪ Fin (NR M) :=
  ⟨fun j => ⟨blockRegTbl.getD j.val 0, by have := blockRegTbl_lt j; unfold NR; omega⟩, fun a b h =>
    blockRegTbl_inj a b (congrArg Fin.val h)⟩

theorem blockRegs_val (hM : 5 ≤ M) (j : Fin 12) : (blockRegs hM j).val = blockRegTbl.getD j.val 0 := rfl

theorem blockRegs_ne_rG (hM : 5 ≤ M) (j : Fin 12) : blockRegs (M := M) hM j ≠ rG := fun e =>
  (blockRegTbl_ne j).1 ((blockRegs_val hM j).symm.trans (congrArg Fin.val e))
theorem blockRegs_ne_rC1 (hM : 5 ≤ M) (j : Fin 12) : blockRegs (M := M) hM j ≠ rC1 := fun e =>
  (blockRegTbl_ne j).2.1 ((blockRegs_val hM j).symm.trans (congrArg Fin.val e))
theorem blockRegs_ne_rK (hM : 5 ≤ M) (j : Fin 12) : blockRegs (M := M) hM j ≠ rK := fun e =>
  (blockRegTbl_ne j).2.2.1 ((blockRegs_val hM j).symm.trans (congrArg Fin.val e))
theorem blockRegs_ne_rT (hM : 5 ≤ M) (j : Fin 12) : blockRegs (M := M) hM j ≠ rT := fun e =>
  (blockRegTbl_ne j).2.2.2 ((blockRegs_val hM j).symm.trans (congrArg Fin.val e))

/-- The registers after `pw2 rC1 … c₃`. -/
def regs0 (L W Lk Bk : ℕ) (r : Fin (NR M)) : ℕ :=
  if r = rC1 then Bk else if r = rT then Lk else if r = rK then W else if r = rG then L else 0

/-- The state after `pw2 rC1 … c₃`. -/
def stA0 {t : ℕ} (L W Lk Bk : ℕ) (inp : List Bool) : WState (NS M t V) (NR M) :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame inp else [], regs0 L W Lk Bk, false⟩

/-- Phase A up to the block. -/
def setupA1 (z : Sz) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (countOnes sIN rG rC2)
  (.seq (incN rK z.a1) (.seq (pw2 rK rIP rOP rG rC2 z.c1)
  (.seq (incN rT z.a2) (.seq (pw2 rT rIP rOP rG rC2 z.c2)
  (.seq (incN rC1 z.a3) (pw2 rC1 rIP rOP rG rC2 z.c3))))))

def costA1 (z : Sz) (L : ℕ) : ℕ :=
  (30 * L + 20) + 4 * z.a1 + (L * (60 * z.W L + 11 * z.c1 + 8) + 7 * L + 3) +
  4 * z.a2 + (L * (60 * z.Lk L + 11 * z.c2 + 8) + 7 * L + 3) +
  4 * z.a3 + (L * (60 * z.Bk L + 11 * z.c3 + 8) + 7 * L + 3) + 6

theorem setupA1_spec (z : Sz) (inp : List Bool) (cap : ℕ)
    (hcap : 2 * inp.length + 4 * (z.W (leadOnes inp) + z.Lk (leadOnes inp) + z.Bk (leadOnes inp)) + 4 * z.a1 +
      4 * z.a2 + 4 * z.a3 + 20 ≤ cap) :
    WXExec cap (setupA1 (V := V) (M := M) K z) (Interfaces.startState (NS M (TSK K) V) (NR M) inp)
      (stA0 (t := TSK K) (leadOnes inp) (z.W (leadOnes inp)) (z.Lk (leadOnes inp)) (z.Bk (leadOnes inp)) inp)
      (costA1 z (leadOnes inp)) := by
  set L := leadOnes inp with hL
  set W := z.W L with hW
  set Lk := z.Lk L with hLk
  set Bk := z.Bk L with hBk
  have hLi : L ≤ inp.length := leadOnes_le inp
  have hWa : z.a1 ≤ W := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hLa : z.a2 ≤ Lk := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hBa : z.a3 ≤ Bk := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  set σs := Interfaces.startState (NS M (TSK K) V) (NR M) inp with hσs
  have v0 : ∀ r, σs.val r = 0 := fun _ => rfl
  have st0 : ∀ i, σs.st i = if i.val = 0 then frame inp else [] := fun _ => rfl
  have sh0 : ∀ i, σs.sh i = 0 := fun _ => rfl
  have s1 := countOnes_spec cap (sIN : Fin (NS M (TSK K) V + 1)) (G := rG) (G2 := rC2) (by lay_ne) σs inp
    (by rw [st0]; rfl) (sh0 _) (v0 _) (v0 _) (by omega)
  rw [← hL] at s1
  set σ1 := σs.setv rG L
  have s2 := incN_spec cap rK z.a1 σ1 (by simp [σ1, v0, Fin.ext_iff]; omega)
  have e2 : σ1.val rK = 0 := by simp [σ1, v0, Fin.ext_iff]
  rw [e2, zero_add] at s2
  set σ2 := σ1.setv rK z.a1
  have s3 := pw2_spec cap (X := rK) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c1 σ2 (by simp [σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ2, σ1, v0, Fin.ext_iff]) (by simp [σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ2, σ1, Fin.ext_iff]; simp [Sz.W] at hW; omega) (by simp [σ2, σ1, Fin.ext_iff]; omega)
  have e3a : σ2.val rG = L := by simp [σ2, σ1, Fin.ext_iff]
  have e3b : σ2.val rK = z.a1 := by simp [σ2]
  rw [e3a, e3b, show 2 ^ (z.c1 * L) * z.a1 = W from rfl] at s3
  set σ3 := σ2.setv rK W
  have s4 := incN_spec cap rT z.a2 σ3 (by simp [σ3, σ2, σ1, v0, Fin.ext_iff]; omega)
  have e4 : σ3.val rT = 0 := by simp [σ3, σ2, σ1, v0, Fin.ext_iff]
  rw [e4, zero_add] at s4
  set σ4 := σ3.setv rT z.a2
  have s5 := pw2_spec cap (X := rT) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c2 σ4 (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]; simp [Sz.Lk] at hLk; omega)
    (by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]; omega)
  have e5a : σ4.val rG = L := by simp [σ4, σ3, σ2, σ1, Fin.ext_iff]
  have e5b : σ4.val rT = z.a2 := by simp [σ4]
  rw [e5a, e5b, show 2 ^ (z.c2 * L) * z.a2 = Lk from rfl] at s5
  set σ5 := σ4.setv rT Lk
  have s6 := incN_spec cap rC1 z.a3 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]; omega)
  have e6 : σ5.val rC1 = 0 := by simp [σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff]
  rw [e6, zero_add] at s6
  set σ6 := σ5.setv rC1 z.a3
  have s7 := pw2_spec cap (X := rC1) (Y := rIP) (T := rOP) (G := rG) (G2 := rC2)
    (by simp [List.nodup_cons, Fin.ext_iff]) z.c3 σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, v0, Fin.ext_iff])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]; simp [Sz.Bk] at hBk; omega)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]; omega)
  have e7a : σ6.val rG = L := by simp [σ6, σ5, σ4, σ3, σ2, σ1, Fin.ext_iff]
  have e7b : σ6.val rC1 = z.a3 := by simp [σ6]
  rw [e7a, e7b, show 2 ^ (z.c3 * L) * z.a3 = Bk from rfl] at s7
  refine WXExec.mono (WXExec.seq s1 (WXExec.seq s2 (WXExec.seq s3 (WXExec.seq s4 (WXExec.seq s5 (WXExec.seq s6
    s7))))) |>.cast cap ?_ le_rfl) ?_
  · refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp [σ6, σ5, σ4, σ3, σ2, σ1, sh0, stA0]
    · funext i; simp [σ6, σ5, σ4, σ3, σ2, σ1, st0, stA0]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, Function.update_apply, v0, stA0, regs0]
      split_ifs <;> simp_all
  · simp only [costA1]; rw [← hW, ← hLk, ← hBk]; omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
