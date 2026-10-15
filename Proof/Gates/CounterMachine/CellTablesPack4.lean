import Proof.Gates.CounterMachine.CellTablesPack3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

variable {V M : ℕ} (K : Callee)

theorem stA0_val {t : ℕ} (L W Lk Bk : ℕ) (inp : List Bool) :
    (stA0 (V := V) (M := M) (t := t) L W Lk Bk inp).val = regs0 L W Lk Bk := rfl
theorem stA0_sh {t : ℕ} (L W Lk Bk : ℕ) (inp : List Bool) :
    (stA0 (V := V) (M := M) (t := t) L W Lk Bk inp).sh = fun _ => 0 := rfl
theorem stA0_st {t : ℕ} (L W Lk Bk : ℕ) (inp : List Bool) :
    (stA0 (V := V) (M := M) (t := t) L W Lk Bk inp).st = fun i => if i.val = 0 then frame inp else [] := rfl
theorem stA0_cell {t : ℕ} (L W Lk Bk : ℕ) (inp : List Bool) :
    (stA0 (V := V) (M := M) (t := t) L W Lk Bk inp).cell = false := rfl

theorem blk_spec (hM : 5 ≤ M) (cT : ℕ) (n0 : ℕ) (rest inp : List Bool) (hinp : inp = natWord n0 ++ rest)
    (L W Lk Bk cap : ℕ) (hL : L = natBitLength n0)
    (hcap : 2 ^ (L + 2) + 8 * L + 10 ≤ cap)
    (hcap2 : (L + 1) * (2 + cT + 3 * L) + 4 * L + cT + 2 * n0 + 30 ≤ cap)
    (hcap3 : 2 ^ (n0 - kLow cT L) * Bk ≤ cap) :
    WXExec cap (bkBlk (blockRegs hM) sIN rG rC1 cT) (stA0 (V := V) (M := M) (t := TSK K) L W Lk Bk inp)
      (stA0 (V := V) (M := M) (t := TSK K) L W Lk (2 ^ (n0 - kLow cT L) * Bk) inp) (bkBlkCost L cT n0 Bk) := by
  subst hL
  have h := bkBlk_spec cap (blockRegs hM) (sIN : Fin (NS M (TSK K) V + 1)) rG rC1 (blockRegs_ne_rG hM) (blockRegs_ne_rC1 hM)
    (by lay_ne) cT (stA0 (V := V) (M := M) (t := TSK K) (natBitLength n0) W Lk Bk inp) n0 Bk rest
    (by rw [stA0_st]; show (if (0 : ℕ) = 0 then frame inp else []) = _; rw [if_pos rfl, hinp]) rfl
    (by rw [stA0_val]; simp [regs0, Fin.ext_iff])
    (by rw [stA0_val]; simp [regs0]) (fun j => by
      rw [stA0_val]; simp only [regs0]
      rw [if_neg (blockRegs_ne_rC1 hM j), if_neg (blockRegs_ne_rT hM j), if_neg (blockRegs_ne_rK hM j), if_neg (blockRegs_ne_rG hM j)])
    hcap hcap2 hcap3
  refine h.cast cap ?_ le_rfl
  refine WState.eq rfl rfl ?_ rfl
  funext r
  rw [WState.setv_val, stA0_val, stA0_val, Function.update_apply]
  by_cases h1 : r = rC1
  · simp [h1, regs0]
  · simp [h1, regs0]

def setupA3 : WMX (NS M (TSK K) V) (NR M) :=
  .seq (addR rT rR rOP) (.seq (addR rT rR rOP) (.seq (addR rC1 rR rOP) (incN rR 3)))

def costA3 (Lk Bk : ℕ) : ℕ := (18 * Lk + 3) + (18 * Lk + 3) + (18 * Bk + 3) + 12 + 3

theorem setupA3_spec (L W Lk Bk : ℕ) (inp : List Bool) (cap : ℕ) (hcap : 2 * Lk + Bk + 3 ≤ cap) :
    WXExec cap (setupA3 (V := V) (M := M) K) (stA0 (t := TSK K) L W Lk Bk inp) (stA (t := TSK K) L W Lk Bk inp)
      (costA3 Lk Bk) := by
  set σ7 := stA0 (V := V) (M := M) (t := TSK K) L W Lk Bk inp
  have s8 := addR_spec cap (ns := NS M (TSK K) V) (A := rT) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne) σ7
    (by simp [σ7, stA0_val, regs0, Fin.ext_iff]) (by simp [σ7, stA0_val, regs0, Fin.ext_iff]; omega)
  have e8a : σ7.val rR = 0 := by simp [σ7, stA0_val, regs0, Fin.ext_iff]
  have e8b : σ7.val rT = Lk := by simp [σ7, stA0_val, regs0, Fin.ext_iff]
  rw [e8a, e8b, zero_add] at s8
  set σ8 := σ7.setv rR Lk
  have s9 := addR_spec cap (ns := NS M (TSK K) V) (A := rT) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne) σ8
    (by simp [σ8, σ7, stA0_val, regs0, Fin.ext_iff]) (by simp [σ8, σ7, stA0_val, regs0, Fin.ext_iff]; omega)
  have e9a : σ8.val rR = Lk := by simp [σ8]
  have e9b : σ8.val rT = Lk := by simp [σ8, σ7, stA0_val, regs0, Fin.ext_iff]
  rw [e9a, e9b] at s9
  set σ9 := σ8.setv rR (Lk + Lk)
  have s10 := addR_spec cap (ns := NS M (TSK K) V) (A := rC1) (B := rR) (T := rOP) (by lay_ne) (by lay_ne) (by lay_ne)
    σ9 (by simp [σ9, σ8, σ7, stA0_val, regs0, Fin.ext_iff]) (by simp [σ9, σ8, σ7, stA0_val, regs0, Fin.ext_iff]; omega)
  have e10a : σ9.val rR = Lk + Lk := by simp [σ9]
  have e10b : σ9.val rC1 = Bk := by simp [σ9, σ8, σ7, stA0_val, regs0, Fin.ext_iff]
  rw [e10a, e10b] at s10
  set σ10 := σ9.setv rR (Lk + Lk + Bk)
  have s11 := incN_spec cap rR 3 σ10 (by simp [σ10]; omega)
  have e11 : σ10.val rR = Lk + Lk + Bk := by simp [σ10]
  rw [e11] at s11
  refine WXExec.mono (WXExec.seq s8 (WXExec.seq s9 (WXExec.seq s10 s11)) |>.cast cap ?_ le_rfl) (by
    simp only [costA3]; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [σ10, σ9, σ8, σ7, WState.setv_val, Function.update_apply]
  rw [stA0_val]
  show _ = regsOf L W Lk Bk r
  simp only [regs0, regsOf]
  split_ifs <;> simp_all

end NearCubicGates.Close.CounterMachine.CellTablesProg
