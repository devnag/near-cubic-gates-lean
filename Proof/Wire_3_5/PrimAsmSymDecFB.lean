import Proof.Wire_3_5.PrimAsmSymDecBr
import Proof.Wire_3_5.PrimAsmSymDecFilt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt

theorem rv_fsLen : fsLen.val = 400 := rfl
theorem rv_fsCap : fsCap.val = 401 := rfl
theorem rv_fsErr : fsErr.val = 402 := rfl
theorem rv_fsSeed : fsSeed.val = 403 := rfl
theorem rv_fsR4 : fsR4.val = 404 := rfl
theorem rv_fsG : fsG.val = 405 := rfl
theorem rv_fsOff : fsOff.val = 406 := rfl
theorem rv_fsL : fsL.val = 407 := rfl
theorem rv_TM : TM.val = 374 := rfl
theorem rv_XA : XA.val = 370 := rfl
theorem rv_XB : XB.val = 371 := rfl
theorem rv_dMS : dMS.val = 334 := rfl

/-- The registers `408 … 511`: the blocks `G` and `H`. -/
def ghList : List (Fin LNR) := (List.finRange 64).map G ++ (List.finRange 40).map H

theorem gh_length : ghList.length = 104 := by simp [ghList]

theorem mem_gh (q : Fin LNR) (h : 408 ≤ q.val) : q ∈ ghList := by
  have hq : q.val < 512 := q.isLt
  unfold ghList
  rw [List.mem_append]
  by_cases h2 : q.val < 472
  · left; rw [List.mem_map]
    exact ⟨⟨q.val - 408, by omega⟩, List.mem_finRange _, Fin.ext (by rw [G_val]; simp only; omega)⟩
  · right; rw [List.mem_map]
    exact ⟨⟨q.val - 472, by omega⟩, List.mem_finRange _, Fin.ext (by rw [H_val]; simp only; omega)⟩

theorem not_mem_gh (q : Fin LNR) (h : q.val < 408) : q ∉ ghList := by
  unfold ghList
  rw [List.mem_append, List.mem_map, List.mem_map]
  rintro (⟨i, -, hi⟩ | ⟨k, -, hk⟩)
  · have := congrArg Fin.val hi; rw [G_val] at this; omega
  · have := congrArg Fin.val hk; rw [H_val] at this; omega

section FB
variable (cap : ℕ) (x : ℕ)

/-- The FILTER bank's parameters: length, cap, error exponent, seed index, `r4 = 4·row`, the pool size. -/
def fbAW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (G 1) fsLen TM) (.seq (FinalPass.Hash4.wcopyR (G 0) fsCap TM)
  (.seq (FinalPass.Hash4.wcopyR (G 2) fsErr TM) (.seq (FinalPass.Hash4.wcopyR (H 18) fsSeed TM)
  (.seq (FinalPass.Hash4.wcopyR (H 13) fsR4 TM) (.seq (dbl fsR4 TM) (.seq (dbl fsR4 TM)
  (.seq (FinalPass.Hash4.wcopyR XA fsG TM) (.seq (addTo XB fsG TM) (.seq (dbl fsG TM) (addTo dMS fsG TM))))))))))

/-- The slice of carrier `1`: offset `2|X_0|`, length `2|X_1|`. -/
def fbB1W : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR XA fsOff TM) (.seq (dbl fsOff TM) (.seq (FinalPass.Hash4.wcopyR XB fsL TM) (dbl fsL TM)))

/-- The slice of carrier `0`: offset `0`, length `2|X_0|`. -/
def fbB0W : WM (LNS x) LNR := .seq (FinalPass.Hash4.wcopyR XA fsL TM) (dbl fsL TM)

/-- The exit state of `fbAW`. -/
def fbAOut (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((((((((σ).setv (fsLen) (len))).setv (fsCap) (capS))).setv (fsErr) (err))).setv (fsSeed) (g))).setv (fsR4) (row))).setv (fsR4) (2 * (row)))).setv (fsR4) (2 * (2 * (row))))).setv (fsG) (xa))).setv (fsG) (xa + xb))).setv (fsG) (2 * (xa + xb)))).setv (fsG) (2 * (xa + xb) + M))

theorem fbA_run (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) (g0 : σ.val (G 0) = capS)
    (g1 : σ.val (G 1) = len) (g2 : σ.val (G 2) = err) (h18 : σ.val (H 18) = g) (h13 : σ.val (H 13) = row)
    (vA : σ.val XA = xa) (vB : σ.val XB = xb) (vM : σ.val dMS = M) (zTM : σ.val TM = 0)
    (zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0) (hB : ∀ q, σ.val q ≤ cap)
    (c4 : 4 * row ≤ cap) (cG : 2 * (xa + xb) + M ≤ cap) :
    WExec cap (fbAW x) σ (fbAOut x σ len capS err g row xa xb M) (24 * UnaryPow.sq cap) := by
  have zfs' : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0 := zfs
  have z0 := zfs' fsLen (by decide) (by decide); have z1 := zfs' fsCap (by decide) (by decide)
  have z2 := zfs' fsErr (by decide) (by decide); have z3 := zfs' fsSeed (by decide) (by decide)
  have z4 := zfs' fsR4 (by decide) (by decide); have z5 := zfs' fsG (by decide) (by decide)
  clear zfs'
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  unfold fbAW fbAOut
  exact (seqD cap 24 1 (copy1 cap (G 1) fsLen TM (by decide) (by decide) (by decide) (len) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← g1]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 0) fsCap TM (by decide) (by decide) (by decide) (capS) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← g0]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 2) fsErr TM (by decide) (by decide) (by decide) (err) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← g2]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 18) fsSeed TM (by decide) (by decide) (by decide) (g) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← h18]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 13) fsR4 TM (by decide) (by decide) (by decide) (row) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← h13]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap fsR4 TM (by decide) (row) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap fsR4 TM (by decide) (2 * (row)) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (XA) fsG TM (by decide) (by decide) (by decide) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← vA]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (add1 cap XB fsG TM (by decide) (by decide) (by decide) (xb) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← vB]; exact hB _) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap fsG TM (by decide) (xa + xb) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (add1 cap dMS fsG TM (by decide) (by decide) (by decide) (M) (2 * (xa + xb)) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, g0, g1, g2, h18, h13, vA, vB, vM, zTM, z0, z1, z2, z3, z4, z5]) (by rw [← vM]; exact hB _) (by omega)) rfl (by omega) (by omega))))))))))))

/-- The exit state of `fbB1W`. -/
def fbB1Out (σ : WState (LNS x) LNR) (xa xb : ℕ) : WState (LNS x) LNR :=
  ((((((((σ).setv (fsOff) (xa))).setv (fsOff) (2 * (xa)))).setv (fsL) (xb))).setv (fsL) (2 * (xb)))

theorem fbB1_run (σ : WState (LNS x) LNR) (xa xb : ℕ) (vA : σ.val XA = xa) (vB : σ.val XB = xb)
    (zTM : σ.val TM = 0) (zOff : σ.val fsOff = 0) (zL : σ.val fsL = 0) (hB : ∀ q, σ.val q ≤ cap)
    (cA : 2 * xa ≤ cap) (cB : 2 * xb ≤ cap) :
    WExec cap (fbB1W x) σ (fbB1Out x σ xa xb) (10 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  unfold fbB1W fbB1Out
  exact (seqD cap 10 1 (copy1 cap (XA) fsOff TM (by decide) (by decide) (by decide) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by rw [← vA]; exact hB _)) (by omega) (by omega)
      (seqD cap _ 1 (dbl1 cap fsOff TM (by decide) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (XB) fsL TM (by decide) (by decide) (by decide) (xb) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by rw [← vB]; exact hB _)) (by omega) (by omega)
      (endD cap _ 1 (dbl1 cap fsL TM (by decide) (xb) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by omega)) rfl (by omega) (by omega)))))

/-- The exit state of `fbB0W`. -/
def fbB0Out (σ : WState (LNS x) LNR) (xa xb : ℕ) : WState (LNS x) LNR :=
  ((((σ).setv (fsL) (xa))).setv (fsL) (2 * (xa)))

theorem fbB0_run (σ : WState (LNS x) LNR) (xa xb : ℕ) (vA : σ.val XA = xa) (vB : σ.val XB = xb)
    (zTM : σ.val TM = 0) (zOff : σ.val fsOff = 0) (zL : σ.val fsL = 0) (hB : ∀ q, σ.val q ≤ cap)
    (cA : 2 * xa ≤ cap) :
    WExec cap (fbB0W x) σ (fbB0Out x σ xa xb) (6 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  unfold fbB0W fbB0Out
  exact (seqD cap 6 1 (copy1 cap (XA) fsL TM (by decide) (by decide) (by decide) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by rw [← vA]; exact hB _)) (by omega) (by omega)
      (endD cap _ 1 (dbl1 cap fsL TM (by decide) (xa) _ (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, rv_fsOff, rv_fsL, rv_TM, rv_XA, rv_XB, rv_dMS, G_val, H_val, vA, vB, zTM, zOff, zL]) (by omega)) rfl (by omega) (by omega)))

theorem fbAOut_st (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) :
    (fbAOut x σ len capS err g row xa xb M).st = σ.st := by unfold fbAOut; simp
theorem fbAOut_sh (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) :
    (fbAOut x σ len capS err g row xa xb M).sh = σ.sh := by unfold fbAOut; simp
theorem fbAOut_cell (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) :
    (fbAOut x σ len capS err g row xa xb M).cell = σ.cell := by unfold fbAOut; simp

/-- The parameters' registers after `fbAW`. -/
theorem fbAOut_val (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) :
    (fbAOut x σ len capS err g row xa xb M).val fsLen = len ∧ (fbAOut x σ len capS err g row xa xb M).val fsCap = capS ∧
    (fbAOut x σ len capS err g row xa xb M).val fsErr = err ∧ (fbAOut x σ len capS err g row xa xb M).val fsSeed = g ∧
    (fbAOut x σ len capS err g row xa xb M).val fsR4 = 2 * (2 * row) ∧
    (fbAOut x σ len capS err g row xa xb M).val fsG = 2 * (xa + xb) + M := by
  unfold fbAOut
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed,
    rv_fsR4, rv_fsG]

theorem fbAOut_other (σ : WState (LNS x) LNR) (len capS err g row xa xb M : ℕ) (q : Fin LNR)
    (h : q.val < 400 ∨ 406 ≤ q.val) : (fbAOut x σ len capS err g row xa xb M).val q = σ.val q := by
  have n0 : q.val ≠ 400 := by omega
  have n1 : q.val ≠ 401 := by omega
  have n2 : q.val ≠ 402 := by omega
  have n3 : q.val ≠ 403 := by omega
  have n4 : q.val ≠ 404 := by omega
  have n5 : q.val ≠ 405 := by omega
  unfold fbAOut
  simp [Function.update_apply, Fin.ext_iff, rv_fsLen, rv_fsCap, rv_fsErr, rv_fsSeed, rv_fsR4, rv_fsG, n0, n1, n2, n3,
    n4, n5]

/-- The slice's offset: `0` for carrier `0`, `2|X_0|` for carrier `1`. -/
def fbOff (r xa : ℕ) : ℕ := if r = 0 then 0 else 2 * xa

/-- The slice's length `2|X_r|`. -/
def fbL (r xa xb : ℕ) : ℕ := if r = 0 then 2 * xa else 2 * xb

/-- The slice's registers, run: `(fsOff, fsL)` set, everything else kept. -/
theorem fbB_run (σ : WState (LNS x) LNR) (r xa xb : ℕ) (hr : r ≤ 1) (h9 : σ.val (H 9) = r) (vA : σ.val XA = xa)
    (vB : σ.val XB = xb) (zTM : σ.val TM = 0) (zOff : σ.val fsOff = 0) (zL : σ.val fsL = 0) (hB : ∀ q, σ.val q ≤ cap)
    (cA : 2 * xa ≤ cap) (cB : 2 * xb ≤ cap) :
    ∃ τ, WExec cap (.ifr (H 9) (fbB1W x) (fbB0W x)) σ τ (10 * UnaryPow.sq cap + 1) ∧ τ.val fsOff = fbOff r xa ∧
      τ.val fsL = fbL r xa xb ∧ (∀ q : Fin LNR, q.val < 406 → τ.val q = σ.val q) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with h0 | h1
  · subst h0
    refine ⟨fbB0Out x σ xa xb, WExec.ifrF h9 (WExec.mono (fbB0_run cap x σ xa xb vA vB zTM zOff zL hB cA)
      (by omega)), ?_, ?_, fun q hq => ?_, by unfold fbB0Out; simp, by unfold fbB0Out; simp, by unfold fbB0Out; simp⟩
    · unfold fbB0Out fbOff; simp [Function.update_apply, Fin.ext_iff, rv_fsL, rv_fsOff, zOff]
    · unfold fbB0Out fbL; simp [Function.update_apply, Fin.ext_iff, rv_fsL]
    · have n : q.val ≠ 407 := by omega
      unfold fbB0Out; simp [Function.update_apply, Fin.ext_iff, rv_fsL, n]
  · subst h1
    refine ⟨fbB1Out x σ xa xb, WExec.ifrT (by rw [h9]; omega) (fbB1_run cap x σ xa xb vA vB zTM zOff zL hB cA cB),
      ?_, ?_, fun q hq => ?_, by unfold fbB1Out; simp, by unfold fbB1Out; simp, by unfold fbB1Out; simp⟩
    · unfold fbB1Out fbOff; simp [Function.update_apply, Fin.ext_iff, rv_fsL, rv_fsOff]
    · unfold fbB1Out fbL; simp [Function.update_apply, Fin.ext_iff, rv_fsL, rv_fsOff]
    · have n : q.val ≠ 407 := by omega
      have n' : q.val ≠ 406 := by omega
      unfold fbB1Out; simp [Function.update_apply, Fin.ext_iff, rv_fsL, rv_fsOff, n, n']

end FB

section Dock
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The FILTER bank**: the parameters, the slice, the clearing of `G`, `H`, the FILTER setup. -/
def fbW (F : FiltSetupSpec5 W) : WM (LNS W.x) LNR :=
  .seq (fbAW W.x) (.seq (.ifr (H 9) (fbB1W W.x) (fbB0W W.x)) (.seq (clrsW ghList) F.prog))

/-- The bank's cost before the FILTER setup. -/
def fbCost (c : ℕ) : ℕ := 24 * UnaryPow.sq c + 1 + (10 * UnaryPow.sq c + 1 + 1 + (104 * (3 * c + 2) + 1))

/-- **The FILTER bank, run**: from the decoded state (the unit's streams as at the entry, the registers below `250`
and `400 … 407` zero, the parameters in `G 0 … G 2`, the seed's index in `H 18`, the cell row in `H 13`, the carrier
`r ≤ 1` in `H 9`, the counts in `XA`, `XB`, `dMS`), `DecOK`'s FILTER disjunct with the slice's body at the seed `e`. -/
theorem fb_spec (F : FiltSetupSpec5 W) (σ : WState (LNS W.x) LNR) (w out u : List Bool) (j : ℕ) (P : GapParams)
    (e : GapSeed P) (row xa xb M r : ℕ) (hr : r ≤ 1)
    (hst : σ.st = (CellLoopD.blankCellD W.x w out j u).st)
    (hsh : ∀ s, s ≠ sk W.x 113 → σ.sh s = (CellLoopD.blankCellD W.x w out j u).sh s) (hcl : σ.cell = false)
    (hzl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0) (zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0)
    (zTM : σ.val TM = 0) (hB : ∀ q, σ.val q ≤ cap)
    (g0 : σ.val (G 0) = P.cap) (g1 : σ.val (G 1) = P.len) (g2 : σ.val (G 2) = P.errExp)
    (h18 : σ.val (H 18) = (Enum.gapSeedEquiv P e : ℕ)) (h13 : σ.val (H 13) = row) (h9 : σ.val (H 9) = r)
    (vA : σ.val XA = xa) (vB : σ.val XB = xb) (vM : σ.val dMS = M)
    (c4 : 4 * row ≤ cap) (cG : 2 * (xa + xb) + M ≤ cap) (cA : 2 * xa ≤ cap) (cB : 2 * xb ≤ cap) (hU : 1 ≤ P.cap)
    (hneed : F.need P.len P.cap P.errExp (fbL r xa xb) (2 * (2 * row)) (2 * (xa + xb) + M) (fbOff r xa)
      (Fintype.card (GapSeed P)) ≤ cap) :
    ∃ τ m, WExec cap (fbW W F) σ τ m ∧ m ≤ fbCost cap + F.bound cap ∧
      DecOK cap W τ out ((filtRefC (filterTable P e (fbL r xa xb)) (SupplierWalk.majorityThreshold P.walkLen)
        (fbL r xa xb) true (sliceLabs (2 * (2 * row)) (2 * (xa + xb) + M) (fbOff r xa) (fbL r xa xb))).flatMap
          (fun t => true :: ListMachine.Rec.termWord t))
        (filtPipeBound P e (fbL r xa xb) (2 * (2 * row)) (2 * (xa + xb) + M) (fbOff r xa) (rulerW P) (rulerW P)) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 := by
  have eA := fbA_run cap W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row xa xb M g0 g1 g2 h18 h13 vA vB vM zTM
    zfs hB c4 cG
  set σA := fbAOut W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row xa xb M with hσA
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := fbAOut_val W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row xa xb M
  have kA : ∀ q : Fin LNR, (q.val < 400 ∨ 406 ≤ q.val) → σA.val q = σ.val q :=
    fun q h => fbAOut_other W.x σ P.len P.cap P.errExp (Enum.gapSeedEquiv P e) row xa xb M q h
  have hBA : ∀ q, σA.val q ≤ cap := wexec_le cap eA hB
  obtain ⟨σB, eB, bOff, bL, kB, sB, shB, clB⟩ := fbB_run cap W.x σA r xa xb hr
    (by rw [kA _ (by rw [H_val]; right; decide)]; exact h9) (by rw [kA _ (by decide)]; exact vA)
    (by rw [kA _ (by decide)]; exact vB) (by rw [kA _ (by decide)]; exact zTM)
    (by rw [kA _ (by decide)]; exact zfs _ (by decide) (by decide))
    (by rw [kA _ (by decide)]; exact zfs _ (by decide) (by decide)) hBA cA cB
  have hBB := wexec_le cap eB hBA
  have eC := clrs_spec cap ghList σB hBB
  set σC := zeroOut σB ghList with hσC
  have vC : ∀ q : Fin LNR, q.val < 408 → σC.val q = σB.val q := fun q h => by
    rw [hσC, zeroOut_val, if_neg (not_mem_gh q h)]
  have stC : σC.st = (CellLoopD.blankCellD W.x w out j u).st := by
    rw [hσC, zeroOut_st, sB, hσA, fbAOut_st, hst]
  have shC : ∀ s, s ≠ sk W.x 113 → σC.sh s = (CellLoopD.blankCellD W.x w out j u).sh s := fun s hs => by
    rw [hσC, zeroOut_sh, shB, hσA, fbAOut_sh, hsh s hs]
  have n0B : sk W.x 0 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n1B : sk W.x 1 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n2B : sk W.x 2 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
  have n01 : sk W.x 0 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n21 : sk W.x 2 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
  have n20 : sk W.x 2 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
  have hFs : FsIn2 W.x σC w out j u P.len P.cap P.errExp (Enum.gapSeedEquiv P e) (2 * (2 * row)) (2 * (xa + xb) + M)
      (fbOff r xa) (fbL r xa xb) :=
    { s0 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n0B]
      s1 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
      h1 := by rw [shC _ n1B]; simp [CellLoopD.blankCellD, blankCell]
      s2 := by rw [stC]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
      h2 := by rw [shC _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
      s113 := by rw [stC]; simp [CellLoopD.blankCellD]
      blank := fun k k0 k1 k2 k3 => by
        have m0 : sk W.x k ≠ sk W.x 0 := fun e => k0 (by rw [sk_inj W.x e]; rfl)
        have m1 : sk W.x k ≠ sk W.x 1 := fun e => k1 (by rw [sk_inj W.x e]; rfl)
        have m2 : sk W.x k ≠ sk W.x 2 := fun e => k2 (by rw [sk_inj W.x e]; rfl)
        have m3 : sk W.x k ≠ sk W.x 113 := fun e => k3 (by rw [sk_inj W.x e]; rfl)
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      blankT := fun k => by
        have m0 : sT W.x k ≠ sk W.x 0 := (sk_ne_sT W.x 0 k).symm
        have m1 : sT W.x k ≠ sk W.x 1 := (sk_ne_sT W.x 1 k).symm
        have m2 : sT W.x k ≠ sk W.x 2 := (sk_ne_sT W.x 2 k).symm
        have m3 : sT W.x k ≠ sk W.x 113 := (sk_ne_sT W.x 113 k).symm
        refine ⟨?_, ?_⟩
        · rw [stC]; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
        · rw [shC _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
      cell := by rw [hσC, zeroOut_cell, clB, hσA, fbAOut_cell, hcl]
      vLen := by rw [vC _ (by decide), kB _ (by decide)]; exact a0
      vCap := by rw [vC _ (by decide), kB _ (by decide)]; exact a1
      vErr := by rw [vC _ (by decide), kB _ (by decide)]; exact a2
      vSeed := by rw [vC _ (by decide), kB _ (by decide)]; exact a3
      vR4 := by rw [vC _ (by decide), kB _ (by decide)]; exact a4
      vG := by rw [vC _ (by decide), kB _ (by decide)]; exact a5
      vOff := by rw [vC _ (by decide)]; exact bOff
      vL := by rw [vC _ (by decide)]; exact bL
      zLow := fun q hq => by
        rw [vC _ (by omega), kB _ (by omega), kA _ (by omega)]; exact hzl q hq
      zHigh := fun q hq => by rw [hσC, zeroOut_val, if_pos (mem_gh q hq)]
      h0 := by rw [shC _ n0B]; simp [CellLoopD.blankCellD, blankCell, n01] }
  obtain ⟨τ, m, eF, hm, hdec, k0, k2, k2h⟩ := SymDecFilt.filt_dock W F cap P e (fbL r xa xb) (2 * (2 * row))
    (2 * (xa + xb) + M) (fbOff r xa) w out u j σC hU (sliceLabs_length _ _ _ _) hneed hFs
  refine ⟨τ, _, WExec.seq eA (WExec.seq eB (WExec.seq eC eF)), ?_, hdec, k0, k2, k2h⟩
  unfold fbCost; rw [gh_length]; omega

end Dock

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
