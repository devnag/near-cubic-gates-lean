import Proof.Wire_3_5.PrimAsmSymDecStreams

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum

/-- The value-named division: `a := a mod b`, `q := a / b` (from `q = 0`). -/
theorem div1 {ns nr : ℕ} (cap : ℕ) (R : Fin 9 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha : σ.val (R 0) = a)
    (hb : σ.val (R 1) = b) (hq : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0)
    (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0) (h7 : σ.val (R 7) = 0) (hb1 : 1 ≤ b) (hcap : a + b + 2 ≤ cap) :
    WExec cap (divW R) σ ((σ.setv (R 0) (a % b)).setv (R 2) (a / b)) (UnaryPow.sq cap) := by
  have h := divW_spec cap R σ (by rw [hb]; exact hb1) h3 h4 h5 h6 h7 (by rw [ha]; omega) (by rw [hb]; omega)
    (by rw [hq, ha]; omega) (by omega)
  rw [ha, hb, hq, Nat.zero_add] at h
  refine WExec.mono h ?_
  unfold UnaryPow.sq
  have e1 : a + 2 ≤ cap + 2 := by omega
  have e2 : 90 * a + 90 * b + 60 ≤ 200 * (cap + 2) := by omega
  have := Nat.mul_le_mul e1 e2
  nlinarith

/-! ## The block -/

def H : Fin 40 ↪ Fin LNR := ⟨fun i => ⟨472 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

theorem H_val (i : Fin 40) : (H i).val = 472 + i.val := rfl

theorem H_ne (i : Fin 40) (r : Fin LNR) (h : r.val < 472) : r ≠ H i := fun e => by
  have := congrArg Fin.val e; rw [H_val] at this; omega

theorem GH (i : Fin 64) (k : Fin 40) : G i ≠ H k := fun e => by
  have := congrArg Fin.val e; rw [G_val, H_val] at this; have := i.isLt; have := k.isLt
  -- 408 + i = 472 + k forces i ≥ 64
  omega

theorem ndNC_H (k : Fin 40) : dNC ≠ H k := H_ne k _ (by decide)

def gtT : Fin 6 ↪ Fin LNR := ⟨![G 56, H 0, H 2, H 36, H 37, H 38], by decide⟩
def dv1 : Fin 9 ↪ Fin LNR := ⟨![H 3, G 55, H 4, H 30, H 31, H 32, H 33, H 34, H 35], by decide⟩
def gtW : Fin 6 ↪ Fin LNR := ⟨![H 5, H 3, H 6, H 36, H 37, H 38], by decide⟩
def dv2 : Fin 9 ↪ Fin LNR := ⟨![H 7, H 8, H 9, H 30, H 31, H 32, H 33, H 34, H 35], by decide⟩
def gtV : Fin 6 ↪ Fin LNR := ⟨![H 10, H 7, H 11, H 36, H 37, H 38], by decide⟩
def dv3 : Fin 9 ↪ Fin LNR := ⟨![H 13, G 53, H 14, H 30, H 31, H 32, H 33, H 34, H 35], by decide⟩
def dv4 : Fin 9 ↪ Fin LNR := ⟨![H 15, G 52, H 16, H 30, H 31, H 32, H 33, H 34, H 35], by decide⟩
def dv5 : Fin 9 ↪ Fin LNR := ⟨![H 17, G 41, H 18, H 30, H 31, H 32, H 33, H 34, H 35], by decide⟩
def gtR : Fin 6 ↪ Fin LNR := ⟨![dNC, H 9, H 19, H 36, H 37, H 38], by decide⟩
@[simp] theorem gtT_apply (i : Fin 6) : gtT i = ![G 56, H 0, H 2, H 36, H 37, H 38] i := rfl
@[simp] theorem dv1_apply (i : Fin 9) : dv1 i = ![H 3, G 55, H 4, H 30, H 31, H 32, H 33, H 34, H 35] i := rfl
@[simp] theorem gtW_apply (i : Fin 6) : gtW i = ![H 5, H 3, H 6, H 36, H 37, H 38] i := rfl
@[simp] theorem dv2_apply (i : Fin 9) : dv2 i = ![H 7, H 8, H 9, H 30, H 31, H 32, H 33, H 34, H 35] i := rfl
@[simp] theorem gtV_apply (i : Fin 6) : gtV i = ![H 10, H 7, H 11, H 36, H 37, H 38] i := rfl
@[simp] theorem dv3_apply (i : Fin 9) : dv3 i = ![H 13, G 53, H 14, H 30, H 31, H 32, H 33, H 34, H 35] i := rfl
@[simp] theorem dv4_apply (i : Fin 9) : dv4 i = ![H 15, G 52, H 16, H 30, H 31, H 32, H 33, H 34, H 35] i := rfl
@[simp] theorem dv5_apply (i : Fin 9) : dv5 i = ![H 17, G 41, H 18, H 30, H 31, H 32, H 33, H 34, H 35] i := rfl
@[simp] theorem gtR_apply (i : Fin 6) : gtR i = ![dNC, H 9, H 19, H 36, H 37, H 38] i := rfl

variable (x : ℕ)

/-- Part A of the split: `j`, the rewind, `[j < TOT]`, `e`, `w`, `[w < EU−1]`, `v`, `r`. -/
def idxAW : WM (LNS x) LNR :=
  .seq (readUW (sk x 2) (H 0)) (.seq (FinalPass.Hash4.wcopyR (H 0) (H 1) (H 39)) (.seq (WM.rewind (sk x 2) (H 1))
  (.seq (gtFlagW gtT) (.seq (FinalPass.Hash4.wcopyR (H 0) (H 3) (H 39)) (.seq (divW dv1)
  (.seq (FinalPass.Hash4.wcopyR (G 55) (H 5) (H 39)) (.seq (.dec (H 5)) (.seq (gtFlagW gtW)
  (.seq (FinalPass.Hash4.wcopyR (H 3) (H 7) (H 39)) (.seq (.dec (H 7)) (.seq (FinalPass.Hash4.wcopyR (G 32) (H 8) (H 39))
  (.seq (StarNums.incN (H 8) 3) (divW dv2)))))))))))))

/-- Part B of the split: `[v < M+2]`, `s`, `row`, `t`, the joint state, the seeds, `[r < |carriers|]`. -/
def idxBW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (H 8) (H 10) (H 39)) (.seq (.dec (H 10)) (.seq (gtFlagW gtV)
  (.seq (FinalPass.Hash4.wcopyR (H 7) (H 12) (H 39)) (.seq (.dec (H 12)) (.seq (FinalPass.Hash4.wcopyR (H 4) (H 13) (H 39))
  (.seq (divW dv3) (.seq (FinalPass.Hash4.wcopyR (H 14) (H 15) (H 39)) (.seq (divW dv4)
  (.seq (FinalPass.Hash4.wcopyR (H 16) (H 17) (H 39)) (.seq (divW dv5) (gtFlagW gtR)))))))))))

/-- **The unit index split.** -/
def idxW : WM (LNS x) LNR := .seq (idxAW x) (idxBW x)

theorem HG (i : Fin 64) (k : Fin 40) : H k ≠ G i := fun e => GH i k e.symm

theorem idxA_spec (cap : ℕ) (σ : WState (LNS x) LNR) (j TOT EU M : ℕ) (hs2 : σ.st (sk x 2) = List.replicate j true)
    (hh2 : σ.sh (sk x 2) = 0) (g56 : σ.val (G 56) = TOT) (g55 : σ.val (G 55) = EU) (g32 : σ.val (G 32) = M)
    (hz : ∀ i, σ.val (H i) = 0) (hEU : 2 ≤ EU) (hcap : j + TOT + EU + M + 10 ≤ cap) :
    ∃ τ, WExec cap (idxAW x) σ τ (30 * UnaryPow.sq cap) ∧
      τ.val (H 0) = (0 + j) ∧
      τ.val (H 1) = (0) ∧
      τ.val (H 2) = (if 0 + j < TOT then 1 else 0) ∧
      τ.val (H 3) = (((0 + j) % EU)) ∧
      τ.val (H 4) = ((0 + j) / EU) ∧
      τ.val (H 5) = (EU - 1) ∧
      τ.val (H 6) = (if ((0 + j) % EU) < EU - 1 then 1 else 0) ∧
      τ.val (H 7) = (((((0 + j) % EU) - 1) % (M + 3))) ∧
      τ.val (H 8) = (M + 3) ∧
      τ.val (H 9) = (((((0 + j) % EU) - 1) / (M + 3))) ∧
      (∀ k : Fin 40, 10 ≤ k.val → τ.val (H k) = 0) ∧ (∀ r, (∀ k, H k ≠ r) → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      τ.sh (sk x 2) = 0 ∧ (∀ s, s ≠ sk x 2 → τ.sh s = σ.sh s) ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hrun : WExec cap (idxAW x) σ ((((((((((((((((((((((((((((((((((((σ).seth (sk x 2) (j))).setv (H 0) (0 + j))).setv (H 1) (0 + j))).setv (H 1) (0))).seth (sk x 2) (j - (0 + j)))).setv (H 2) (if 0 + j < TOT then 1 else 0))).setv (H 3) (0 + j))).setv (H 3) (((0 + j) % EU)))).setv (H 4) ((0 + j) / EU))).setv (H 5) (EU))).setv (H 5) (EU - 1))).setv (H 6) (if ((0 + j) % EU) < EU - 1 then 1 else 0))).setv (H 7) (((0 + j) % EU)))).setv (H 7) (((0 + j) % EU) - 1))).setv (H 8) (M))).setv (H 8) (M + 3))).setv (H 7) (((((0 + j) % EU) - 1) % (M + 3))))).setv (H 9) (((((0 + j) % EU) - 1) / (M + 3)))) (30 * UnaryPow.sq cap) := by
    unfold idxAW
    exact (seqD cap 30 1 (readU_spec cap (sk x 2) (H 0) j 0 σ hs2 hh2 (hz 0) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 0) (H 1) (H 39) (by decide) (by decide) (by decide) (0 + j) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (wrewind_spec cap (sk x 2) (H 1) (0 + j) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp; omega)) (by omega) (by omega)
      (seqD cap _ 1 (gt1 cap gtT TOT (0 + j) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtT_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 0) (H 3) (H 39) (by decide) (by decide) (by decide) (0 + j) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (div1 cap dv1 (0 + j) EU _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv1_apply]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 55) (H 5) (H 39) (by decide) (by decide) (by decide) EU _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dec1 cap (H 5) EU _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (gt1 cap gtW (EU - 1) ((0 + j) % EU) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, gtW_apply]) (by omega) (by have := Nat.mod_lt (0 + j) (show 0 < EU by omega); omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 3) (H 7) (H 39) (by decide) (by decide) (by decide) ((0 + j) % EU) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by have := Nat.mod_lt (0 + j) (show 0 < EU by omega); omega)) (by omega) (by omega)
      (seqD cap _ 1 (dec1 cap (H 7) ((0 + j) % EU) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by have := Nat.mod_lt (0 + j) (show 0 < EU by omega); omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (G 32) (H 8) (H 39) (by decide) (by decide) (by decide) M _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (incN1 cap (H 8) M 3 _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG]) (by omega)) (by omega) (by omega)
      (endD cap _ 1 (div1 cap dv2 (((0 + j) % EU) - 1) (M + 3) _ (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by simp [Function.update_apply, hz, g56, g55, g32, GH, HG, dv2_apply]) (by omega) (by have := Nat.mod_lt (0 + j) (show 0 < EU by omega); omega)) rfl (by omega) (by omega)))))))))))))))
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · simp [Function.update_apply, hz, g56, g55, g32, GH, HG]
  · intro k hk
    fin_cases k <;> simp [Function.update_apply, hz, g56, g55, g32, GH, HG] at hk ⊢
  · intro r hr
    have hr' : ∀ k, r ≠ H k := fun k h => hr k h.symm
    simp [Function.update_apply, hr']
  · simp
  · simp [hh2]
  · intro s hs
    simp [Function.update_apply, hs]
  · simp

theorem idxB_spec (cap : ℕ) (σ : WState (LNS x) LNR) (e v r M N2 nSt nFlat nc : ℕ)
    (h4 : σ.val (H 4) = e) (h7 : σ.val (H 7) = v) (h8 : σ.val (H 8) = M + 3) (h9 : σ.val (H 9) = r)
    (g53 : σ.val (G 53) = N2) (g52 : σ.val (G 52) = nSt) (g41 : σ.val (G 41) = nFlat) (vNC : σ.val dNC = nc)
    (hz : ∀ k : Fin 40, 10 ≤ k.val → σ.val (H k) = 0) (hN2 : 1 ≤ N2) (hSt : 1 ≤ nSt) (hFl : 1 ≤ nFlat)
    (hcap : e + v + r + M + N2 + nSt + nFlat + nc + 10 ≤ cap) :
    ∃ τ, WExec cap (idxBW x) σ τ (26 * UnaryPow.sq cap) ∧
      τ.val (H 10) = (M + 3 - 1) ∧
      τ.val (H 11) = (if v < M + 3 - 1 then 1 else 0) ∧
      τ.val (H 12) = (v - 1) ∧
      τ.val (H 13) = (e % N2) ∧
      τ.val (H 14) = (e / N2) ∧
      τ.val (H 15) = ((e / N2) % nSt) ∧
      τ.val (H 16) = ((e / N2) / nSt) ∧
      τ.val (H 17) = (((e / N2) / nSt) % nFlat) ∧
      τ.val (H 18) = (((e / N2) / nSt) / nFlat) ∧
      τ.val (H 19) = (if r < nc then 1 else 0) ∧
      (∀ k : Fin 40, k.val < 10 → τ.val (H k) = σ.val (H k)) ∧ (∀ k : Fin 40, 20 ≤ k.val → τ.val (H k) = 0) ∧
      (∀ r, (∀ k, H k ≠ r) → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hrun : WExec cap (idxBW x) σ ((((((((((((((((((((((((((((((σ).setv (H 10) (M + 3))).setv (H 10) (M + 3 - 1))).setv (H 11) (if v < M + 3 - 1 then 1 else 0))).setv (H 12) (v))).setv (H 12) (v - 1))).setv (H 13) (e))).setv (H 13) (e % N2))).setv (H 14) (e / N2))).setv (H 15) ((e / N2)))).setv (H 15) ((e / N2) % nSt))).setv (H 16) ((e / N2) / nSt))).setv (H 17) (((e / N2) / nSt)))).setv (H 17) (((e / N2) / nSt) % nFlat))).setv (H 18) (((e / N2) / nSt) / nFlat))).setv (H 19) (if r < nc then 1 else 0)) (26 * UnaryPow.sq cap) := by
    unfold idxBW
    exact (seqD cap 26 1 (copy1 cap (H 8) (H 10) (H 39) (by decide) (by decide) (by decide) (M + 3) _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dec1 cap (H 10) (M + 3) _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (gt1 cap gtV (M + 3 - 1) v _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtV_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 7) (H 12) (H 39) (by decide) (by decide) (by decide) v _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (dec1 cap (H 12) v _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 4) (H 13) (H 39) (by decide) (by decide) (by decide) e _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (div1 cap dv3 e N2 _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv3_apply]) (by omega) (by omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 14) (H 15) (H 39) (by decide) (by decide) (by decide) (e / N2) _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by have := Nat.div_le_self e N2; omega)) (by omega) (by omega)
      (seqD cap _ 1 (div1 cap dv4 (e / N2) nSt _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv4_apply]) (by omega) (by have := Nat.div_le_self e N2; omega)) (by omega) (by omega)
      (seqD cap _ 1 (copy1 cap (H 16) (H 17) (H 39) (by decide) (by decide) (by decide) ((e / N2) / nSt) _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]) (by have := Nat.div_le_self e N2; have := Nat.div_le_self (e / N2) nSt; omega)) (by omega) (by omega)
      (seqD cap _ 1 (div1 cap dv5 ((e / N2) / nSt) nFlat _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, dv5_apply]) (by omega) (by have := Nat.div_le_self e N2; have := Nat.div_le_self (e / N2) nSt; omega)) (by omega) (by omega)
      (endD cap _ 1 (gt1 cap gtR nc r _ (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H, gtR_apply]) (by omega) (by omega) (by omega)) rfl (by omega) (by omega)))))))))))))
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H]
  · intro k hk
    fin_cases k <;> simp [Function.update_apply] at hk ⊢
  · intro k hk
    fin_cases k <;> simp [Function.update_apply, hz, h7, h8, h4, h9, g53, g52, g41, vNC, GH, HG, ndNC_H] at hk ⊢
  · intro r hr
    have hr' : ∀ k, r ≠ H k := fun k h => hr k h.symm
    simp [Function.update_apply, hr']
  · simp
  · simp
  · simp

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
