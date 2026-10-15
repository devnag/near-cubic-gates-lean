import Proof.Wire_3_5.PrimAsmSymDecStar
import Proof.Wire_3_5.PrimAsmFlatNums

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

/-! ## The block and its parts -/

def G : Fin 64 ↪ Fin LNR := ⟨fun i => ⟨408 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

theorem G_val (i : Fin 64) : (G i).val = 408 + i.val := rfl

def KG : Fin 32 ↪ Fin 64 := ⟨![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
  25, 26, 27, 28, 29, 30, 31], by decide⟩
def KF : Fin 20 ↪ Fin 64 := ⟨![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51],
  by decide⟩
def pw26 : Fin 5 ↪ Fin 64 := ⟨![57, 1, 58, 59, 60], by decide⟩
def mB1 : Fin 5 ↪ Fin 64 := ⟨![33, 58, 59, 60, 61], by decide⟩
def pN : Fin 4 ↪ Fin 64 := ⟨![57, 53, 58, 59], by decide⟩
def mE : Fin 5 ↪ Fin 64 := ⟨![55, 54, 58, 59, 60], by decide⟩
def mT1 : Fin 5 ↪ Fin 64 := ⟨![56, 41, 58, 59, 60], by decide⟩
def mT2 : Fin 5 ↪ Fin 64 := ⟨![56, 52, 58, 59, 60], by decide⟩
def mT3 : Fin 5 ↪ Fin 64 := ⟨![56, 53, 58, 59, 60], by decide⟩
def mT4 : Fin 5 ↪ Fin 64 := ⟨![56, 55, 58, 59, 60], by decide⟩
def sq0 : Fin 10 ↪ Fin LNR := ⟨![dM0, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51], by decide⟩
def sq1 : Fin 10 ↪ Fin LNR := ⟨![dM1, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51], by decide⟩
def sq2 : Fin 10 ↪ Fin LNR := ⟨![dM2, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51], by decide⟩
def sq3 : Fin 10 ↪ Fin LNR := ⟨![dM3, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51], by decide⟩

@[simp] theorem KG_apply (i : Fin 32) : KG i = ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] i := rfl
@[simp] theorem KF_apply (i : Fin 20) : KF i = ![32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51] i := rfl
@[simp] theorem pw26_apply (i : Fin 5) : pw26 i = ![57, 1, 58, 59, 60] i := rfl
@[simp] theorem mB1_apply (i : Fin 5) : mB1 i = ![33, 58, 59, 60, 61] i := rfl
@[simp] theorem pN_apply (i : Fin 4) : pN i = ![57, 53, 58, 59] i := rfl
@[simp] theorem mE_apply (i : Fin 5) : mE i = ![55, 54, 58, 59, 60] i := rfl
@[simp] theorem mT1_apply (i : Fin 5) : mT1 i = ![56, 41, 58, 59, 60] i := rfl
@[simp] theorem mT2_apply (i : Fin 5) : mT2 i = ![56, 52, 58, 59, 60] i := rfl
@[simp] theorem mT3_apply (i : Fin 5) : mT3 i = ![56, 53, 58, 59, 60] i := rfl
@[simp] theorem mT4_apply (i : Fin 5) : mT4 i = ![56, 55, 58, 59, 60] i := rfl
@[simp] theorem sq0_apply (i : Fin 10) : sq0 i = ![dM0, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51] i := rfl
@[simp] theorem sq1_apply (i : Fin 10) : sq1 i = ![dM1, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51] i := rfl
@[simp] theorem sq2_apply (i : Fin 10) : sq2 i = ![dM2, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51] i := rfl
@[simp] theorem sq3_apply (i : Fin 10) : sq3 i = ![dM3, G 52, G 57, G 58, G 59, G 60, G 61, G 62, G 63, G 51] i := rfl

/-! ## The program -/

variable (x : ℕ)

/-- Part A: the SYM filter's parameters and numbers. -/
def nAW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 13) (G 0) (G 63)) (.seq (FinalPass.Hash4.wcopyR dN (G 57) (G 63)) (.seq (.inc (G
  57)) (.seq (UnaryPow.powConstW (pw26.trans G) 26) (.seq (dbl (G 1) (G 58)) (.seq (WM.clear (G 57)) (.seq
  (FinalPass.Hash4.wcopyR (SGb 10) (G 2) (G 63)) (GapNums.gapNumsW (KG.trans G))))))))

/-- Part B: the list's parameters and numbers. -/
def nBW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR dMS (G 32) (G 63)) (.seq (FinalPass.Hash4.wcopyR dNC (G 33) (G 63)) (.seq
  (StarNums.incN (G 58) 4096) (.seq (mulByW (mB1.trans G)) (.seq (WM.clear (G 58)) (.seq (FinalPass.Hash4.wcopyR (G
  0) (G 58) (G 63)) (.seq (mulByW (mB1.trans G)) (.seq (WM.clear (G 58)) (.seq (FinalPass.Hash4.wcopyR (SGb 1) (G
  34) (G 63)) (.seq (StarNums.incN (G 34) 5) (FlatNums.flatNumsW (KF.trans G)))))))))))

/-- Part C: `Π_j (m_j+1)²`. -/
def nCW : WM (LNS x) LNR :=
  .seq (.inc (G 52)) (.seq (SymQM.sqStepW sq0) (.seq (SymQM.sqStepW sq1) (.seq (SymQM.sqStepW sq2) (SymQM.sqStepW
  sq3))))

/-- Part D: `2^{2kh}`, `R`, `EU`, the unit count. -/
def nDW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (SGb 8) (G 57) (G 63)) (.seq (dbl (G 57) (G 58)) (.seq (pow2W (pN.trans G)) (.seq
  (WM.clear (G 57)) (.seq (FinalPass.Hash4.wcopyR dNC (G 54) (G 63)) (.seq (addTo dA (G 54) (G 63)) (.seq (addTo dA
  (G 54) (G 63)) (.seq (FinalPass.Hash4.wcopyR dMS (G 55) (G 63)) (.seq (StarNums.incN (G 55) 3) (.seq (mulByW
  (mE.trans G)) (.seq (StarNums.incN (G 55) 2) (.seq (FinalPass.Hash4.wcopyR (G 21) (G 56) (G 63)) (.seq (mulByW
  (mT1.trans G)) (.seq (mulByW (mT2.trans G)) (.seq (mulByW (mT3.trans G)) (mulByW (mT4.trans G))))))))))))))))

/-- **The call's state-space numbers.** -/
def symNumsW : WM (LNS x) LNR := .seq (nAW x) (.seq (nBW x) (.seq (nCW x) (nDW x)))

/-! ## The values -/

/-- The SYM filter's parameters from the call's `n`, cap and error exponent. -/
def gP (n capS err : ℕ) : Filters.GapParams := ⟨2 * (n + 1) ^ 26, capS, err⟩

/-- `Π_j (m_j+1)²` over the four padded slots. -/
def stV (m0 m1 m2 m3 : ℕ) : ℕ :=
  1 * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1)

/-- The list's `B`. -/
def bV (nc capS : ℕ) : ℕ := nc * 4096 * capS

/-- The units per state and cell `EU = R(M+3)+2`, `R = |carriers| + 2a`. -/
def euV (M nc a : ℕ) : ℕ := (M + 3) * (nc + a + a) + 2

/-- The SYM tape's unit count. -/
def totV (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) : ℕ :=
  2 ^ (gP n capS err).seedBits * 2 ^ FlatNums.fbv M (bV nc capS) (L + 5) * stV m0 m1 m2 m3 * 2 ^ (2 * kh) *
    euV M nc a

/-- The block's values after the program. -/
def numsVec (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) : Fin 64 → ℕ :=
  ![capS, 2 * (n + 1) ^ 26, err, (gP n capS err).prefixBits, (gP n capS err).labelBits, (gP n capS err).fieldBits,
    (gP n capS err).walkLen, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (gP n capS err).seedBits,
    2 ^ (gP n capS err).seedBits, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, M, bV nc capS, L + 5,
    Nat.clog 2 (bV nc capS) + 9, Nat.clog 2 M, FlatNums.rkv M (bV nc capS), FlatNums.sbv M (bV nc capS),
    FlatNums.wlv (L + 5), FlatNums.fbv M (bV nc capS) (L + 5), 2 ^ FlatNums.fbv M (bV nc capS) (L + 5),
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, stV m0 m1 m2 m3, 2 ^ (2 * kh), nc + a + a, euV M nc a,
    totV n capS err M nc L kh a m0 m1 m2 m3, 0, 0, 0, 0, 0, 0, 0]

/-- The program's capacity needs. -/
structure NumsNeed (cap n capS err M nc L kh a m0 m1 m2 m3 : ℕ) : Prop where
  c1 : 1 ≤ capS
  cS : capS * 32 + 2 ≤ cap
  cL : 2 * (n + 1) ^ 26 + 8 ≤ cap
  cE : err + 4 ≤ cap
  cSB : 2 ^ ((gP n capS err).seedBits + 1) ≤ cap
  cLB : (gP n capS err).labelBits + (gP n capS err).fieldBits + (gP n capS err).walkLen + 512 ≤ cap
  cB : bV nc capS + 4096 ≤ cap
  cF : M + bV nc capS + (L + 5) + 2 ^ (FlatNums.fbv M (bV nc capS) (L + 5) + 1) + 1000 ≤ cap
  cN : 2 ^ (2 * kh + 1) ≤ cap
  cT : 2 * totV n capS err M nc L kh a m0 m1 m2 m3 + M + nc + a + a + 10 ≤ cap
  cM : m0 + m1 + m2 + m3 ≤ M

/-! ## Register facts -/

theorem G_ne (i : Fin 64) (r : Fin LNR) (h : r.val < 408) : r ≠ G i := fun e => by
  have := congrArg Fin.val e; rw [G_val] at this; omega

theorem nHb (i : Fin 64) : Hb 13 ≠ G i := G_ne i _ (by decide)
theorem ndN (i : Fin 64) : dN ≠ G i := G_ne i _ (by decide)
theorem nSG10 (i : Fin 64) : SGb 10 ≠ G i := G_ne i _ (by decide)
theorem ndMS (i : Fin 64) : dMS ≠ G i := G_ne i _ (by decide)
theorem ndNC (i : Fin 64) : dNC ≠ G i := G_ne i _ (by decide)
theorem nSG1 (i : Fin 64) : SGb 1 ≠ G i := G_ne i _ (by decide)
theorem nSG8 (i : Fin 64) : SGb 8 ≠ G i := G_ne i _ (by decide)
theorem ndA (i : Fin 64) : dA ≠ G i := G_ne i _ (by decide)
theorem nM0 (i : Fin 64) : dM0 ≠ G i := G_ne i _ (by decide)
theorem nM1 (i : Fin 64) : dM1 ≠ G i := G_ne i _ (by decide)
theorem nM2 (i : Fin 64) : dM2 ≠ G i := G_ne i _ (by decide)
theorem nM3 (i : Fin 64) : dM3 ≠ G i := G_ne i _ (by decide)

/-! ## The parts' exit states -/

/-- After part A. -/
def aOut (σ : WState (LNS x) LNR) (n capS err : ℕ) : WState (LNS x) LNR :=
  (((((((((((((σ).setv (G 0) (capS)).setv (G 57) (n)).setv (G 57) (n + 1)).setv (G 1) ((n + 1) ^ 26)).setv (G 1) (2 *
    (n + 1) ^ 26)).setv (G 57) (0)).setv (G 2) (err)).setv (G 3) ((gP n capS err).prefixBits)).setv (G 4) ((gP n capS
    err).labelBits)).setv (G 5) ((gP n capS err).fieldBits)).setv (G 6) ((gP n capS err).walkLen)).setv (G 20) ((gP n
    capS err).seedBits)).setv (G 21) (2 ^ (gP n capS err).seedBits)

/-- After part B. -/
def bOut (σ : WState (LNS x) LNR) (M nc capS L : ℕ) : WState (LNS x) LNR :=
  (((((((((((((((((σ).setv (G 32) (M)).setv (G 33) (nc)).setv (G 58) (4096)).setv (G 33) (nc * 4096)).setv (G 58)
    (0)).setv (G 58) (capS)).setv (G 33) (nc * 4096 * capS)).setv (G 58) (0)).setv (G 34) (L)).setv (G 34) (L +
    5)).setv (G 35) (Nat.clog 2 (nc * 4096 * capS) + 9)).setv (G 36) (Nat.clog 2 M)).setv (G 37) (FlatNums.rkv M (nc *
    4096 * capS))).setv (G 38) (FlatNums.sbv M (nc * 4096 * capS))).setv (G 39) (FlatNums.wlv (L + 5))).setv (G 40)
    (FlatNums.fbv M (nc * 4096 * capS) (L + 5))).setv (G 41) (2 ^ FlatNums.fbv M (nc * 4096 * capS) (L + 5))

/-- After part C. -/
def cOut (σ : WState (LNS x) LNR) (m0 m1 m2 m3 : ℕ) : WState (LNS x) LNR :=
  (((((σ).setv (G 52) (0 + 1)).setv (G 52) ((0 + 1) * (m0 + 1) * (m0 + 1))).setv (G 52) ((0 + 1) * (m0 + 1) * (m0 + 1)
    * (m1 + 1) * (m1 + 1))).setv (G 52) ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 +
    1))).setv (G 52) ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1))

/-- After part D. -/
def dOut (σ : WState (LNS x) LNR) (kh nc a M t21 t41 t52 : ℕ) : WState (LNS x) LNR :=
  ((((((((((((((((σ).setv (G 57) (kh)).setv (G 57) (2 * kh)).setv (G 53) (2 ^ (2 * kh))).setv (G 57) (0)).setv (G 54)
    (nc)).setv (G 54) (nc + a)).setv (G 54) (nc + a + a)).setv (G 55) (M)).setv (G 55) (M + 3)).setv (G 55) ((M + 3) *
    (nc + a + a))).setv (G 55) ((M + 3) * (nc + a + a) + 2)).setv (G 56) (t21)).setv (G 56) (t21 * t41)).setv (G 56)
    (t21 * t41 * t52)).setv (G 56) (t21 * t41 * t52 * 2 ^ (2 * kh))).setv (G 56) (t21 * t41 * t52 * 2 ^ (2 * kh) * ((M
    + 3) * (nc + a + a) + 2))

/-! ## The parts' runs -/

theorem nA_spec (cap : ℕ) (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ)
    (vC : σ.val (Hb 13) = capS) (vN : σ.val dN = n) (vE : σ.val (SGb 10) = err) (hz : ∀ i, σ.val (G i) = 0)
    (hN : NumsNeed cap n capS err M nc L kh a m0 m1 m2 m3) :
    WExec cap (nAW x) σ (aOut x σ n capS err) (234 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have cL := hN.cL
  have cS := hN.cS
  have cE := hN.cE
  have p26 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hsb : 1 ≤ 2 ^ (gP n capS err).seedBits := Nat.one_le_two_pow
  unfold nAW
  refine seqD cap _ 1 (copy1 cap (Hb 13) (G 0) (G 63) (by decide) (by decide) (by decide) capS _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap dN (G 57) (G 63) (by decide) (by decide) (by decide) n _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (G 57) n _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 108 (pow1 cap (pw26.trans G) (n + 1) 26 _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (G 1) (G 58) (by decide) ((n + 1) ^ 26) _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (G 57) (n + 1) _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (SGb 10) (G 2) (G 63) (by decide) (by decide) (by decide) err _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 110 (GapNums.gapNums_spec cap (KG.trans G) _ (gP n capS err) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply] at hi ⊢) (by simp [gP]; exact hN.c1) (by simp [gP]; omega) (by omega) hN.cS (by simp [gP]; omega) (by simp [gP]; omega) hN.cSB hN.cLB) ?_ (by omega) (by omega)
  simp only [aOut, Function.Embedding.trans_apply, KG_apply, pw26_apply, Matrix.cons_val]

theorem nB_spec (cap : ℕ) (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ)
    (hG0 : σ.val (G 0) = capS) (vM : σ.val dMS = M) (vNC : σ.val dNC = nc) (vL : σ.val (SGb 1) = L)
    (hz : ∀ i : Fin 64, 32 ≤ i.val → σ.val (G i) = 0) (hN : NumsNeed cap n capS err M nc L kh a m0 m1 m2 m3) :
    WExec cap (nBW x) σ (bOut x σ M nc capS L) (137 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have cB := hN.cB
  have cF := hN.cF
  have cS := hN.cS
  have cT := hN.cT
  have hB0 : nc * 4096 ≤ nc * 4096 * capS := Nat.le_mul_of_pos_right _ hN.c1
  have hB1 : nc * 4096 * capS = bV nc capS := rfl
  have hfb : 1 ≤ 2 ^ FlatNums.fbv M (bV nc capS) (L + 5) := Nat.one_le_two_pow
  have hsb : 1 ≤ 2 ^ (gP n capS err).seedBits := Nat.one_le_two_pow
  unfold nBW
  refine seqD cap _ 1 (copy1 cap dMS (G 32) (G 63) (by decide) (by decide) (by decide) M _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap dNC (G 33) (G 63) (by decide) (by decide) (by decide) nc _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (G 58) 4096 _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mB1.trans G) nc 4096 _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (G 58) 4096 _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (G 0) (G 58) (G 63) (by decide) (by decide) (by decide) capS _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mB1.trans G) (nc * 4096) capS _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, mB1_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (G 58) capS _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (SGb 1) (G 34) (G 63) (by decide) (by decide) (by decide) L _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (G 34) L 5 _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 110 (WExec.cast cap (FlatNums.flatNums_spec cap (KF.trans G) _ M (nc * 4096 * capS) (L + 5) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply] at hi ⊢) (by unfold bV at cF; omega)) (FlatNums.flatOut_eq _ _ _ _ _ (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, hG0, ndMS, ndNC, nSG1, vM, vNC, vL, KF_apply, Function.Embedding.trans_apply] at hi ⊢)) le_rfl) ?_ (by omega) (by omega)
  simp only [bOut, Function.Embedding.trans_apply, KF_apply, mB1_apply, Matrix.cons_val]

theorem nC_spec (cap : ℕ) (σ : WState (LNS x) LNR) (m0 m1 m2 m3 M : ℕ)
    (v0 : σ.val dM0 = m0) (v1 : σ.val dM1 = m1) (v2 : σ.val dM2 = m2) (v3 : σ.val dM3 = m3)
    (hz : ∀ i : Fin 64, 51 ≤ i.val → σ.val (G i) = 0) (hM : m0 + m1 + m2 + m3 ≤ M)
    (hcap : stV m0 m1 m2 m3 + M + 1 ≤ cap) :
    WExec cap (nCW x) σ (cOut x σ m0 m1 m2 m3) (60 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have s1 : (0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1) = stV m0 m1 m2 m3 := by
    unfold stV; ring
  have p1 : (0 + 1) * (m0 + 1) * (m0 + 1) ≤ stV m0 m1 m2 m3 := by
    have e : stV m0 m1 m2 m3 = ((0 + 1) * (m0 + 1) * (m0 + 1)) * ((m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1)) := by
      unfold stV; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have p2 : (0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) ≤ stV m0 m1 m2 m3 := by
    have e : stV m0 m1 m2 m3 = ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1)) * ((m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1)) := by unfold stV; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have p3 : (0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) ≤ stV m0 m1 m2 m3 := by
    have e : stV m0 m1 m2 m3 = ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1)) * ((m3 + 1) * (m3 + 1)) := by unfold stV; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have p4 : (0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1) = stV m0 m1 m2 m3 := by unfold stV; ring
  unfold nCW
  refine seqD cap _ 1 (inc1 cap (G 52) 0 _ (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 13 (SymQM.sqStepW_spec cap sq0 _ m0 (0 + 1) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 13 (SymQM.sqStepW_spec cap sq1 _ m1 ((0 + 1) * (m0 + 1) * (m0 + 1)) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 13 (SymQM.sqStepW_spec cap sq2 _ m2 ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1)) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 13 (SymQM.sqStepW_spec cap sq3 _ m3 ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1)) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nM0, nM1, nM2, nM3, v0, v1, v2, v3, sq0_apply, sq1_apply, sq2_apply, sq3_apply] at hi ⊢) (by omega)) ?_ (by omega) (by omega)
  simp only [cOut, sq0_apply, sq1_apply, sq2_apply, sq3_apply, Matrix.cons_val]

theorem nD_spec (cap : ℕ) (σ : WState (LNS x) LNR) (kh nc a M t21 t41 t52 : ℕ)
    (vK : σ.val (SGb 8) = kh) (vNC : σ.val dNC = nc) (vA : σ.val dA = a) (vM : σ.val dMS = M)
    (h21 : σ.val (G 21) = t21) (h41 : σ.val (G 41) = t41) (h52 : σ.val (G 52) = t52)
    (hz : ∀ i : Fin 64, 53 ≤ i.val → σ.val (G i) = 0) (p21 : 1 ≤ t21) (p41 : 1 ≤ t41) (p52 : 1 ≤ t52)
    (hkh : 2 ^ (2 * kh + 1) ≤ cap) (hcap : 2 * (t21 * t41 * t52 * 2 ^ (2 * kh) * ((M + 3) * (nc + a + a) + 2)) + M + nc + a + a + 10 ≤ cap) :
    WExec cap (nDW x) σ (dOut x σ kh nc a M t21 t41 t52) (44 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hk1 : 2 * kh < 2 ^ (2 * kh + 1) := by have := Nat.lt_two_pow_self (n := 2 * kh + 1); omega
  have hk2 : 1 ≤ 2 ^ (2 * kh) := Nat.one_le_two_pow
  have heu : 2 ≤ (M + 3) * (nc + a + a) + 2 := by omega
  have q1 : t21 ≤ t21 * t41 := Nat.le_mul_of_pos_right _ p41
  have q1' : t41 ≤ t21 * t41 := Nat.le_mul_of_pos_left _ p21
  have q2 : t21 * t41 ≤ t21 * t41 * t52 := Nat.le_mul_of_pos_right _ p52
  have q2' : t52 ≤ t21 * t41 * t52 := Nat.le_mul_of_pos_left _ (Nat.mul_pos p21 p41)
  have q3 : t21 * t41 * t52 ≤ t21 * t41 * t52 * 2 ^ (2 * kh) := Nat.le_mul_of_pos_right _ hk2
  have q3' : 2 ^ (2 * kh) ≤ t21 * t41 * t52 * 2 ^ (2 * kh) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos p21 p41) p52)
  have q4 : t21 * t41 * t52 * 2 ^ (2 * kh) ≤ t21 * t41 * t52 * 2 ^ (2 * kh) * ((M + 3) * (nc + a + a) + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have q4' : (M + 3) * (nc + a + a) + 2 ≤ t21 * t41 * t52 * 2 ^ (2 * kh) * ((M + 3) * (nc + a + a) + 2) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p21 p41) p52) hk2)
  have q5 : (M + 3) * (nc + a + a) ≤ (M + 3) * (nc + a + a) + 2 := by omega
  unfold nDW
  refine seqD cap _ 1 (copy1 cap (SGb 8) (G 57) (G 63) (by decide) (by decide) (by decide) kh _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (G 57) (G 58) (by decide) kh _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (SymQM.pow2v cap (pN.trans G) (2 * kh) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, pN_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, pN_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, pN_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, pN_apply, Function.Embedding.trans_apply]) hkh) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (G 57) (2 * kh) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap dNC (G 54) (G 63) (by decide) (by decide) (by decide) nc _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap dA (G 54) (G 63) (by decide) (by decide) (by decide) a nc _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap dA (G 54) (G 63) (by decide) (by decide) (by decide) a (nc + a) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap dMS (G 55) (G 63) (by decide) (by decide) (by decide) M _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (G 55) M 3 _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mE.trans G) (M + 3) (nc + a + a) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mE_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mE_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mE_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mE_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mE_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (G 55) ((M + 3) * (nc + a + a)) 2 _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (G 21) (G 56) (G 63) (by decide) (by decide) (by decide) t21 _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mT1.trans G) (t21) (t41) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT1_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT1_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mT2.trans G) (t21 * t41) (t52) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT2_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT2_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT2_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT2_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT2_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (mT3.trans G) (t21 * t41 * t52) (2 ^ (2 * kh)) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT3_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT3_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT3_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT3_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT3_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 3 (mulBy1 cap (mT4.trans G) (t21 * t41 * t52 * 2 ^ (2 * kh)) (((M + 3) * (nc + a + a) + 2)) _ (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT4_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT4_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT4_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT4_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nSG8, ndNC, ndA, ndMS, vK, vNC, vA, vM, h21, h41, h52, mT4_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) ?_ (by omega) (by omega)
  simp only [dOut, pN_apply, mE_apply, mT1_apply, mT2_apply, mT3_apply, mT4_apply, Function.Embedding.trans_apply, Matrix.cons_val]

/-! ## The whole run -/

/-- The exit state. -/
def numsOut (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) : WState (LNS x) LNR :=
  dOut x (cOut x (bOut x (aOut x σ n capS err) M nc capS L) m0 m1 m2 m3) kh nc a M (2 ^ (gP n capS err).seedBits)
    (2 ^ FlatNums.fbv M (nc * 4096 * capS) (L + 5)) ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1))

theorem stV_eq (m0 m1 m2 m3 : ℕ) : (0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1) = stV m0 m1 m2 m3 := by unfold stV; ring

theorem totV_eq (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) :
    2 ^ (gP n capS err).seedBits * 2 ^ FlatNums.fbv M (nc * 4096 * capS) (L + 5) * ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1)) * 2 ^ (2 * kh) *
      ((M + 3) * (nc + a + a) + 2) = totV n capS err M nc L kh a m0 m1 m2 m3 := by
  unfold totV euV bV stV; ring

/-- **The block's values after the run.** -/
theorem numsOut_val (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) (hz : ∀ i, σ.val (G i) = 0)
    (i : Fin 64) : (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3).val (G i) = numsVec n capS err M nc L kh a m0 m1 m2 m3 i := by
  have e1 := stV_eq m0 m1 m2 m3
  have e2 := totV_eq n capS err M nc L kh a m0 m1 m2 m3
  unfold numsOut dOut cOut bOut aOut
  fin_cases i <;> simp [Function.update_apply, numsVec, hz, bV, euV, stV, totV] <;> ring

/-- Everything outside the block is unchanged. -/
theorem numsOut_other (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) (r : Fin LNR)
    (hr : ∀ i, G i ≠ r) : (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3).val r = σ.val r := by
  have hr' : ∀ i, r ≠ G i := fun i h => hr i h.symm
  unfold numsOut dOut cOut bOut aOut
  simp [Function.update_apply, hr']

theorem numsOut_st (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) :
    (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3).st = σ.st := by
  unfold numsOut dOut cOut bOut aOut; simp

theorem numsOut_sh (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) :
    (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3).sh = σ.sh := by
  unfold numsOut dOut cOut bOut aOut; simp

theorem numsOut_cell (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) :
    (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3).cell = σ.cell := by
  unfold numsOut dOut cOut bOut aOut; simp

theorem symNums_spec (cap : ℕ) (σ : WState (LNS x) LNR) (n capS err M nc L kh a m0 m1 m2 m3 : ℕ)
    (vC : σ.val (Hb 13) = capS) (vN : σ.val dN = n) (vE : σ.val (SGb 10) = err) (vM : σ.val dMS = M)
    (vNC : σ.val dNC = nc) (vL : σ.val (SGb 1) = L) (vK : σ.val (SGb 8) = kh) (vA : σ.val dA = a)
    (v0 : σ.val dM0 = m0) (v1 : σ.val dM1 = m1) (v2 : σ.val dM2 = m2) (v3 : σ.val dM3 = m3)
    (hz : ∀ i, σ.val (G i) = 0) (hN : NumsNeed cap n capS err M nc L kh a m0 m1 m2 m3) :
    WExec cap (symNumsW x) σ (numsOut x σ n capS err M nc L kh a m0 m1 m2 m3) (500 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have eA := nA_spec x cap σ n capS err M nc L kh a m0 m1 m2 m3 vC vN vE hz hN
  have eB := nB_spec x cap (aOut x σ n capS err) n capS err M nc L kh a m0 m1 m2 m3
    (by simp [aOut]) (by simp [aOut, Function.update_apply, ndMS, vM]) (by simp [aOut, Function.update_apply, ndNC, vNC])
    (by simp [aOut, Function.update_apply, nSG1, vL])
    (fun i hi => by fin_cases i <;> simp [aOut, Function.update_apply, hz] at hi ⊢) hN
  have eC := nC_spec x cap (bOut x (aOut x σ n capS err) M nc capS L) m0 m1 m2 m3 M
    (by simp [aOut, bOut, Function.update_apply, nM0, v0]) (by simp [aOut, bOut, Function.update_apply, nM1, v1])
    (by simp [aOut, bOut, Function.update_apply, nM2, v2]) (by simp [aOut, bOut, Function.update_apply, nM3, v3])
    (fun i hi => by fin_cases i <;> simp [aOut, bOut, Function.update_apply, hz] at hi ⊢) hN.cM
    (by have := hN.cT; have := stV_eq m0 m1 m2 m3
        have h1 : stV m0 m1 m2 m3 ≤ totV n capS err M nc L kh a m0 m1 m2 m3 := by
          unfold totV
          have p1 : 1 ≤ 2 ^ (gP n capS err).seedBits := Nat.one_le_two_pow
          have p2 : 1 ≤ 2 ^ FlatNums.fbv M (bV nc capS) (L + 5) := Nat.one_le_two_pow
          have p3 : 1 ≤ 2 ^ (2 * kh) := Nat.one_le_two_pow
          have p4 : 1 ≤ euV M nc a := by unfold euV; omega
          calc stV m0 m1 m2 m3 ≤ 2 ^ (gP n capS err).seedBits * 2 ^ FlatNums.fbv M (bV nc capS) (L + 5) *
                stV m0 m1 m2 m3 := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
            _ ≤ _ * 2 ^ (2 * kh) := Nat.le_mul_of_pos_right _ (by omega)
            _ ≤ _ * euV M nc a := Nat.le_mul_of_pos_right _ (by omega)
        omega)
  have eD := nD_spec x cap (cOut x (bOut x (aOut x σ n capS err) M nc capS L) m0 m1 m2 m3) kh nc a M
    (2 ^ (gP n capS err).seedBits) (2 ^ FlatNums.fbv M (nc * 4096 * capS) (L + 5)) ((0 + 1) * (m0 + 1) * (m0 + 1) * (m1 + 1) * (m1 + 1) * (m2 + 1) * (m2 + 1) * (m3 + 1) * (m3 + 1))
    (by simp [aOut, bOut, cOut, Function.update_apply, nSG8, vK]) (by simp [aOut, bOut, cOut, Function.update_apply, ndNC, vNC])
    (by simp [aOut, bOut, cOut, Function.update_apply, ndA, vA]) (by simp [aOut, bOut, cOut, Function.update_apply, ndMS, vM])
    (by simp [aOut, bOut, cOut, Function.update_apply]) (by simp [aOut, bOut, cOut, Function.update_apply])
    (by simp [aOut, bOut, cOut, Function.update_apply])
    (fun i hi => by fin_cases i <;> simp [aOut, bOut, cOut, Function.update_apply, hz] at hi ⊢)
    Nat.one_le_two_pow Nat.one_le_two_pow (Nat.one_le_iff_ne_zero.mpr (by positivity)) hN.cN
    (by have := hN.cT; have := totV_eq n capS err M nc L kh a m0 m1 m2 m3; omega)
  unfold symNumsW numsOut
  exact WExec.mono (WExec.seq eA (WExec.seq eB (WExec.seq eC eD))) (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
