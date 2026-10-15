import Proof.Wire_3_5.PrimAsmCapNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltNum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

variable {ns nr : ℕ} (cap : ℕ)

/-- `⌈log₂ V⌉ = natBitLength (V − 1)` for `V ≥ 2`. -/
theorem clog_eq_nbl (V : ℕ) (hV : 2 ≤ V) : Nat.clog 2 V = natBitLength (V - 1) := by
  have h := StarNums.clog_two_add_two (V - 2)
  rwa [show V - 2 + 2 = V by omega, show V - 2 + 1 = V - 1 by omega] at h

/-! ### Specs with the values named -/

theorem bitLen1 (R : Fin 8 ↪ Fin nr) (v : ℕ) (σ : WState ns nr) (hv : σ.val (R 0) = v) (hw : σ.val (R 1) = 0)
    (hq : σ.val (R 2) = 0) (hrb : σ.val (R 3) = 0) (hL : σ.val (R 4) = 0) (ht : σ.val (R 6) = 0) (hcap : v + 2 ≤ cap) :
    WExec cap (bitLenM R) σ (σ.setv (R 4) (natBitLength v)) (UnaryPow.sq cap) := by
  have h := bitLenM_spec cap R σ hw hq hrb hL ht (by rw [hv]; exact hcap)
  rw [hv] at h
  have hs : 100 * cap + 100 ≤ UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
  exact WExec.mono h (by omega)

theorem halve1 (w q rb : Fin nr) (hwq : w ≠ q) (hwr : w ≠ rb) (hqr : q ≠ rb) (v : ℕ) (σ : WState ns nr)
    (hv : σ.val w = v) (hq : σ.val q = 0) (hr : σ.val rb = 0) (hcap : v ≤ cap) (hc1 : 1 ≤ cap) :
    WExec cap (halveM w q rb) σ ((σ.setv w (v / 2)).setv rb (v % 2)) (UnaryPow.sq cap) := by
  have h := halveM_spec cap w q rb hwq hwr hqr σ hq hr (by rw [hv]; exact hcap) hc1
  rw [hv] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

theorem dbl1 (p t : Fin nr) (hpt : p ≠ t) (v : ℕ) (σ : WState ns nr) (hv : σ.val p = v) (ht : σ.val t = 0)
    (hcap : 2 * v ≤ cap) : WExec cap (dbl p t) σ (σ.setv p (2 * v)) (UnaryPow.sq cap) := by
  have h := dbl_spec cap p t hpt σ ht (by rw [hv]; exact hcap)
  rw [hv] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

/-! The block `K : Fin 32 ↪ Fin nr`: `0` the cap `B`, `1` `n`, `2` `errExp`, `3` prefixBits, `4` labelBits,
`5` fieldBits, `6` walkLen (outputs), `7` `⌈log₂ M⌉`, `8` `32B`, `9` `n+1`, `10` `M`, `11` constant, `12` product temp,
`13` flag, `14 … 31` scratch. -/

def bP : Fin 8 ↪ Fin 32 := ⟨![8, 14, 15, 16, 3, 17, 18, 19], by decide⟩
def bC : Fin 8 ↪ Fin 32 := ⟨![10, 14, 15, 16, 7, 17, 18, 19], by decide⟩
def mX : Fin 5 ↪ Fin 32 := ⟨![0, 11, 8, 14, 15], by decide⟩
def p26 : Fin 5 ↪ Fin 32 := ⟨![9, 10, 14, 15, 16], by decide⟩
def m2 : Fin 5 ↪ Fin 32 := ⟨![10, 11, 12, 14, 15], by decide⟩
def gPC : Fin 6 ↪ Fin 32 := ⟨![3, 7, 13, 14, 15, 16], by decide⟩

@[simp] theorem bP_apply (i : Fin 8) : bP i = ![8, 14, 15, 16, 3, 17, 18, 19] i := rfl
@[simp] theorem bC_apply (i : Fin 8) : bC i = ![10, 14, 15, 16, 7, 17, 18, 19] i := rfl
@[simp] theorem mX_apply (i : Fin 5) : mX i = ![0, 11, 8, 14, 15] i := rfl
@[simp] theorem p26_apply (i : Fin 5) : p26 i = ![9, 10, 14, 15, 16] i := rfl
@[simp] theorem m2_apply (i : Fin 5) : m2 i = ![10, 11, 12, 14, 15] i := rfl
@[simp] theorem gPC_apply (i : Fin 6) : gPC i = ![3, 7, 13, 14, 15, 16] i := rfl

/-- Part A: `K 3 := ⌈log₂(32B)⌉`. -/
def filtA (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (K 11) 32) (.seq (mulAddW (mX.trans K)) (.seq (WM.clear (K 11)) (.seq (.dec (K 8))
  (.seq (bitLenM (bP.trans K)) (WM.clear (K 8))))))

/-- Part B: `K 7 := ⌈log₂ M⌉`, `K 5 := ⌈log₂ M⌉ + 4`, `K 4 := max (K 3) (K 7)`. -/
def filtB (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (K 1) (K 9) (K 14)) (.seq (.inc (K 9)) (.seq (UnaryPow.powConstW (p26.trans K) 26)
  (.seq (WM.clear (K 9)) (.seq (StarNums.incN (K 11) 2) (.seq (mulByW (m2.trans K)) (.seq (WM.clear (K 11))
  (.seq (.dec (K 10)) (.seq (bitLenM (bC.trans K)) (.seq (WM.clear (K 10))
  (.seq (FinalPass.Hash4.wcopyR (K 7) (K 5) (K 14)) (.seq (StarNums.incN (K 5) 4)
  (.seq (gtFlagW (gPC.trans K)) (.seq (.ifr (K 13) (FinalPass.Hash4.wcopyR (K 3) (K 4) (K 14))
    (FinalPass.Hash4.wcopyR (K 7) (K 4) (K 14))) (WM.clear (K 13)))))))))))))))

/-- Part C: `K 6 := 2⌊E/4⌋ + 1`, and `K 7` cleared. -/
def filtC (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (K 2) (K 6) (K 14)) (.seq (halveM (K 6) (K 14) (K 15)) (.seq (WM.clear (K 15))
  (.seq (halveM (K 6) (K 14) (K 15)) (.seq (WM.clear (K 15)) (.seq (dbl (K 6) (K 14)) (.seq (.inc (K 6))
  (WM.clear (K 7))))))))

/-- **The filter's parameters** from the cap, `n` and `errExp`. -/
def filtM (K : Fin 32 ↪ Fin nr) : WM ns nr := .seq (filtA K) (.seq (filtB K) (filtC K))

theorem incN1 (r : Fin nr) (v c : ℕ) (σ : WState ns nr) (hr : σ.val r = v) (hc : v + c ≤ cap) :
    WExec cap (StarNums.incN r c) σ (σ.setv r (v + c)) (UnaryPow.sq cap) := by
  have h := StarNums.incN_spec cap r c σ (by rw [hr]; exact hc)
  rw [hr] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

/-- The larger of two registers, copied: `R 4 := max (R 3) (R 7)` by the flag `R 13 = [R 7 < R 3]`. -/
theorem maxCopy1 (K : Fin 32 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha : σ.val (K 3) = a) (hb : σ.val (K 7) = b)
    (hf : σ.val (K 13) = if b < a then 1 else 0) (h4 : σ.val (K 4) = 0) (h14 : σ.val (K 14) = 0) (hac : a ≤ cap)
    (hbc : b ≤ cap) :
    WExec cap (.ifr (K 13) (FinalPass.Hash4.wcopyR (K 3) (K 4) (K 14)) (FinalPass.Hash4.wcopyR (K 7) (K 4) (K 14))) σ
      (σ.setv (K 4) (max a b)) (2 * UnaryPow.sq cap) := by
  have hs := UnaryPow.sq_ge cap
  by_cases hlt : b < a
  · rw [if_pos hlt] at hf
    have h := copy1 cap (K 3) (K 4) (K 14) (by simp) (by simp) (by simp) a σ ha h4 h14 hac
    rw [show max a b = a by omega]
    exact WExec.mono (WExec.ifrT (by rw [hf]; omega) h) (by omega)
  · rw [if_neg hlt] at hf
    have h := copy1 cap (K 7) (K 4) (K 14) (by simp) (by simp) (by simp) b σ hb h4 h14 hbc
    rw [show max a b = b by omega]
    exact WExec.mono (WExec.ifrF hf h) (by omega)

theorem filtA_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (B : ℕ) (hB0 : σ.val (K 0) = B)
    (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0) (hB1 : 1 ≤ B) (hBc : B * 32 + 2 ≤ cap) :
    WExec cap (filtA K) σ (σ.setv (K 3) (Nat.clog 2 (32 * B))) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hv : Nat.clog 2 (32 * B) = natBitLength (0 + B * 32 - 1) := by
    rw [clog_eq_nbl _ (by omega), Nat.zero_add, Nat.mul_comm]
  rw [hv]
  unfold filtA
  refine seqD cap _ 1 (incN0 cap (K 11) 32 σ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mX.trans K) B 32 0 _ (by simp [hB0]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 11) 32 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (K 8) (0 + B * 32) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (bitLen1 cap (bP.trans K) (0 + B * 32 - 1) _ (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (K 8) (0 + B * 32 - 1) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, bP_apply, mX_apply, Matrix.cons_val]
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- Part B at an opaque power `P = (n+1)^{26}` (the exponent never reaches unification). -/
theorem filtB_run (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (n PB P : ℕ) (hP : (n + 1) ^ 26 = P)
    (hn0 : σ.val (K 1) = n) (hP0 : σ.val (K 3) = PB) (hz : ∀ i : Fin 32, 4 ≤ i.val → σ.val (K i) = 0)
    (hc1 : 1 ≤ cap) (hnc : n + 1 ≤ cap) (hpc : P * 2 + 8 ≤ cap) (hPc : PB ≤ cap) :
    WExec cap (filtB K) σ (((σ.setv (K 7) (natBitLength (P * 2 - 1))).setv (K 5)
      (natBitLength (P * 2 - 1) + 4)).setv (K 4) (max PB (natBitLength (P * 2 - 1))))
      (160 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hp : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ (by omega)
  obtain ⟨CL, hCL⟩ : ∃ CL, natBitLength (P * 2 - 1) = CL := ⟨_, rfl⟩
  rw [hCL]
  have hCLc : CL + 4 ≤ cap := by
    have := CopyNat.natBitLength_le_self_succ (P * 2 - 1); omega
  have hp26 : (n + 1) ^ 26 ≤ cap := by rw [hP]; omega
  unfold filtB
  refine seqD cap _ 1 (copy1 cap (K 1) (K 9) (K 14) (by simp) (by simp) (by simp) n _ (by simp [hn0])
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (K 9) n _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 108 (pow1 cap (p26.trans K) (n + 1) 26 _ (by simp) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hnc hp26) (by omega) (by omega) ?_
  rw [hP]
  refine seqD cap _ 1 (clear1 cap (K 9) (n + 1) _ (by simp) hnc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (K 11) 2 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m2.trans K) P 2 _ (by simp) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 11) 2 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (K 10) (P * 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (bitLen1 cap (bC.trans K) (P * 2 - 1) _ (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  rw [hCL]
  refine seqD cap _ 1 (clear1 cap (K 10) (P * 2 - 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (K 7) (K 5) (K 14) (by simp) (by simp) (by simp) CL _ (by simp)
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (K 5) CL 4 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (gt1 cap (gPC.trans K) PB CL _ (by simp [hP0]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hPc (by omega) hc1) (by omega) (by omega) ?_
  refine seqD cap _ 2 (maxCopy1 cap K PB CL _ (by simp [hP0]) (by simp) (by simp) (by simp [hz])
    (by simp [hz]) hPc (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (K 13) (if CL < PB then 1 else 0) _ (by simp)
    (by split_ifs <;> omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, bC_apply, p26_apply, m2_apply, gPC_apply, Matrix.cons_val]
  clear hn0 hP0 hc1 hnc hpc hPc hsq hp hCLc hp26 hP hCL
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

theorem filtB_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (n PB : ℕ) (hn0 : σ.val (K 1) = n)
    (hP0 : σ.val (K 3) = PB) (hz : ∀ i : Fin 32, 4 ≤ i.val → σ.val (K i) = 0) (hc1 : 1 ≤ cap) (hnc : n + 1 ≤ cap)
    (hpc : (n + 1) ^ 26 * 2 + 8 ≤ cap) (hPc : PB ≤ cap) :
    WExec cap (filtB K) σ (((σ.setv (K 7) (Nat.clog 2 (2 * (n + 1) ^ 26))).setv (K 5)
      (Nat.clog 2 (2 * (n + 1) ^ 26) + 4)).setv (K 4) (max PB (Nat.clog 2 (2 * (n + 1) ^ 26))))
      (160 * UnaryPow.sq cap) := by
  have hp : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have hv : Nat.clog 2 (2 * (n + 1) ^ 26) = natBitLength ((n + 1) ^ 26 * 2 - 1) := by
    rw [clog_eq_nbl _ (by omega), Nat.mul_comm]
  rw [hv]
  exact filtB_run cap K σ n PB ((n + 1) ^ 26) rfl hn0 hP0 hz hc1 hnc hpc hPc

theorem filtC_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (E CL : ℕ) (hE0 : σ.val (K 2) = E)
    (hC0 : σ.val (K 7) = CL) (h6 : σ.val (K 6) = 0) (hz : ∀ i : Fin 32, 14 ≤ i.val → σ.val (K i) = 0)
    (hc1 : 1 ≤ cap) (hEc : E + 4 ≤ cap) (hCc : CL ≤ cap) :
    WExec cap (filtC K) σ ((σ.setv (K 6) (2 * (E / 4) + 1)).setv (K 7) 0) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hE4 : 2 * (E / 2 / 2) ≤ cap := by omega
  unfold filtC
  refine seqD cap _ 1 (copy1 cap (K 2) (K 6) (K 14) (by simp) (by simp) (by simp) E σ hE0 h6 (by simp [hz])
    (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (K 6) (K 14) (K 15) (by simp) (by simp) (by simp) E _ (by simp) (by simp [hz])
    (by simp [hz]) (by omega) hc1) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 15) (E % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (K 6) (K 14) (K 15) (by simp) (by simp) (by simp) (E / 2) _ (by simp)
    (by simp [hz]) (by simp) (by omega) hc1) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 15) (E / 2 % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (K 6) (K 14) (by simp) (E / 2 / 2) _ (by simp) (by simp [hz]) hE4) (by omega)
    (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (K 6) (2 * (E / 2 / 2)) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (K 7) CL _ (by simp [hC0]) hCc) ?_ (by omega) (by omega)
  have hdiv : E / 2 / 2 = E / 4 := by omega
  rw [hdiv]
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, h6]

theorem filtM_run' (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (B n E PB CL : ℕ) (hPB : Nat.clog 2 (32 * B) = PB)
    (hCL : Nat.clog 2 (2 * (n + 1) ^ 26) = CL) (hB0 : σ.val (K 0) = B)
    (hn0 : σ.val (K 1) = n) (hE0 : σ.val (K 2) = E) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0)
    (hB1 : 1 ≤ B) (hc1 : 1 ≤ cap) (hBc : B * 32 + 2 ≤ cap) (hnc : n + 1 ≤ cap) (hpc : (n + 1) ^ 26 * 2 + 8 ≤ cap)
    (hEc : E + 4 ≤ cap) (hPc : PB ≤ cap) (hCc : CL ≤ cap) :
    WExec cap (filtM K) σ ((((σ.setv (K 3) PB).setv (K 5) (CL + 4)).setv (K 4) (max PB CL)).setv (K 6)
      (2 * (E / 4) + 1)) (201 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hA := filtA_spec cap K σ B hB0 hz hB1 hBc
  rw [hPB] at hA
  have hB := filtB_spec cap K (σ.setv (K 3) PB) n PB (by simp [hn0]) (by simp)
    (fun i hi => by
      have hi3 : i ≠ 3 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hi3, hz i (by omega)]) hc1 hnc hpc hPc
  rw [hCL] at hB
  have hC := filtC_spec cap K ((((σ.setv (K 3) PB).setv (K 7) CL).setv (K 5) (CL + 4)).setv (K 4) (max PB CL)) E CL
    (by simp [hE0]) (by simp) (by simp [hz]) (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hn3, hn7, hn5, hn4, hz i (by omega)]) hc1 hEc hCc
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB hC)) ?_ (by omega)
  clear hA hB hC hB0 hn0 hE0 hB1 hc1 hBc hnc hpc hEc hPc hCc hsq hPB hCL
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

theorem filtM_run (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (B n E : ℕ) (hB0 : σ.val (K 0) = B)
    (hn0 : σ.val (K 1) = n) (hE0 : σ.val (K 2) = E) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0)
    (hB1 : 1 ≤ B) (hc1 : 1 ≤ cap) (hBc : B * 32 + 2 ≤ cap) (hnc : n + 1 ≤ cap) (hpc : (n + 1) ^ 26 * 2 + 8 ≤ cap)
    (hEc : E + 4 ≤ cap) :
    WExec cap (filtM K) σ ((((σ.setv (K 3) (Nat.clog 2 (32 * B))).setv (K 5) (Nat.clog 2 (2 * (n + 1) ^ 26) + 4)).setv
      (K 4) (max (Nat.clog 2 (32 * B)) (Nat.clog 2 (2 * (n + 1) ^ 26)))).setv (K 6) (2 * (E / 4) + 1))
      (201 * UnaryPow.sq cap) := by
  have hPc : Nat.clog 2 (32 * B) ≤ cap := by
    have h1 := clog_eq_nbl (32 * B) (by omega)
    have h2 := CopyNat.natBitLength_le_self_succ (32 * B - 1)
    omega
  have hCc : Nat.clog 2 (2 * (n + 1) ^ 26) ≤ cap := by
    have hp : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
    have h1 := clog_eq_nbl (2 * (n + 1) ^ 26) (by omega)
    have h2 := CopyNat.natBitLength_le_self_succ (2 * (n + 1) ^ 26 - 1)
    omega
  exact filtM_run' cap K σ B n E _ _ rfl rfl hB0 hn0 hE0 hz hB1 hc1 hBc hnc hpc hEc hPc hCc

theorem filtM_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (P : Filters.GapParams) (n : ℕ)
    (hlen : P.len = 2 * (n + 1) ^ 26) (hB0 : σ.val (K 0) = P.cap) (hn0 : σ.val (K 1) = n)
    (hE0 : σ.val (K 2) = P.errExp) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0) (hB1 : 1 ≤ P.cap)
    (hc1 : 1 ≤ cap) (hBc : P.cap * 32 + 2 ≤ cap) (hnc : n + 1 ≤ cap) (hpc : (n + 1) ^ 26 * 2 + 8 ≤ cap)
    (hEc : P.errExp + 4 ≤ cap) :
    WExec cap (filtM K) σ ((((σ.setv (K 3) P.prefixBits).setv (K 5) P.fieldBits).setv (K 4) P.labelBits).setv
      (K 6) P.walkLen) (201 * UnaryPow.sq cap) := by
  have h := filtM_run cap K σ P.cap n P.errExp hB0 hn0 hE0 hz hB1 hc1 hBc hnc hpc hEc
  unfold Filters.GapParams.prefixBits Filters.GapParams.fieldBits Filters.GapParams.labelBits
    Filters.GapParams.walkLen
  rw [hlen]
  exact h

end NearCubicWires.WireExponent3_5.PrimAsm.FiltNum
