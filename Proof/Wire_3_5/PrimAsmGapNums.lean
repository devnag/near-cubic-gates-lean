import Proof.Wire_3_5.PrimAsmFiltNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.GapNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum NearCubicWires.WireExponent3_5.PrimAsm.FiltNum
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ} (cap : ℕ)

/-- Part B': `K 7 := ⌈log₂ M⌉` from `K 1 = M`, `K 5 := K 7 + 4`, `K 4 := max (K 3) (K 7)`. -/
def gB (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (K 1) (K 10) (K 14)) (.seq (.dec (K 10)) (.seq (bitLenM (bC.trans K))
  (.seq (WM.clear (K 10)) (.seq (FinalPass.Hash4.wcopyR (K 7) (K 5) (K 14)) (.seq (StarNums.incN (K 5) 4)
  (.seq (gtFlagW (gPC.trans K)) (.seq (.ifr (K 13) (FinalPass.Hash4.wcopyR (K 3) (K 4) (K 14))
    (FinalPass.Hash4.wcopyR (K 7) (K 4) (K 14))) (WM.clear (K 13)))))))))

theorem gB_run (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (M PB : ℕ) (hM0 : σ.val (K 1) = M) (hM2 : 2 ≤ M)
    (hP0 : σ.val (K 3) = PB) (hz : ∀ i : Fin 32, 4 ≤ i.val → σ.val (K i) = 0) (hc1 : 1 ≤ cap) (hMc : M + 8 ≤ cap)
    (hPc : PB ≤ cap) :
    WExec cap (gB K) σ (((σ.setv (K 7) (Nat.clog 2 M)).setv (K 5) (Nat.clog 2 M + 4)).setv (K 4)
      (max PB (Nat.clog 2 M))) (20 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hCL : Nat.clog 2 M = natBitLength (M - 1) := clog_eq_nbl M hM2
  obtain ⟨CL, hCLd⟩ : ∃ CL, natBitLength (M - 1) = CL := ⟨_, rfl⟩
  rw [hCL, hCLd]
  have hCLc : CL + 4 ≤ cap := by have := CopyNat.natBitLength_le_self_succ (M - 1); omega
  unfold gB
  refine seqD cap _ 1 (copy1 cap (K 1) (K 10) (K 14) (by simp) (by simp) (by simp) M _ (by simp [hM0])
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (K 10) M _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (bitLen1 cap (bC.trans K) (M - 1) _ (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  rw [hCLd]
  refine seqD cap _ 1 (clear1 cap (K 10) (M - 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (K 7) (K 5) (K 14) (by simp) (by simp) (by simp) CL _ (by simp)
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (K 5) CL 4 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (gt1 cap (gPC.trans K) PB CL _ (by simp [hP0]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hPc (by omega) hc1) (by omega) (by omega) ?_
  refine seqD cap _ 2 (maxCopy1 cap K PB CL _ (by simp [hP0]) (by simp) (by simp) (by simp [hz])
    (by simp [hz]) hPc (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (K 13) (if CL < PB then 1 else 0) _ (by simp)
    (by split_ifs <;> omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, bC_apply, gPC_apply, Matrix.cons_val]
  clear hM0 hP0 hc1 hMc hPc hsq hCLc hCL hCLd
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ## The seed length -/

def mA : Fin 5 ↪ Fin 32 := ⟨![4, 11, 20, 26, 27], by decide⟩
def mB : Fin 5 ↪ Fin 32 := ⟨![24, 11, 20, 26, 27], by decide⟩
def mF : Fin 5 ↪ Fin 32 := ⟨![5, 11, 20, 26, 27], by decide⟩
def mW : Fin 5 ↪ Fin 32 := ⟨![25, 11, 20, 26, 27], by decide⟩
def pS : Fin 4 ↪ Fin 32 := ⟨![20, 21, 22, 23], by decide⟩

@[simp] theorem mA_apply (i : Fin 5) : mA i = ![4, 11, 20, 26, 27] i := rfl
@[simp] theorem mB_apply (i : Fin 5) : mB i = ![24, 11, 20, 26, 27] i := rfl
@[simp] theorem mF_apply (i : Fin 5) : mF i = ![5, 11, 20, 26, 27] i := rfl
@[simp] theorem mW_apply (i : Fin 5) : mW i = ![25, 11, 20, 26, 27] i := rfl
@[simp] theorem pS_apply (i : Fin 4) : pS i = ![20, 21, 22, 23] i := rfl

/-- Part S: `K 20 := 256·lb + 256·(lb−1) + 256·lb + 512·fb + 160·(wl−1)` (`seedBits`), `K 21 := 2^{K 20}`. -/
def gS (K : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (K 4) (K 24) (K 14)) (.seq (.dec (K 24))
  (.seq (FinalPass.Hash4.wcopyR (K 6) (K 25) (K 14)) (.seq (.dec (K 25))
  (.seq (StarNums.incN (K 11) 256) (.seq (mulAddW (mA.trans K)) (.seq (mulAddW (mB.trans K))
  (.seq (mulAddW (mA.trans K)) (.seq (WM.clear (K 11)) (.seq (StarNums.incN (K 11) 512)
  (.seq (mulAddW (mF.trans K)) (.seq (WM.clear (K 11)) (.seq (StarNums.incN (K 11) 160)
  (.seq (mulAddW (mW.trans K)) (.seq (WM.clear (K 11)) (.seq (WM.clear (K 24)) (.seq (WM.clear (K 25))
  (pow2W (pS.trans K))))))))))))))))))

/-- The seed length from the three numbers. -/
def sbOf (lb fb wl : ℕ) : ℕ := 2 * (128 * (lb + (lb - 1) + lb + 2 * fb)) + 160 * (wl - 1)

theorem sbOf_eq (lb fb wl : ℕ) :
    sbOf lb fb wl = lb * 256 + (lb - 1) * 256 + lb * 256 + fb * 512 + (wl - 1) * 160 := by
  unfold sbOf; ring_nf

theorem gS_run (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (lb fb wl : ℕ) (h4 : σ.val (K 4) = lb)
    (h5 : σ.val (K 5) = fb) (h6 : σ.val (K 6) = wl) (hlb : 1 ≤ lb) (hwl : 1 ≤ wl)
    (hz : ∀ i : Fin 32, (i.val = 11 ∨ 14 ≤ i.val) → σ.val (K i) = 0) (hc1 : 1 ≤ cap)
    (hsc : 2 ^ (sbOf lb fb wl + 1) ≤ cap) (hlc : lb + fb + wl + 512 ≤ cap) :
    WExec cap (gS K) σ ((σ.setv (K 20) (sbOf lb fb wl)).setv (K 21) (2 ^ sbOf lb fb wl)) (40 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hsb := sbOf_eq lb fb wl
  have hsbc : sbOf lb fb wl + 1 ≤ cap := by
    have := Nat.lt_two_pow_self (n := sbOf lb fb wl + 1); omega
  obtain ⟨sb, hsbd⟩ : ∃ s, s = sbOf lb fb wl := ⟨_, rfl⟩
  rw [← hsbd] at hsb hsc hsbc ⊢
  unfold gS
  refine seqD cap _ 1 (copy1 cap (K 4) (K 24) (K 14) (by simp) (by simp) (by simp) lb _ h4 (hz 24 (by simp))
    (hz 14 (by simp)) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (K 24) lb _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (K 6) (K 25) (K 14) (by simp) (by simp) (by simp) wl _ (by simp [h6])
    (by simp [hz]) (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dec1 cap (K 25) wl _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (K 11) 256 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mA.trans K) lb 256 0 _ (by simp [h4]) (by simp) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mB.trans K) (lb - 1) 256 (0 + lb * 256) _ (by simp) (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mA.trans K) lb 256 (0 + lb * 256 + (lb - 1) * 256) _ (by simp [h4]) (by simp)
    (by simp) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 11) 256 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (K 11) 512 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mF.trans K) fb 512 (0 + lb * 256 + (lb - 1) * 256 + lb * 256) _
    (by simp [h5]) (by simp) (by simp) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 11) 512 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (K 11) 160 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mW.trans K) (wl - 1) 160
    (0 + lb * 256 + (lb - 1) * 256 + lb * 256 + fb * 512) _ (by simp) (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 11) 160 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 24) (lb - 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (K 25) (wl - 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  have hS : 0 + lb * 256 + (lb - 1) * 256 + lb * 256 + fb * 512 + (wl - 1) * 160 = sb := by omega
  rw [hS]
  have hp := pow2W_spec cap (pS.trans K) (((((((((((((((((σ.setv (K 24) lb).setv (K 24) (lb - 1)).setv (K 25) wl).setv
    (K 25) (wl - 1)).setv (K 11) 256).setv (K 20) (0 + lb * 256)).setv (K 20) (0 + lb * 256 + (lb - 1) * 256)).setv
    (K 20) (0 + lb * 256 + (lb - 1) * 256 + lb * 256)).setv (K 11) 0).setv (K 11) 512).setv (K 20)
    (0 + lb * 256 + (lb - 1) * 256 + lb * 256 + fb * 512)).setv (K 11) 0).setv (K 11) 160).setv (K 20) sb).setv
    (K 11) 0).setv (K 24) 0).setv (K 25) 0) (by simp [hz]) (by simp [hz]) (by simp [hz]) (by simp; omega)
  simp only [Function.Embedding.trans_apply, pS_apply, Matrix.cons_val] at hp
  have hv20 : (((((((((((((((((σ.setv (K 24) lb).setv (K 24) (lb - 1)).setv (K 25) wl).setv
    (K 25) (wl - 1)).setv (K 11) 256).setv (K 20) (0 + lb * 256)).setv (K 20) (0 + lb * 256 + (lb - 1) * 256)).setv
    (K 20) (0 + lb * 256 + (lb - 1) * 256 + lb * 256)).setv (K 11) 0).setv (K 11) 512).setv (K 20)
    (0 + lb * 256 + (lb - 1) * 256 + lb * 256 + fb * 512)).setv (K 11) 0).setv (K 11) 160).setv (K 20) sb).setv
    (K 11) 0).setv (K 24) 0).setv (K 25) 0).val (K 20) = sb := by simp
  rw [hv20] at hp
  refine endD cap _ 1 hp ?_ (by
    have hlt : sb < 2 ^ sb := Nat.lt_two_pow_self
    have h2 : 2 ^ (sb + 1) = 2 * 2 ^ sb := by rw [pow_succ]; ring
    have hq : sb * (18 * 2 ^ sb + 7) ≤ cap * (18 * cap + 7) := Nat.mul_le_mul (by omega) (by omega)
    unfold UnaryPow.sq
    nlinarith) (by omega)
  clear hp hv20
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ## The filter's numbers -/

/-- **The regular filter's numbers** from `K 0 = U`, `K 1 = M`, `K 2 = errExp`. -/
def gapNumsW (K : Fin 32 ↪ Fin nr) : WM ns nr := .seq (filtA K) (.seq (gB K) (.seq (filtC K) (gS K)))

theorem seedBits_eq (P : Filters.GapParams) : P.seedBits = sbOf P.labelBits P.fieldBits P.walkLen := rfl

/-- **The filter's numbers, run**: `K 3 … K 6` = `prefixBits`, `labelBits`, `fieldBits`, `walkLen`, `K 20` = `seedBits`,
`K 21 = 2^{seedBits}`, every other register of the block unchanged (`K 7`, the scratch, back at `0`). -/
theorem gapNums_spec (K : Fin 32 ↪ Fin nr) (σ : WState ns nr) (P : Filters.GapParams) (hB0 : σ.val (K 0) = P.cap)
    (hM0 : σ.val (K 1) = P.len) (hE0 : σ.val (K 2) = P.errExp) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0)
    (hB1 : 1 ≤ P.cap) (hM2 : 2 ≤ P.len) (hc1 : 1 ≤ cap) (hBc : P.cap * 32 + 2 ≤ cap) (hMc : P.len + 8 ≤ cap)
    (hEc : P.errExp + 4 ≤ cap) (hsc : 2 ^ (P.seedBits + 1) ≤ cap)
    (hlc : P.labelBits + P.fieldBits + P.walkLen + 512 ≤ cap) :
    WExec cap (gapNumsW K) σ ((((((σ.setv (K 3) P.prefixBits).setv (K 4) P.labelBits).setv (K 5) P.fieldBits).setv
      (K 6) P.walkLen).setv (K 20) P.seedBits).setv (K 21) (2 ^ P.seedBits)) (110 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨PB, hPB⟩ : ∃ v, v = Nat.clog 2 (32 * P.cap) := ⟨_, rfl⟩
  obtain ⟨CL, hCL⟩ : ∃ v, v = Nat.clog 2 P.len := ⟨_, rfl⟩
  have ePB : P.prefixBits = PB := hPB.symm
  have eLB : P.labelBits = max PB CL := by rw [hPB, hCL]; rfl
  have eFB : P.fieldBits = CL + 4 := by rw [hCL]; rfl
  have eWL : P.walkLen = 2 * (P.errExp / 4) + 1 := rfl
  have hPc : PB ≤ cap := by
    have : P.prefixBits ≤ P.labelBits := le_max_left _ _
    rw [← ePB]; omega
  have hPB1 : 1 ≤ PB := by rw [hPB]; exact Nat.clog_pos (by norm_num) (by omega)
  have hmx : 1 ≤ max PB CL := le_trans hPB1 (le_max_left _ _)
  have hCc : CL ≤ cap := by rw [eFB] at hlc; omega
  have hA := filtA_spec cap K σ P.cap hB0 hz hB1 hBc
  rw [← hPB] at hA
  have hB := gB_run cap K (σ.setv (K 3) PB) P.len PB (by simp [hM0]) hM2 (by simp)
    (fun i hi => by
      have hi3 : i ≠ 3 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hi3, hz i (by omega)]) hc1 hMc hPc
  rw [← hCL] at hB
  have hC := filtC_spec cap K ((((σ.setv (K 3) PB).setv (K 7) CL).setv (K 5) (CL + 4)).setv (K 4) (max PB CL))
    P.errExp CL (by simp [hE0]) (by simp) (by simp [hz]) (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hn3, hn7, hn5, hn4, hz i (by omega)]) hc1 hEc hCc
  have hS := gS_run cap K (((((((σ.setv (K 3) PB).setv (K 7) CL).setv (K 5) (CL + 4)).setv (K 4) (max PB CL)).setv
      (K 6) (2 * (P.errExp / 4) + 1)).setv (K 7) 0)) (max PB CL) (CL + 4) (2 * (P.errExp / 4) + 1)
    (by simp) (by simp) (by simp) hmx (by omega)
    (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      have hn6 : i ≠ 6 := by intro h; subst h; simp at hi
      rcases hi with hi | hi
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)]
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)])
    hc1 (by rw [← eLB, ← eFB, ← eWL, ← seedBits_eq]; exact hsc) (by rw [← eLB, ← eFB, ← eWL]; exact hlc)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB (WExec.seq hC hS))) ?_ (by omega)
  rw [ePB, eLB, eFB, eWL, seedBits_eq, eLB, eFB, eWL]
  clear hA hB hC hS hB0 hM0 hE0 hB1 hc1 hBc hMc hEc hPc hCc hsq hPB hCL hsc hlc hM2 ePB eLB eFB eWL
  have hb0 := setv_base K σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

end NearCubicWires.WireExponent3_5.PrimAsm.GapNums
