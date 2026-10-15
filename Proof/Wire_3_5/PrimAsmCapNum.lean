import Proof.Wire_3_5.PrimAsmSparseNum
import Proof.Wire_3_5.PrimAsmCodec
import Proof.Wire_3_5.LedgerCap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

variable {ns nr : ℕ} (cap : ℕ)

/-- The constant factor of the main term's 32nd power: `2^80·a_m^{32}·β⁻³²`. -/
def cMain (C : Ledger.CapParams) (m : Mode) : ℕ := 2 ^ 80 * C.coef m ^ 32 * C.betaInv ^ 32

/-- The constant factor of the encoding term's square: `32·C_par²·β⁻²`. -/
def cEnc (C : Ledger.CapParams) : ℕ := 32 * C.Cpar ^ 2 * C.betaInv ^ 2

def e48 : Fin 5 ↪ Fin 32 := ⟨![1, 5, 16, 17, 18], by decide⟩
def e32 : Fin 5 ↪ Fin 32 := ⟨![2, 6, 16, 17, 18], by decide⟩
def e64 : Fin 5 ↪ Fin 32 := ⟨![0, 7, 16, 17, 18], by decide⟩
def m56 : Fin 5 ↪ Fin 32 := ⟨![5, 6, 15, 16, 17], by decide⟩
def m57 : Fin 5 ↪ Fin 32 := ⟨![5, 7, 15, 16, 17], by decide⟩
def m514 : Fin 5 ↪ Fin 32 := ⟨![5, 14, 15, 16, 17], by decide⟩
def eK : Fin 5 ↪ Fin 32 := ⟨![3, 8, 16, 17, 18], by decide⟩
def cdK : Fin 12 ↪ Fin 32 := ⟨![5, 8, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23], by decide⟩
def rt1 : Fin 7 ↪ Fin 32 := ⟨![9, 10, 15, 19, 16, 17, 18], by decide⟩
def e3 : Fin 5 ↪ Fin 32 := ⟨![1, 11, 16, 17, 18], by decide⟩
def m110 : Fin 5 ↪ Fin 32 := ⟨![11, 0, 15, 16, 17], by decide⟩
def m1114 : Fin 5 ↪ Fin 32 := ⟨![11, 14, 15, 16, 17], by decide⟩
def rt2 : Fin 7 ↪ Fin 32 := ⟨![11, 12, 15, 19, 16, 17, 18], by decide⟩

@[simp] theorem e48_apply (i : Fin 5) : e48 i = ![1, 5, 16, 17, 18] i := rfl
@[simp] theorem e32_apply (i : Fin 5) : e32 i = ![2, 6, 16, 17, 18] i := rfl
@[simp] theorem e64_apply (i : Fin 5) : e64 i = ![0, 7, 16, 17, 18] i := rfl
@[simp] theorem m56_apply (i : Fin 5) : m56 i = ![5, 6, 15, 16, 17] i := rfl
@[simp] theorem m57_apply (i : Fin 5) : m57 i = ![5, 7, 15, 16, 17] i := rfl
@[simp] theorem m514_apply (i : Fin 5) : m514 i = ![5, 14, 15, 16, 17] i := rfl
@[simp] theorem eK_apply (i : Fin 5) : eK i = ![3, 8, 16, 17, 18] i := rfl
@[simp] theorem cdK_apply (i : Fin 12) : cdK i = ![5, 8, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23] i := rfl
@[simp] theorem rt1_apply (i : Fin 7) : rt1 i = ![9, 10, 15, 19, 16, 17, 18] i := rfl
@[simp] theorem e3_apply (i : Fin 5) : e3 i = ![1, 11, 16, 17, 18] i := rfl
@[simp] theorem m110_apply (i : Fin 5) : m110 i = ![11, 0, 15, 16, 17] i := rfl
@[simp] theorem m1114_apply (i : Fin 5) : m1114 i = ![11, 14, 15, 16, 17] i := rfl
@[simp] theorem rt2_apply (i : Fin 7) : rt2 i = ![11, 12, 15, 19, 16, 17, 18] i := rfl

/-- The mode-dependent constant, by the mode flag. -/
def cMainW (C : Ledger.CapParams) (H : Fin 32 ↪ Fin nr) : WM ns nr :=
  .ifr (H 4) (StarNums.incN (H 14) (cMain C .thr)) (StarNums.incN (H 14) (cMain C .sym))

/-- `L^{K_m}` (`K_THR = 174`, `K_SYM = 142`), by the mode flag. -/
def powKW (H : Fin 32 ↪ Fin nr) : WM ns nr :=
  .ifr (H 4) (UnaryPow.powConstW (eK.trans H) 174) (UnaryPow.powConstW (eK.trans H) 142)

/-- **The cap**: `H 13 := B_m(q)` from `q, r, s, L` and the mode flag. -/
def capM (C : Ledger.CapParams) (H : Fin 32 ↪ Fin nr) : WM ns nr :=
  .seq (UnaryPow.powConstW (e48.trans H) 48) (.seq (UnaryPow.powConstW (e32.trans H) 32)
  (.seq (UnaryPow.powConstW (e64.trans H) 64) (.seq (mulByW (m56.trans H)) (.seq (mulByW (m57.trans H))
  (.seq (cMainW C H) (.seq (mulByW (m514.trans H)) (.seq (WM.clear (H 14)) (.seq (powKW H)
  (.seq (UnaryPow.ceilDivW (cdK.trans H)) (.seq (UnaryPow.ceilRootW 31 (rt1.trans H))
  (.seq (UnaryPow.powConstW (e3.trans H) 3) (.seq (mulByW (m110.trans H))
  (.seq (StarNums.incN (H 14) (cEnc C)) (.seq (mulByW (m1114.trans H)) (.seq (WM.clear (H 14))
  (.seq (UnaryPow.ceilRootW 1 (rt2.trans H)) (.seq (.inc (H 13)) (.seq (addTo (H 10) (H 13) (H 16))
  (.seq (addTo (H 12) (H 13) (H 16))
  (.seq (WM.clear (H 5)) (.seq (WM.clear (H 6)) (.seq (WM.clear (H 7)) (.seq (WM.clear (H 8))
  (.seq (WM.clear (H 9)) (.seq (WM.clear (H 10)) (.seq (WM.clear (H 11)) (WM.clear (H 12))))))))))))))))))))))))))))

/-! ## Specs with the values named -/

theorem flag_thr {σ : WState ns nr} {f : Fin nr} {m : Mode} (hm : decide (σ.val f ≠ 0) = Codec.modeBit m)
    (h : m = .thr) : σ.val f ≠ 0 := by
  subst h; simpa [Codec.modeBit] using hm

theorem flag_sym {σ : WState ns nr} {f : Fin nr} {m : Mode} (hm : decide (σ.val f ≠ 0) = Codec.modeBit m)
    (h : m = .sym) : σ.val f = 0 := by
  subst h; simpa [Codec.modeBit] using hm

theorem cMainW_spec (C : Ledger.CapParams) (H : Fin 32 ↪ Fin nr) (m : Mode) (σ : WState ns nr)
    (hm : decide (σ.val (H 4) ≠ 0) = Codec.modeBit m) (h14 : σ.val (H 14) = 0) (hc : cMain C m ≤ cap) :
    WExec cap (cMainW C H) σ (σ.setv (H 14) (cMain C m)) (2 * UnaryPow.sq cap) := by
  have hs := UnaryPow.sq_ge cap
  cases m with
  | thr => exact WExec.mono (WExec.ifrT (flag_thr hm rfl) (incN0 cap (H 14) _ σ h14 hc)) (by omega)
  | sym => exact WExec.mono (WExec.ifrF (flag_sym hm rfl) (incN0 cap (H 14) _ σ h14 hc)) (by omega)

theorem powKW_spec (H : Fin 32 ↪ Fin nr) (m : Mode) (σ : WState ns nr) (L : ℕ)
    (hm : decide (σ.val (H 4) ≠ 0) = Codec.modeBit m) (hL : σ.val (H 3) = L) (h8 : σ.val (H 8) = 0)
    (h16 : σ.val (H 16) = 0) (h17 : σ.val (H 17) = 0) (h18 : σ.val (H 18) = 0) (hc1 : 1 ≤ cap) (hL1 : L ≤ cap)
    (hLK : L ^ Ledger.capExp32 m ≤ cap) :
    WExec cap (powKW H) σ (σ.setv (H 8) (L ^ Ledger.capExp32 m)) (701 * UnaryPow.sq cap) := by
  have hs := UnaryPow.sq_ge cap
  cases m with
  | thr =>
    exact WExec.mono (WExec.ifrT (flag_thr hm rfl) (pow1 cap (eK.trans H) L 174 σ (by simpa using hL)
      (by simpa using h8) (by simpa using h16) (by simpa using h17) (by simpa using h18) hc1 hL1 hLK)) (by omega)
  | sym =>
    exact WExec.mono (WExec.ifrF (flag_sym hm rfl) (pow1 cap (eK.trans H) L 142 σ (by simpa using hL)
      (by simpa using h8) (by simpa using h16) (by simpa using h17) (by simpa using h18) hc1 hL1 hLK)) (by omega)

theorem root1 (R : Fin 7 ↪ Fin nr) (j x : ℕ) (σ : WState ns nr) (hx : σ.val (R 0) = x)
    (hz : ∀ i : Fin 7, 1 ≤ i.val → σ.val (R i) = 0) (hcap : 2 ^ (j + 1) * x + 1 ≤ cap) :
    WExec cap (UnaryPow.ceilRootW j R) σ (σ.setv (R 1) (Ledger.ceilRoot j x))
      ((cap + 2) * (4 * (j + 6)) * UnaryPow.sq cap) := by
  have h := UnaryPow.ceilRootW_spec cap j R σ hz (by rw [hx]; exact hcap)
  rw [hx] at h
  refine WExec.mono h ?_
  have hp : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have hxc : x ≤ cap := by nlinarith
  have := Nat.mul_le_mul_right ((j + 6) * (4 * UnaryPow.sq cap)) (show x + 2 ≤ cap + 2 by omega)
  nlinarith

theorem add1 (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (a b : ℕ) (σ : WState ns nr)
    (ha : σ.val p = a) (hb : σ.val v = b) (ht : σ.val t = 0) (hac : a ≤ cap) (hc : b + a ≤ cap) :
    WExec cap (addTo p v t) σ (σ.setv v (b + a)) (UnaryPow.sq cap) := by
  have h := addTo_spec cap p v t hpv hpt hvt σ ht (by rw [ha]; exact hac) (by rw [ha, hb]; exact hc)
  rw [ha, hb] at h
  have hs := UnaryPow.lin_le_sq cap
  exact WExec.mono h (by omega)

/-! ## The cap -/

theorem capM_run (C : Ledger.CapParams) (m : Mode) (H : Fin 32 ↪ Fin nr) (σ : WState ns nr) (q r s L : ℕ)
    (hq0 : σ.val (H 0) = q) (hr0 : σ.val (H 1) = r) (hs0 : σ.val (H 2) = s) (hL0 : σ.val (H 3) = L)
    (hm : decide (σ.val (H 4) ≠ 0) = Codec.modeBit m) (hz : ∀ i : Fin 32, 5 ≤ i.val → σ.val (H i) = 0)
    (hc1 : 1 ≤ cap) (hr : r ≤ cap) (hs : s ≤ cap) (hq : q ≤ cap) (hL1 : L ≤ cap)
    (h48 : r ^ 48 ≤ cap) (h32 : s ^ 32 ≤ cap) (h64 : q ^ 64 ≤ cap) (h4832 : r ^ 48 * s ^ 32 ≤ cap)
    (hrsq : r ^ 48 * s ^ 32 * q ^ 64 ≤ cap) (hC : cMain C m ≤ cap)
    (hnum : r ^ 48 * s ^ 32 * q ^ 64 * cMain C m ≤ cap) (hLK : L ^ Ledger.capExp32 m ≤ cap)
    (hLKp : 1 ≤ L ^ Ledger.capExp32 m)
    (hsum : r ^ 48 * s ^ 32 * q ^ 64 * cMain C m + L ^ Ledger.capExp32 m ≤ cap)
    (hroot1 : 2 ^ 32 * ((r ^ 48 * s ^ 32 * q ^ 64 * cMain C m + L ^ Ledger.capExp32 m - 1) /
      L ^ Ledger.capExp32 m) + 1 ≤ cap)
    (h3 : r ^ 3 ≤ cap) (h3q : r ^ 3 * q ≤ cap) (hCe : cEnc C ≤ cap) (hE : r ^ 3 * q * cEnc C ≤ cap)
    (hroot2 : 2 ^ 2 * (r ^ 3 * q * cEnc C) + 1 ≤ cap) :
    WExec cap (capM C H) σ (σ.setv (H 13) (1 + Ledger.ceilRoot 31
      ((r ^ 48 * s ^ 32 * q ^ 64 * cMain C m + L ^ Ledger.capExp32 m - 1) / L ^ Ledger.capExp32 m) +
      Ledger.ceilRoot 1 (r ^ 3 * q * cEnc C)))
      (((cap + 2) * 200 + 1500) * UnaryPow.sq cap) := by
  set num := r ^ 48 * s ^ 32 * q ^ 64 * cMain C m with hnumd
  set LK := L ^ Ledger.capExp32 m with hLKd
  set MP := (num + LK - 1) / LK with hMPd
  set E := r ^ 3 * q * cEnc C with hEd
  set B1 := Ledger.ceilRoot 31 MP with hB1d
  set B2 := Ledger.ceilRoot 1 E with hB2d
  have hMPle : MP ≤ num + LK - 1 := Nat.div_le_self _ _
  have hB1 : B1 ≤ MP := Ledger.ceilRoot_le_self 31 MP
  have hB2 : B2 ≤ E := Ledger.ceilRoot_le_self 1 E
  have hMPc : MP ≤ cap := by omega
  have hB12 : 1 + B1 + B2 ≤ cap := by omega
  have hs8 := UnaryPow.sq_ge cap
  unfold capM
  refine seqD cap _ 196 (pow1 cap (e48.trans H) r 48 σ (by simp [hr0]) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hr h48) (by omega) (by omega) ?_
  refine seqD cap _ 132 (pow1 cap (e32.trans H) s 32 _ (by simp [hs0]) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hs h32) (by omega) (by omega) ?_
  refine seqD cap _ 260 (pow1 cap (e64.trans H) q 64 _ (by simp [hq0]) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hq h64) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m56.trans H) (r ^ 48) (s ^ 32) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) h4832 h48 h32) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m57.trans H) (r ^ 48 * s ^ 32) (q ^ 64) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hrsq h4832 h64) (by omega) (by omega) ?_
  refine seqD cap _ 2 (cMainW_spec cap C H m _ (by simpa using hm) (by simp [hz]) hC) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m514.trans H) (r ^ 48 * s ^ 32 * q ^ 64) (cMain C m) _ (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by simp [hz]) hnum hrsq hC) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 14) (cMain C m) _ (by simp) hC) (by omega) (by omega) ?_
  refine seqD cap _ 701 (powKW_spec cap H m _ L (by simpa using hm) (by simp [hL0]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hc1 hL1 hLK) (by omega) (by omega) ?_
  refine seqD cap _ 5 (ceilDiv1 cap (cdK.trans H) num LK _ (by simp [hnumd]) (by simp [hLKd])
    (by intro i hi; fin_cases i <;> simp at hi <;> simp [hz]) hLKp hsum) (by omega) (by omega) ?_
  refine seqD cap _ ((cap + 2) * (4 * (31 + 6))) (root1 cap (rt1.trans H) 31 MP _ (by simp [hMPd])
    (by intro i hi; fin_cases i <;> simp at hi <;> simp [hz]) hroot1) le_rfl (by omega) ?_
  refine seqD cap _ 16 (pow1 cap (e3.trans H) r 3 _ (by simp [hr0]) (by simp [hz]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc1 hr h3) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m110.trans H) (r ^ 3) q _ (by simp) (by simp [hq0]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) h3q h3 hq) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (H 14) (cEnc C) _ (by simp [hz]) hCe) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (m1114.trans H) (r ^ 3 * q) (cEnc C) _ (by simp) (by simp) (by simp [hz])
    (by simp [hz]) (by simp [hz]) hE h3q hCe) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 14) (cEnc C) _ (by simp) hCe) (by omega) (by omega) ?_
  refine seqD cap _ ((cap + 2) * (4 * (1 + 6))) (root1 cap (rt2.trans H) 1 E _ (by simp [hEd])
    (by intro i hi; fin_cases i <;> simp at hi <;> simp [hz]) hroot2) le_rfl (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (H 13) 0 _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (H 10) (H 13) (H 16) (by simp) (by simp) (by simp) B1 (0 + 1) _ (by simp [hB1d])
    (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (add1 cap (H 12) (H 13) (H 16) (by simp) (by simp) (by simp) B2 (0 + 1 + B1) _
    (by simp [hB2d]) (by simp) (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 5) num _ (by simp [hnumd]) hnum) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 6) (s ^ 32) _ (by simp) h32) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 7) (q ^ 64) _ (by simp) h64) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 8) LK _ (by simp [hLKd]) hLK) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 9) MP _ (by simp [hMPd]) hMPc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 10) B1 _ (by simp [hB1d]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (H 11) E _ (by simp [hEd]) hE) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (H 12) B2 _ (by simp [hB2d]) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, e48_apply, e32_apply, e64_apply, m56_apply, m57_apply, m514_apply,
    eK_apply, cdK_apply, rt1_apply, e3_apply, m110_apply, m1114_apply, rt2_apply, Matrix.cons_val]
  clear hq0 hr0 hs0 hL0 hm hc1 hr hs hq hL1 h48 h32 h64 h4832 hrsq hC hnum hLK hLKp hsum hroot1 h3 h3q hCe hE hroot2
    hMPle hB1 hB2 hMPc hB12 hs8
  have hb0 := setv_base H σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz, hB1d, hB2d, hMPd] <;> ring

theorem num_eq (C : Ledger.CapParams) (m : Mode) (r s q : ℕ) :
    r ^ 48 * s ^ 32 * q ^ 64 * cMain C m = Ledger.capMainNum C m r s q := by
  unfold cMain Ledger.capMainNum; ring

theorem enc_eq (C : Ledger.CapParams) (r q : ℕ) : r ^ 3 * q * cEnc C = Ledger.capEncPow C r q := by
  unfold cEnc Ledger.capEncPow; ring

/-- **The cap `B_m(q)` of `tr:B`** (`Ledger.rowBCap`), from `q`, `r`, `s`, `L = L(q)` and the mode flag. -/
theorem capM_spec (C : Ledger.CapParams) (m : Mode) (H : Fin 32 ↪ Fin nr) (σ : WState ns nr) (q r s : ℕ)
    (hq0 : σ.val (H 0) = q) (hr0 : σ.val (H 1) = r) (hs0 : σ.val (H 2) = s) (hL0 : σ.val (H 3) = Ledger.Lq q)
    (hm : decide (σ.val (H 4) ≠ 0) = Codec.modeBit m) (hz : ∀ i : Fin 32, 5 ≤ i.val → σ.val (H i) = 0)
    (hc1 : 1 ≤ cap) (hr : r ≤ cap) (hs : s ≤ cap) (hq : q ≤ cap) (hL1 : Ledger.Lq q ≤ cap)
    (h48 : r ^ 48 ≤ cap) (h32 : s ^ 32 ≤ cap) (h64 : q ^ 64 ≤ cap) (h4832 : r ^ 48 * s ^ 32 ≤ cap)
    (hrsq : r ^ 48 * s ^ 32 * q ^ 64 ≤ cap) (hC : cMain C m ≤ cap)
    (hnum : Ledger.capMainNum C m r s q ≤ cap) (hLK : Ledger.Lq q ^ Ledger.capExp32 m ≤ cap)
    (hsum : Ledger.capMainNum C m r s q + Ledger.Lq q ^ Ledger.capExp32 m ≤ cap)
    (hroot1 : 2 ^ 32 * Ledger.capMainPow C m r s q + 1 ≤ cap)
    (h3 : r ^ 3 ≤ cap) (h3q : r ^ 3 * q ≤ cap) (hCe : cEnc C ≤ cap) (hE : Ledger.capEncPow C r q ≤ cap)
    (hroot2 : 2 ^ 2 * Ledger.capEncPow C r q + 1 ≤ cap) :
    WExec cap (capM C H) σ (σ.setv (H 13) (Ledger.rowBCap C m r s q))
      (((cap + 2) * 200 + 1500) * UnaryPow.sq cap) := by
  have hLKp : 1 ≤ Ledger.Lq q ^ Ledger.capExp32 m := Nat.one_le_pow _ _ (Ledger.Lq_pos q)
  rw [← num_eq] at hnum hsum
  rw [← enc_eq] at hE hroot2
  have hroot1' : 2 ^ 32 * ((r ^ 48 * s ^ 32 * q ^ 64 * cMain C m + Ledger.Lq q ^ Ledger.capExp32 m - 1) /
      Ledger.Lq q ^ Ledger.capExp32 m) + 1 ≤ cap := by
    unfold Ledger.capMainPow at hroot1; rw [← num_eq] at hroot1; exact hroot1
  have h := capM_run cap C m H σ q r s (Ledger.Lq q) hq0 hr0 hs0 hL0 hm hz hc1 hr hs hq hL1 h48 h32 h64 h4832 hrsq hC
    hnum hLK hLKp hsum hroot1' h3 h3q hCe hE hroot2
  refine WExec.cast cap h ?_ le_rfl
  unfold Ledger.rowBCap Ledger.capMainPow
  rw [num_eq, enc_eq]

end NearCubicWires.WireExponent3_5.PrimAsm.CapNum
