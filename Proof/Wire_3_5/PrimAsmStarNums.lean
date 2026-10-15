import Proof.Wire_3_5.PrimAsmUnaryArith
import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Wire_3_5.LedgerLoad
import Proof.Wire_3_5.Shared.S0

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.StarNums
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith

/-- `⌈log₂(n+2)⌉ = ⌊log₂(n+1)⌋ + 1`, the bit length of `n + 1`. -/
theorem clog_two_add_two (n : ℕ) : Nat.clog 2 (n + 2) = natBitLength (n + 1) := by
  unfold natBitLength
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 1)
    omega
  · have h1 : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
    have h2 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) _
    have h3 : 2 ^ Nat.log 2 (n + 1) < 2 ^ Nat.clog 2 (n + 2) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
    omega

theorem log_eq_natBitLength_sub (m : ℕ) : Nat.log 2 m = natBitLength m - 1 := by
  unfold natBitLength; omega

variable {ns nr : ℕ} (cap : ℕ)

/-- `r += c` for a constant `c`. -/
def incN (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | c + 1 => .seq (incN r c) (.inc r)

theorem incN_spec (r : Fin nr) : ∀ (c : ℕ) (σ : WState ns nr), σ.val r + c ≤ cap →
    WExec cap (incN r c) σ (σ.setv r (σ.val r + c)) (4 * c)
  | 0, σ, _ => by
    rw [Nat.add_zero, wsetv_same]
    exact WExec.skip σ
  | c + 1, σ, hc => by
    have h1 := incN_spec r c σ (by omega)
    have h2 := WExec.inc (cap := cap) r (σ.setv r (σ.val r + c)) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    simp only [wsetv_setv, WState.setv_val, Function.update_self]
    rw [Nat.add_assoc]

/-! ## Phase A: `L` and `r` -/

/-- The bit-length register maps of phase A: `L := natBitLength (n+1)` into `S 1`, then `natBitLength L` into `S 2`. -/
def eA1 : Fin 8 ↪ Fin 20 := ⟨![11, 12, 13, 14, 1, 15, 16, 17], by decide⟩
def eA2 : Fin 8 ↪ Fin 20 := ⟨![1, 12, 13, 14, 2, 15, 16, 17], by decide⟩

@[simp] theorem eA1_apply (i : Fin 8) : eA1 i = ![11, 12, 13, 14, 1, 15, 16, 17] i := rfl
@[simp] theorem eA2_apply (i : Fin 8) : eA2 i = ![1, 12, 13, 14, 2, 15, 16, 17] i := rfl

/-- **Phase A1**: `S 1 := natBitLength (n+1)` from `S 0 = n` (through `S 11`, `S 12` and the bit-length scratch). -/
def phaseA1 (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 11) (S 12)) (.seq (.inc (S 11)) (.seq (bitLenM (eA1.trans S))
    (WM.clear (S 11))))

theorem phaseA1_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hz : ∀ i : Fin 20, i ≠ 0 → σ.val (S i) = 0) (hcap : σ.val (S 0) + 4 ≤ cap) :
    WExec cap (phaseA1 S) σ (σ.setv (S 1) (natBitLength (σ.val (S 0) + 1))) (90 * σ.val (S 0) + 200) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  set n := σ.val (S 0) with hn
  have h1 := FinalPass.Hash4.wcopyR_spec cap (S 0) (S 11) (S 12) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (hz 11 (by decide)) (hz 12 (by decide)) (by omega)
  have h2 := WExec.inc (cap := cap) (S 11) (σ.setv (S 11) n) (by simp; omega)
  set σ2 := (σ.setv (S 11) n).setv (S 11) ((σ.setv (S 11) n).val (S 11) + 1) with hσ2
  have hσ2v : ∀ i : Fin 20, i ≠ 11 → σ2.val (S i) = σ.val (S i) := by
    intro i hi; simp [σ2, Function.update_apply, hne hi]
  have hσ211 : σ2.val (S 11) = n + 1 := by simp [σ2]
  have h3 := bitLenM_spec cap (eA1.trans S) σ2
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ2v 12 (by decide), hz 12 (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ2v 13 (by decide), hz 13 (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ2v 14 (by decide), hz 14 (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ2v 1 (by decide), hz 1 (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ2v 16 (by decide), hz 16 (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA1_apply]; simp [hσ211]; omega)
  simp only [Function.Embedding.trans_apply, eA1_apply] at h3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_four, hσ211] at h3
  have hσ311 : (σ2.setv (S 1) (natBitLength (n + 1))).val (S 11) = n + 1 := by
    simp [Function.update_apply, hne (show (11 : Fin 20) ≠ 1 by decide), hσ211]
  have h4 := wclear_spec cap (S 11) (n + 1) _ hσ311 (by rw [hσ311]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h11 : j = S 11
  · subst h11; simp [Function.update_apply, hne (show (11 : Fin 20) ≠ 1 by decide), hz 11 (by decide)]
  · by_cases h1 : j = S 1
    · subst h1; simp [Function.update_apply, h11]
    · simp [σ2, Function.update_apply, h11, h1]

/-- **Phase A2**: `S 3 := 2(⌊log₂ L⌋ + c_r)` from `S 1 = L` (through `S 2`, `S 12` and the bit-length scratch). -/
def phaseA2 (cr : ℕ) (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (bitLenM (eA2.trans S)) (.seq (.dec (S 2)) (.seq (FinalPass.Hash4.wcopyR (S 2) (S 3) (S 12))
    (.seq (incN (S 3) cr) (.seq (dbl (S 3) (S 12)) (WM.clear (S 2))))))

theorem phaseA2_spec (cr : ℕ) (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hz : ∀ i : Fin 20, i ≠ 0 → i ≠ 1 → σ.val (S i) = 0) (hcap : 2 * σ.val (S 1) + 2 * cr + 8 ≤ cap) :
    WExec cap (phaseA2 cr S) σ (σ.setv (S 3) (2 * (Nat.log 2 (σ.val (S 1)) + cr)))
      (100 * σ.val (S 1) + 30 * cr + 200) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  set L := σ.val (S 1) with hL
  have hlogL : Nat.log 2 L ≤ L := Nat.log_le_self 2 L
  have hLL : natBitLength L - 1 = Nat.log 2 L := (log_eq_natBitLength_sub L).symm
  have hbl := CopyNat.natBitLength_le_self_succ L
  have h5 := bitLenM_spec cap (eA2.trans S) σ
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp [hz 12 (by decide) (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp [hz 13 (by decide) (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp [hz 14 (by decide) (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp [hz 2 (by decide) (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp [hz 16 (by decide) (by decide)])
    (by simp only [Function.Embedding.trans_apply, eA2_apply]; simp; omega)
  simp only [Function.Embedding.trans_apply, eA2_apply] at h5
  simp only [Matrix.cons_val_zero, Matrix.cons_val_four] at h5
  have h6 := WExec.dec (cap := cap) (S 2) (σ.setv (S 2) (natBitLength L)) (by simp; omega)
  have e6 : (σ.setv (S 2) (natBitLength L)).setv (S 2) ((σ.setv (S 2) (natBitLength L)).val (S 2) - 1) =
      σ.setv (S 2) (Nat.log 2 L) := by simp [wsetv_setv, hLL]
  rw [e6] at h6
  have h7 := FinalPass.Hash4.wcopyR_spec cap (S 2) (S 3) (S 12) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (S 2) (Nat.log 2 L))
    (by simp [Function.update_apply, hne (show (3 : Fin 20) ≠ 2 by decide), hz 3 (by decide) (by decide)])
    (by simp [Function.update_apply, hne (show (12 : Fin 20) ≠ 2 by decide), hz 12 (by decide) (by decide)])
    (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at h7
  have h8 := incN_spec cap (S 3) cr ((σ.setv (S 2) (Nat.log 2 L)).setv (S 3) (Nat.log 2 L)) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at h8
  have h9 := dbl_spec cap (S 3) (S 12) (hne (by decide)) ((σ.setv (S 2) (Nat.log 2 L)).setv (S 3) (Nat.log 2 L + cr))
    (by simp [Function.update_apply, hne (show (12 : Fin 20) ≠ 3 by decide), hne (show (12 : Fin 20) ≠ 2 by decide),
      hz 12 (by decide) (by decide)])
    (by simp; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at h9
  have hv2 : ((σ.setv (S 2) (Nat.log 2 L)).setv (S 3) (2 * (Nat.log 2 L + cr))).val (S 2) = Nat.log 2 L := by
    simp [Function.update_apply, hne (show (2 : Fin 20) ≠ 3 by decide)]
  have h10 := wclear_spec cap (S 2) (Nat.log 2 L) _ hv2 (by rw [hv2]; omega)
  refine WExec.cast cap (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (WExec.seq h8 (WExec.seq h9 h10))))) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h2 : j = S 2
  · subst h2; simp [Function.update_apply, hne (show (2 : Fin 20) ≠ 3 by decide), hz 2 (by decide) (by decide)]
  · by_cases h3 : j = S 3
    · subst h3; simp [Function.update_apply, h2]
    · simp [Function.update_apply, h2, h3]

/-- **Phase A**: `S 1 := L = ⌈log₂(n+2)⌉`, `S 3 := r = rowBr c_r n` from `S 0 = n`. -/
def phaseA (cr : ℕ) (S : Fin 20 ↪ Fin nr) : WM ns nr := .seq (phaseA1 S) (phaseA2 cr S)

theorem phaseA_spec (cr : ℕ) (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hz : ∀ i : Fin 20, i ≠ 0 → σ.val (S i) = 0) (hcap : 4 * σ.val (S 0) + 2 * cr + 20 ≤ cap) :
    WExec cap (phaseA cr S) σ
      ((σ.setv (S 1) (Nat.clog 2 (σ.val (S 0) + 2))).setv (S 3) (Ledger.rowBr cr (σ.val (S 0))))
      (200 * σ.val (S 0) + 30 * cr + 800) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  have hbl := CopyNat.natBitLength_le_self_succ (σ.val (S 0) + 1)
  have h1 := phaseA1_spec cap S σ hz (by omega)
  have h2 := phaseA2_spec cap cr S (σ.setv (S 1) (natBitLength (σ.val (S 0) + 1)))
    (fun i h0 h1 => by simp [Function.update_apply, hne h1, hz i h0]) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  unfold Ledger.rowBr Ledger.Lq
  rw [clog_two_add_two]

/-! ## Register reads and the scratch block `S 11 … S 19` -/

theorem val_setvS (S : Fin 20 ↪ Fin nr) (σ : WState ns nr) (i j : Fin 20) (x : ℕ) :
    (σ.setv (S i) x).val (S j) = if j = i then x else σ.val (S j) := by
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_apply, h]

theorem scratch_ne {i : Fin 20} (hi : 11 ≤ i.val) {j : Fin 20} (hj : j.val < 11) : i ≠ j := by
  rintro rfl; omega

theorem scratch_setv (S : Fin 20 ↪ Fin nr) (σ : WState ns nr) (j : Fin 20) (hj : j.val < 11) (x : ℕ)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) : ∀ i : Fin 20, 11 ≤ i.val → (σ.setv (S j) x).val (S i) = 0 := by
  intro i hi; rw [val_setvS, if_neg (scratch_ne hi hj)]; exact hs i hi

/-! ## Phase B: `s = ⌊log₂(n/r+1)⌋` -/

/-- Division registers of phase B: `S 11 ÷ S 3`, the quotient into `S 2`. -/
def eB : Fin 9 ↪ Fin 20 := ⟨![11, 3, 2, 12, 13, 14, 15, 16, 17], by decide⟩
/-- Bit-length registers of phase B: `natBitLength (S 2)` into `S 4`. -/
def eB2 : Fin 8 ↪ Fin 20 := ⟨![2, 12, 13, 14, 4, 15, 16, 17], by decide⟩

/-- **Phase B1**: `S 2 := n / r` from `S 0 = n`, `S 3 = r` (the remainder discarded). -/
def phaseB1 (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 11) (S 12)) (.seq (divW (eB.trans S)) (WM.clear (S 11)))

theorem phaseB1_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h2 : σ.val (S 2) = 0)
    (hr : 1 ≤ σ.val (S 3)) (hrn : σ.val (S 3) ≤ σ.val (S 0)) (hcap : σ.val (S 0) + 2 ≤ cap) :
    WExec cap (phaseB1 S) σ (σ.setv (S 2) (σ.val (S 0) / σ.val (S 3)))
      ((σ.val (S 0) + 2) * (180 * σ.val (S 0) + 60) + 21 * σ.val (S 0) + 10) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  set n := σ.val (S 0) with hn
  set r := σ.val (S 3) with hr'
  have h1 := FinalPass.Hash4.wcopyR_spec cap (S 0) (S 11) (S 12) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (hs 11 (by decide)) (hs 12 (by decide)) (by omega)
  set σ1 := σ.setv (S 11) n with hσ1
  have hv1 : ∀ i : Fin 20, i ≠ 11 → σ1.val (S i) = σ.val (S i) := by
    intro i hi; simp [σ1, Function.update_apply, hne hi]
  have hv11 : σ1.val (S 11) = n := by simp [σ1]
  have e0 : (eB.trans S) 0 = S 11 := rfl
  have e1 : (eB.trans S) 1 = S 3 := rfl
  have e2 : (eB.trans S) 2 = S 2 := rfl
  have e3 : (eB.trans S) 3 = S 12 := rfl
  have e4 : (eB.trans S) 4 = S 13 := rfl
  have e5 : (eB.trans S) 5 = S 14 := rfl
  have e6 : (eB.trans S) 6 = S 15 := rfl
  have e7 : (eB.trans S) 7 = S 16 := rfl
  have h3v : σ1.val (S 3) = r := hv1 3 (by decide)
  have h2v : σ1.val (S 2) = 0 := by rw [hv1 2 (by decide), h2]
  have hdiv := divW_spec cap (eB.trans S) σ1 (by rw [e1, h3v]; exact hr)
    (by rw [e3, hv1 12 (by decide), hs 12 (by decide)]) (by rw [e4, hv1 13 (by decide), hs 13 (by decide)])
    (by rw [e5, hv1 14 (by decide), hs 14 (by decide)]) (by rw [e6, hv1 15 (by decide), hs 15 (by decide)])
    (by rw [e7, hv1 16 (by decide), hs 16 (by decide)]) (by rw [e0, hv11]; omega) (by rw [e1, h3v]; omega)
    (by rw [e2, e0, h2v, hv11]; omega) (by omega)
  rw [e0, e1, e2, hv11, h3v, h2v, Nat.zero_add] at hdiv
  have hv4 : ((σ1.setv (S 11) (n % r)).setv (S 2) (n / r)).val (S 11) = n % r := by
    simp [Function.update_apply, hne (show (11 : Fin 20) ≠ 2 by decide)]
  have hmod : n % r ≤ n := Nat.mod_le n r
  have h4 := wclear_spec cap (S 11) (n % r) _ hv4 (by rw [hv4]; omega)
  have hmul : (n + 2) * (90 * n + 90 * r + 60) ≤ (n + 2) * (180 * n + 60) := Nat.mul_le_mul_left _ (by omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq hdiv h4)) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h11 : j = S 11
  · subst h11; simp [σ1, Function.update_apply, hne (show (11 : Fin 20) ≠ 2 by decide), hs 11 (by decide)]
  · by_cases h2' : j = S 2
    · subst h2'; simp [Function.update_apply, h11]
    · simp [σ1, Function.update_apply, h11, h2']

/-- **Phase B2**: `S 4 := ⌊log₂(q+1)⌋` from `S 2 = q`, and `S 2` cleared. -/
def phaseB2 (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (.inc (S 2)) (.seq (bitLenM (eB2.trans S)) (.seq (.dec (S 4)) (WM.clear (S 2))))

theorem phaseB2_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h4 : σ.val (S 4) = 0) (hcap : σ.val (S 2) + 4 ≤ cap) :
    WExec cap (phaseB2 S) σ ((σ.setv (S 2) 0).setv (S 4) (Nat.log 2 (σ.val (S 2) + 1))) (70 * σ.val (S 2) + 200) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  set q := σ.val (S 2) with hq
  have h1 := WExec.inc (cap := cap) (S 2) σ (by omega)
  set σ1 := σ.setv (S 2) (σ.val (S 2) + 1) with hσ1
  have hv1 : ∀ i : Fin 20, i ≠ 2 → σ1.val (S i) = σ.val (S i) := by
    intro i hi; simp [σ1, Function.update_apply, hne hi]
  have hv12 : σ1.val (S 2) = q + 1 := by
    show (σ.setv (S 2) (σ.val (S 2) + 1)).val (S 2) = σ.val (S 2) + 1; simp
  have f0 : (eB2.trans S) 0 = S 2 := rfl
  have f1 : (eB2.trans S) 1 = S 12 := rfl
  have f2 : (eB2.trans S) 2 = S 13 := rfl
  have f3 : (eB2.trans S) 3 = S 14 := rfl
  have f4 : (eB2.trans S) 4 = S 4 := rfl
  have f6 : (eB2.trans S) 6 = S 16 := rfl
  have h2 := bitLenM_spec cap (eB2.trans S) σ1 (by rw [f1, hv1 12 (by decide), hs 12 (by decide)])
    (by rw [f2, hv1 13 (by decide), hs 13 (by decide)]) (by rw [f3, hv1 14 (by decide), hs 14 (by decide)])
    (by rw [f4, hv1 4 (by decide), h4]) (by rw [f6, hv1 16 (by decide), hs 16 (by decide)])
    (by rw [f0, hv12]; omega)
  rw [f0, f4, hv12] at h2
  have hbl := CopyNat.natBitLength_le_self_succ (q + 1)
  have hlog : natBitLength (q + 1) - 1 = Nat.log 2 (q + 1) := (log_eq_natBitLength_sub (q + 1)).symm
  have h3 := WExec.dec (cap := cap) (S 4) (σ1.setv (S 4) (natBitLength (q + 1))) (by simp; omega)
  have e3 : (σ1.setv (S 4) (natBitLength (q + 1))).setv (S 4)
      ((σ1.setv (S 4) (natBitLength (q + 1))).val (S 4) - 1) = σ1.setv (S 4) (Nat.log 2 (q + 1)) := by
    simp [wsetv_setv, hlog]
  rw [e3] at h3
  have hv2 : (σ1.setv (S 4) (Nat.log 2 (q + 1))).val (S 2) = q + 1 := by
    simp [Function.update_apply, hne (show (2 : Fin 20) ≠ 4 by decide), hv12]
  have h5 := wclear_spec cap (S 2) (q + 1) _ hv2 (by rw [hv2]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h5))) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h2' : j = S 2
  · subst h2'; simp [Function.update_apply, hne (show (2 : Fin 20) ≠ 4 by decide)]
  · by_cases h4' : j = S 4
    · subst h4'; simp [Function.update_apply, h2']
    · simp [σ1, Function.update_apply, h2', h4']

def phaseB (S : Fin 20 ↪ Fin nr) : WM ns nr := .seq (phaseB1 S) (phaseB2 S)

theorem phaseB_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h2 : σ.val (S 2) = 0) (h4 : σ.val (S 4) = 0)
    (hr : 1 ≤ σ.val (S 3)) (hrn : σ.val (S 3) ≤ σ.val (S 0)) (hcap : σ.val (S 0) + 4 ≤ cap) :
    WExec cap (phaseB S) σ (σ.setv (S 4) (Nat.log 2 (σ.val (S 0) / σ.val (S 3) + 1)))
      ((σ.val (S 0) + 2) * (180 * σ.val (S 0) + 60) + 91 * σ.val (S 0) + 211) := by
  have hq : σ.val (S 0) / σ.val (S 3) ≤ σ.val (S 0) := Nat.div_le_self _ _
  have h1 := phaseB1_spec cap S σ hs h2 hr hrn (by omega)
  have h2' := phaseB2_spec cap S (σ.setv (S 2) (σ.val (S 0) / σ.val (S 3))) (scratch_setv S σ 2 (by decide) _ hs)
    (by rw [val_setvS, if_neg (show ¬ ((4 : Fin 20) = 2) by decide), h4]) (by simp; omega)
  simp only [WState.setv_val, Function.update_self] at h2'
  refine WExec.cast cap (WExec.seq h1 h2') ?_ (by omega)
  have e : σ.setv (S 2) 0 = σ := by
    have := wsetv_same σ (S 2); rwa [h2] at this
  rw [wsetv_setv, e]

/-! ## Phase C: `b = 2^s − 1`, `r/2`, `n − r·b` -/

def eC1 : Fin 4 ↪ Fin 20 := ⟨![4, 5, 11, 12], by decide⟩
def eC3 : Fin 5 ↪ Fin 20 := ⟨![3, 5, 13, 11, 12], by decide⟩
def eC3b : Fin 4 ↪ Fin 20 := ⟨![7, 13, 11, 12], by decide⟩

/-- **Phase C1**: `S 5 := 2^s − 1` from `S 4 = s`. -/
def phaseC1 (S : Fin 20 ↪ Fin nr) : WM ns nr := .seq (pow2W (eC1.trans S)) (.dec (S 5))

theorem phaseC1_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h5 : σ.val (S 5) = 0) (hcap : 2 ^ (σ.val (S 4) + 1) ≤ cap) :
    WExec cap (phaseC1 S) σ (σ.setv (S 5) (2 ^ σ.val (S 4) - 1))
      (σ.val (S 4) * (18 * 2 ^ σ.val (S 4) + 7) + 18 * σ.val (S 4) + 22) := by
  have g0 : (eC1.trans S) 0 = S 4 := rfl
  have g1 : (eC1.trans S) 1 = S 5 := rfl
  have g2 : (eC1.trans S) 2 = S 11 := rfl
  have g3 : (eC1.trans S) 3 = S 12 := rfl
  have h1 := pow2W_spec cap (eC1.trans S) σ (by rw [g1, h5]) (by rw [g2, hs 11 (by decide)])
    (by rw [g3, hs 12 (by decide)]) (by rw [g0]; exact hcap)
  rw [g0, g1] at h1
  have hp : 2 ^ σ.val (S 4) ≤ cap := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)) hcap
  have h2 := WExec.dec (cap := cap) (S 5) (σ.setv (S 5) (2 ^ σ.val (S 4))) (by simp; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  simp [wsetv_setv]

/-- **Phase C2**: `S 6 := r / 2` from `S 3 = r`. -/
def phaseC2 (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 3) (S 6) (S 11)) (.seq (halveM (S 6) (S 11) (S 12)) (WM.clear (S 12)))

theorem phaseC2_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h6 : σ.val (S 6) = 0) (hcap : σ.val (S 3) + 1 ≤ cap) :
    WExec cap (phaseC2 S) σ (σ.setv (S 6) (σ.val (S 3) / 2)) (30 * σ.val (S 3) + 20) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  set r := σ.val (S 3) with hr
  have h1 := FinalPass.Hash4.wcopyR_spec cap (S 3) (S 6) (S 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ h6 (hs 11 (by decide)) (by omega)
  set σ1 := σ.setv (S 6) r with hσ1
  have h2 := halveM_spec cap (S 6) (S 11) (S 12) (hne (by decide)) (hne (by decide)) (hne (by decide)) σ1
    (by simp [σ1, Function.update_apply, hne (show (11 : Fin 20) ≠ 6 by decide), hs 11 (by decide)])
    (by simp [σ1, Function.update_apply, hne (show (12 : Fin 20) ≠ 6 by decide), hs 12 (by decide)])
    (by simp [σ1]; omega) (by omega)
  have hv6 : σ1.val (S 6) = r := by simp [σ1]
  rw [hv6] at h2
  have hv12 : ((σ1.setv (S 6) (r / 2)).setv (S 12) (r % 2)).val (S 12) = r % 2 := by simp
  have h3 := wclear_spec cap (S 12) (r % 2) _ hv12 (by rw [hv12]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h12 : j = S 12
  · subst h12; simp [σ1, Function.update_apply, hne (show (12 : Fin 20) ≠ 6 by decide), hs 12 (by decide)]
  · by_cases h6' : j = S 6
    · subst h6'; simp [σ1, Function.update_apply, h12]
    · simp [σ1, Function.update_apply, h12, h6']

/-- **Phase C3**: `S 7 := n − r·b` from `S 0 = n`, `S 3 = r`, `S 5 = b`. -/
def phaseC3 (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (mulAddW (eC3.trans S)) (.seq (FinalPass.Hash4.wcopyR (S 0) (S 7) (S 11))
    (.seq (subW (eC3b.trans S)) (WM.clear (S 13))))

theorem phaseC3_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h7 : σ.val (S 7) = 0)
    (hcap : σ.val (S 0) + σ.val (S 3) * σ.val (S 5) + σ.val (S 3) + σ.val (S 5) ≤ cap) :
    WExec cap (phaseC3 S) σ (σ.setv (S 7) (σ.val (S 0) - σ.val (S 3) * σ.val (S 5)))
      (σ.val (S 5) * (18 * σ.val (S 3) + 8) + 18 * σ.val (S 5) + 33 * (σ.val (S 3) * σ.val (S 5)) +
        18 * σ.val (S 0) + 30) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  have k0 : (eC3.trans S) 0 = S 3 := rfl
  have k1 : (eC3.trans S) 1 = S 5 := rfl
  have k2 : (eC3.trans S) 2 = S 13 := rfl
  have k3 : (eC3.trans S) 3 = S 11 := rfl
  have k4 : (eC3.trans S) 4 = S 12 := rfl
  have h1 := mulAddW_spec cap (eC3.trans S) σ (by rw [k3, hs 11 (by decide)]) (by rw [k4, hs 12 (by decide)])
    (by rw [k1]; omega) (by rw [k2, k0, k1, hs 13 (by decide)]; omega) (by rw [k0]; omega)
  rw [k0, k1, k2, hs 13 (by decide), Nat.zero_add] at h1
  have hv1 : ∀ i : Fin 20, i ≠ 13 → (σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).val (S i) = σ.val (S i) := by
    intro i hi; simp [Function.update_apply, hne hi]
  have h2 := FinalPass.Hash4.wcopyR_spec cap (S 0) (S 7) (S 11) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))) (by rw [hv1 7 (by decide), h7])
    (by rw [hv1 11 (by decide), hs 11 (by decide)]) (by rw [hv1 0 (by decide)]; omega)
  rw [hv1 0 (by decide)] at h2
  have m0 : (eC3b.trans S) 0 = S 7 := rfl
  have m1 : (eC3b.trans S) 1 = S 13 := rfl
  have m2 : (eC3b.trans S) 2 = S 11 := rfl
  have m3 : (eC3b.trans S) 3 = S 12 := rfl
  have hv2 : ∀ i : Fin 20, i ≠ 7 → i ≠ 13 →
      ((σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).setv (S 7) (σ.val (S 0))).val (S i) = σ.val (S i) := by
    intro i hi hi'; simp [Function.update_apply, hne hi, hne hi']
  have hσ27 : ((σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).setv (S 7) (σ.val (S 0))).val (S 7) = σ.val (S 0) := by
    simp
  have hσ213 : ((σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).setv (S 7) (σ.val (S 0))).val (S 13) =
      σ.val (S 3) * σ.val (S 5) := by
    simp [Function.update_apply, hne (show (13 : Fin 20) ≠ 7 by decide)]
  have h3 := subW_spec cap (eC3b.trans S) ((σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).setv (S 7) (σ.val (S 0)))
    (by rw [m2, hv2 11 (by decide) (by decide), hs 11 (by decide)])
    (by rw [m3, hv2 12 (by decide) (by decide), hs 12 (by decide)]) (by rw [m0, hσ27]; omega)
    (by rw [m1, hσ213]; omega)
  rw [m0, m1, hσ27, hσ213] at h3
  have hv13 : (((σ.setv (S 13) (σ.val (S 3) * σ.val (S 5))).setv (S 7) (σ.val (S 0))).setv (S 7)
      (σ.val (S 0) - σ.val (S 3) * σ.val (S 5))).val (S 13) = σ.val (S 3) * σ.val (S 5) := by
    simp [Function.update_apply, hne (show (13 : Fin 20) ≠ 7 by decide)]
  have h4 := wclear_spec cap (S 13) (σ.val (S 3) * σ.val (S 5)) _ hv13 (by rw [hv13]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h13 : j = S 13
  · subst h13; simp [Function.update_apply, hne (show (13 : Fin 20) ≠ 7 by decide), hs 13 (by decide)]
  · by_cases h7' : j = S 7
    · subst h7'; simp [Function.update_apply, h13]
    · simp [Function.update_apply, h13, h7']

/-- **Phase C**: `S 5 := b`, `S 6 := r/2`, `S 7 := n − r·b` from `S 0 = n`, `S 3 = r`, `S 4 = s`, `2^s − 1 = b`. -/
def phaseC (S : Fin 20 ↪ Fin nr) : WM ns nr := .seq (phaseC1 S) (.seq (phaseC2 S) (phaseC3 S))

theorem phaseC_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr) (n r s b : ℕ)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (hn : σ.val (S 0) = n) (hr : σ.val (S 3) = r)
    (hsv : σ.val (S 4) = s) (hb : 2 ^ s - 1 = b) (h5 : σ.val (S 5) = 0) (h6 : σ.val (S 6) = 0)
    (h7 : σ.val (S 7) = 0) (hcap1 : 2 ^ (s + 1) ≤ cap) (hcap : n + r * b + r + b + 1 ≤ cap) :
    WExec cap (phaseC S) σ (((σ.setv (S 5) b).setv (S 6) (r / 2)).setv (S 7) (n - r * b))
      (s * (18 * 2 ^ s + 7) + 18 * s + b * (18 * r + 8) + 18 * b + 33 * (r * b) + 18 * n + 30 * r + 80) := by
  have h1 := phaseC1_spec cap S σ hs h5 (by rw [hsv]; exact hcap1)
  rw [hsv, hb] at h1
  have hs1 := scratch_setv S σ 5 (by decide) b hs
  have h2 := phaseC2_spec cap S (σ.setv (S 5) b) hs1
    (by rw [val_setvS, if_neg (show ¬ ((6 : Fin 20) = 5) by decide), h6])
    (by rw [val_setvS, if_neg (show ¬ ((3 : Fin 20) = 5) by decide), hr]; omega)
  rw [val_setvS, if_neg (show ¬ ((3 : Fin 20) = 5) by decide), hr] at h2
  have hs2 := scratch_setv S _ 6 (by decide) (r / 2) hs1
  have v0 : ((σ.setv (S 5) b).setv (S 6) (r / 2)).val (S 0) = n := by simp [hn]
  have v3 : ((σ.setv (S 5) b).setv (S 6) (r / 2)).val (S 3) = r := by simp [hr]
  have v5 : ((σ.setv (S 5) b).setv (S 6) (r / 2)).val (S 5) = b := by simp
  have v7 : ((σ.setv (S 5) b).setv (S 6) (r / 2)).val (S 7) = 0 := by simp [h7]
  have h3 := phaseC3_spec cap S ((σ.setv (S 5) b).setv (S 6) (r / 2)) hs2 v7 (by rw [v0, v3, v5]; omega)
  rw [v0, v3, v5] at h3
  exact WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl (by omega)

/-! ## Phase D: `kh = s·(r/2)`, `k = r·s`, the endpoint exponent `fe·L` -/

def eD1 : Fin 5 ↪ Fin 20 := ⟨![4, 6, 8, 11, 12], by decide⟩
def eD2 : Fin 5 ↪ Fin 20 := ⟨![3, 4, 9, 11, 12], by decide⟩
def eD3 : Fin 5 ↪ Fin 20 := ⟨![13, 1, 10, 11, 12], by decide⟩

/-- **Phase D1**: `S 8 := s·(r/2)` from `S 4 = s`, `S 6 = r/2`. -/
def phaseD1 (S : Fin 20 ↪ Fin nr) : WM ns nr := mulAddW (eD1.trans S)

theorem phaseD1_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h8 : σ.val (S 8) = 0)
    (hcap : σ.val (S 4) * σ.val (S 6) + σ.val (S 4) + σ.val (S 6) ≤ cap) :
    WExec cap (phaseD1 S) σ (σ.setv (S 8) (σ.val (S 4) * σ.val (S 6)))
      (σ.val (S 6) * (18 * σ.val (S 4) + 8) + 18 * σ.val (S 6) + 10) := by
  have d0 : (eD1.trans S) 0 = S 4 := rfl
  have d1 : (eD1.trans S) 1 = S 6 := rfl
  have d2 : (eD1.trans S) 2 = S 8 := rfl
  have d3 : (eD1.trans S) 3 = S 11 := rfl
  have d4 : (eD1.trans S) 4 = S 12 := rfl
  have h := mulAddW_spec cap (eD1.trans S) σ (by rw [d3, hs 11 (by decide)]) (by rw [d4, hs 12 (by decide)])
    (by rw [d1]; omega) (by rw [d2, d0, d1, h8]; omega) (by rw [d0]; omega)
  rw [d0, d1, d2, h8, Nat.zero_add] at h
  exact h

/-- **Phase D2**: `S 9 := r·s` from `S 3 = r`, `S 4 = s`. -/
def phaseD2 (S : Fin 20 ↪ Fin nr) : WM ns nr := mulAddW (eD2.trans S)

theorem phaseD2_spec (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h9 : σ.val (S 9) = 0)
    (hcap : σ.val (S 3) * σ.val (S 4) + σ.val (S 3) + σ.val (S 4) ≤ cap) :
    WExec cap (phaseD2 S) σ (σ.setv (S 9) (σ.val (S 3) * σ.val (S 4)))
      (σ.val (S 4) * (18 * σ.val (S 3) + 8) + 18 * σ.val (S 4) + 10) := by
  have d0 : (eD2.trans S) 0 = S 3 := rfl
  have d1 : (eD2.trans S) 1 = S 4 := rfl
  have d2 : (eD2.trans S) 2 = S 9 := rfl
  have d3 : (eD2.trans S) 3 = S 11 := rfl
  have d4 : (eD2.trans S) 4 = S 12 := rfl
  have h := mulAddW_spec cap (eD2.trans S) σ (by rw [d3, hs 11 (by decide)]) (by rw [d4, hs 12 (by decide)])
    (by rw [d1]; omega) (by rw [d2, d0, d1, h9]; omega) (by rw [d0]; omega)
  rw [d0, d1, d2, h9, Nat.zero_add] at h
  exact h

/-- **Phase D3**: `S 10 := fe·L` from `S 1 = L` (through `S 13`). -/
def phaseD3 (fe : ℕ) (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (incN (S 13) fe) (.seq (mulAddW (eD3.trans S)) (WM.clear (S 13)))

theorem phaseD3_spec (fe : ℕ) (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (h10 : σ.val (S 10) = 0)
    (hcap : fe * σ.val (S 1) + fe + σ.val (S 1) ≤ cap) :
    WExec cap (phaseD3 fe S) σ (σ.setv (S 10) (fe * σ.val (S 1)))
      (σ.val (S 1) * (18 * fe + 8) + 18 * σ.val (S 1) + 7 * fe + 13) := by
  have hne : ∀ {i j : Fin 20}, i ≠ j → S i ≠ S j := fun h => S.injective.ne h
  have h1 := incN_spec cap (S 13) fe σ (by rw [hs 13 (by decide)]; omega)
  rw [hs 13 (by decide), Nat.zero_add] at h1
  have hv1 : ∀ i : Fin 20, i ≠ 13 → (σ.setv (S 13) fe).val (S i) = σ.val (S i) := by
    intro i hi; simp [Function.update_apply, hne hi]
  have hv13 : (σ.setv (S 13) fe).val (S 13) = fe := by simp
  have d0 : (eD3.trans S) 0 = S 13 := rfl
  have d1 : (eD3.trans S) 1 = S 1 := rfl
  have d2 : (eD3.trans S) 2 = S 10 := rfl
  have d3 : (eD3.trans S) 3 = S 11 := rfl
  have d4 : (eD3.trans S) 4 = S 12 := rfl
  have h2 := mulAddW_spec cap (eD3.trans S) (σ.setv (S 13) fe)
    (by rw [d3, hv1 11 (by decide), hs 11 (by decide)]) (by rw [d4, hv1 12 (by decide), hs 12 (by decide)])
    (by rw [d1, hv1 1 (by decide)]; omega) (by rw [d2, d0, d1, hv1 10 (by decide), hv1 1 (by decide), hv13, h10]; omega)
    (by rw [d0, hv13]; omega)
  rw [d0, d1, d2, hv1 10 (by decide), hv1 1 (by decide), hv13, h10, Nat.zero_add] at h2
  have hv13' : ((σ.setv (S 13) fe).setv (S 10) (fe * σ.val (S 1))).val (S 13) = fe := by
    simp [Function.update_apply, hne (show (13 : Fin 20) ≠ 10 by decide)]
  have h3 := wclear_spec cap (S 13) fe _ hv13' (by rw [hv13']; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  by_cases h13 : j = S 13
  · subst h13; simp [Function.update_apply, hne (show (13 : Fin 20) ≠ 10 by decide), hs 13 (by decide)]
  · simp [Function.update_apply, h13]

/-- **Phase D**: `S 8 := s·rh`, `S 9 := r·s`, `S 10 := fe·L`. -/
def phaseD (fe : ℕ) (S : Fin 20 ↪ Fin nr) : WM ns nr := .seq (phaseD1 S) (.seq (phaseD2 S) (phaseD3 fe S))

theorem phaseD_spec (fe : ℕ) (S : Fin 20 ↪ Fin nr) (σ : WState ns nr) (L r s rh : ℕ)
    (hs : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0) (hL : σ.val (S 1) = L) (hr : σ.val (S 3) = r)
    (hsv : σ.val (S 4) = s) (hrh : σ.val (S 6) = rh) (h8 : σ.val (S 8) = 0) (h9 : σ.val (S 9) = 0)
    (h10 : σ.val (S 10) = 0) (hc1 : s * rh + s + rh ≤ cap) (hc2 : r * s + r + s ≤ cap)
    (hc3 : fe * L + fe + L ≤ cap) :
    WExec cap (phaseD fe S) σ (((σ.setv (S 8) (s * rh)).setv (S 9) (r * s)).setv (S 10) (fe * L))
      (rh * (18 * s + 8) + 18 * rh + s * (18 * r + 8) + 18 * s + L * (18 * fe + 8) + 18 * L + 7 * fe + 40) := by
  have h1 := phaseD1_spec cap S σ hs h8 (by rw [hsv, hrh]; exact hc1)
  rw [hsv, hrh] at h1
  have hs1 := scratch_setv S σ 8 (by decide) (s * rh) hs
  have u3 : (σ.setv (S 8) (s * rh)).val (S 3) = r := by simp [hr]
  have u4 : (σ.setv (S 8) (s * rh)).val (S 4) = s := by simp [hsv]
  have h2 := phaseD2_spec cap S (σ.setv (S 8) (s * rh)) hs1 (by simp [h9]) (by rw [u3, u4]; exact hc2)
  rw [u3, u4] at h2
  have hs2 := scratch_setv S _ 9 (by decide) (r * s) hs1
  have u1 : ((σ.setv (S 8) (s * rh)).setv (S 9) (r * s)).val (S 1) = L := by simp [hL]
  have h3 := phaseD3_spec cap fe S ((σ.setv (S 8) (s * rh)).setv (S 9) (r * s)) hs2 (by simp [h10])
    (by rw [u1]; exact hc3)
  rw [u1] at h3
  exact WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) rfl (by omega)

/-! ## The per-call star numbers of `P` -/

/-- The whole computation: phases A–D. -/
def starNumsM (cr fe : ℕ) (S : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (phaseA cr S) (.seq (phaseB S) (.seq (phaseC S) (phaseD fe S)))

/-- The output registers: `S 1 = L = ⌈log₂(n+2)⌉`, `S 3 = r`, `S 4 = s`, `S 5 = b`, `S 6 = r/2`, `S 7 = n − r·b`,
`S 8 = s·(r/2)` (the sampled half-width), `S 9 = k = r·s`, `S 10 = fe·L` (the endpoint exponent). -/
def starOut (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) : WState ns nr :=
  ((((((((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r).setv (S 4) P.s).setv (S 5) P.b).setv (S 6)
    (P.r / 2)).setv (S 7) (P.n - P.r * P.b)).setv (S 8) (P.s * (P.r / 2))).setv (S 9) P.k).setv (S 10)
    (fe * Nat.clog 2 (P.n + 2))

/-- The cost of the computation: quadratic in `n`. -/
def starCost (n cr fe : ℕ) : ℕ := 400 * (n + 2) * (n + 2) + 30 * cr + 25 * fe * (n + 2)

theorem starNums_spec (cr fe : ℕ) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (σ : WState ns nr) (hn : σ.val (S 0) = P.n) (hz : ∀ i : Fin 20, i ≠ 0 → σ.val (S i) = 0)
    (hcap : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap) :
    WExec cap (starNumsM cr fe S) σ (starOut σ S P fe) (starCost P.n cr fe) := by
  have hr2 := P.two_le_r
  have hr4 := P.four_r_le_n
  have hrb := P.r_mul_b_le
  have hbs := P.b_succ
  have hexp : (fe + 4) * (P.n + 3) = fe * P.n + 3 * fe + 4 * P.n + 12 := by ring
  have hq : P.n / P.r ≤ P.n := Nat.div_le_self _ _
  have h2s : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hslt : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have hrq : P.r * (P.n / P.r) ≤ P.n := Nat.mul_div_le P.n P.r
  have hrs : P.r * P.s ≤ P.n := le_trans (Nat.mul_le_mul_left _ (by omega)) hrq
  have hsrh : P.s * (P.r / 2) ≤ P.r * P.s := by
    rw [Nat.mul_comm P.r]; exact Nat.mul_le_mul_left _ (by omega)
  have hL : Nat.clog 2 (P.n + 2) ≤ P.n + 2 := by
    rw [clog_two_add_two]; have := CopyNat.natBitLength_le_self_succ (P.n + 1); omega
  have hfL : fe * Nat.clog 2 (P.n + 2) ≤ fe * P.n + 2 * fe := by
    have := Nat.mul_le_mul_left fe hL; rw [Nat.mul_add] at this; omega
  have hs2 : P.s * 2 ^ P.s ≤ P.n * P.n + P.n := by
    have := Nat.mul_le_mul (show P.s ≤ P.n by omega) (show 2 ^ P.s ≤ P.n + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have hpow : 2 ^ (P.s + 1) = 2 * 2 ^ P.s := by rw [pow_succ]; ring
  have hs0 : ∀ i : Fin 20, 11 ≤ i.val → σ.val (S i) = 0 := fun i hi => hz i (scratch_ne hi (by decide))
  -- phase A
  have hA := phaseA_spec cap cr S σ hz (by rw [hn]; omega)
  rw [hn, ← hrP] at hA
  have hsA := scratch_setv S _ 3 (by decide) P.r (scratch_setv S σ 1 (by decide) (Nat.clog 2 (P.n + 2)) hs0)
  -- phase B
  have hB := phaseB_spec cap S ((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r) hsA
    (by simp [hz 2 (by decide)]) (by simp [hz 4 (by decide)]) (by simp; omega) (by simp [hn]; omega)
    (by simp [hn]; omega)
  have a0 : ((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r).val (S 0) = P.n := by simp [hn]
  have a3 : ((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r).val (S 3) = P.r := by simp
  rw [a0, a3] at hB
  -- phase C
  have hsB := scratch_setv S _ 4 (by decide) (Nat.log 2 (P.n / P.r + 1)) hsA
  have hC := phaseC_spec cap S (((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r).setv (S 4)
    (Nat.log 2 (P.n / P.r + 1))) P.n P.r P.s P.b hsB (by simp [hn]) (by simp) (by simp; rfl) rfl
    (by simp [hz 5 (by decide)]) (by simp [hz 6 (by decide)]) (by simp [hz 7 (by decide)]) (by omega) (by omega)
  -- phase D
  have hsC := scratch_setv S _ 7 (by decide) (P.n - P.r * P.b) (scratch_setv S _ 6 (by decide) (P.r / 2)
    (scratch_setv S _ 5 (by decide) P.b hsB))
  have hD := phaseD_spec cap fe S ((((((σ.setv (S 1) (Nat.clog 2 (P.n + 2))).setv (S 3) P.r).setv (S 4)
    (Nat.log 2 (P.n / P.r + 1))).setv (S 5) P.b).setv (S 6) (P.r / 2)).setv (S 7) (P.n - P.r * P.b))
    (Nat.clog 2 (P.n + 2)) P.r P.s (P.r / 2) hsC (by simp) (by simp) (by simp; rfl) (by simp)
    (by simp [hz 8 (by decide)]) (by simp [hz 9 (by decide)]) (by simp [hz 10 (by decide)])
    (by omega) (by omega) (by omega)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB (WExec.seq hC hD))) rfl ?_
  have e1 : (P.n + 2) * (180 * P.n + 60) = 180 * (P.n * P.n) + 420 * P.n + 120 := by ring
  have e2 : 400 * (P.n + 2) * (P.n + 2) = 400 * (P.n * P.n) + 1600 * P.n + 1600 := by ring
  have e3 : 25 * fe * (P.n + 2) = 25 * (fe * P.n) + 50 * fe := by ring
  have e4 : P.s * (18 * 2 ^ P.s + 7) = 18 * (P.s * 2 ^ P.s) + 7 * P.s := by ring
  have e5 : P.b * (18 * P.r + 8) = 18 * (P.r * P.b) + 8 * P.b := by ring
  have e6 : P.r / 2 * (18 * P.s + 8) = 18 * (P.s * (P.r / 2)) + 8 * (P.r / 2) := by ring
  have e7 : P.s * (18 * P.r + 8) = 18 * (P.r * P.s) + 8 * P.s := by ring
  have e8 : Nat.clog 2 (P.n + 2) * (18 * fe + 8) = 18 * (fe * Nat.clog 2 (P.n + 2)) + 8 * Nat.clog 2 (P.n + 2) := by
    ring
  unfold starCost
  omega

/-- The reads of the output block. -/
theorem starOut_val (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) :
    (starOut σ S P fe).val (S 1) = Nat.clog 2 (P.n + 2) ∧ (starOut σ S P fe).val (S 3) = P.r ∧
      (starOut σ S P fe).val (S 4) = P.s ∧ (starOut σ S P fe).val (S 5) = P.b ∧
      (starOut σ S P fe).val (S 6) = P.r / 2 ∧ (starOut σ S P fe).val (S 7) = P.n - P.r * P.b ∧
      (starOut σ S P fe).val (S 8) = P.s * (P.r / 2) ∧ (starOut σ S P fe).val (S 9) = P.k ∧
      (starOut σ S P fe).val (S 10) = fe * Nat.clog 2 (P.n + 2) := by
  simp [starOut]

/-- The other registers of the block keep their values. -/
theorem starOut_val_other (σ : WState ns nr) (S : Fin 20 ↪ Fin nr) (P : Shared.StarParams) (fe : ℕ) (i : Fin 20)
    (hi : i = 0 ∨ i = 2 ∨ 11 ≤ i.val) : (starOut σ S P fe).val (S i) = σ.val (S i) := by
  have h1 : i ≠ 1 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h3 : i ≠ 3 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h4 : i ≠ 4 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h5 : i ≠ 5 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h6 : i ≠ 6 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h7 : i ≠ 7 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h8 : i ≠ 8 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h9 : i ≠ 9 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  have h10 : i ≠ 10 := by rcases hi with rfl | rfl | h <;> first | decide | exact scratch_ne h (by decide)
  simp [starOut, val_setvS, h1, h3, h4, h5, h6, h7, h8, h9, h10]

end NearCubicWires.WireExponent3_5.PrimAsm.StarNums
