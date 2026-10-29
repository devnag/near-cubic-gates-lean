import SourceAdapters.Williams.Formatter

/-!
# W04: the input loader (release input tapes → the leaf's input word, in blocks)

Decode `natWord N`, derive `k` by an exact integer root algorithm, and arrange row-major inputs.
Bound the loader by input length plus polynomial work in `log N`. Consumer: `MultitapeMultiplier.multiplies`
(`Statement.lean:1129–1132`) starts from `inputTapes N A B` (`Statement.lean:1106–1109`): tape 0 = `natWord N ++
rowMajorBitMatrix A`, tape 1 = `rowMajorBitMatrix B`, both without an end marker (`readTapeBit` is `false` beyond the
list, `Statement.lean:336–337`). The leaf's input (`PublishedStatements/Williams.lean`, `inputWord`) is terminated, so
the loader must compute the payload length `P = N·k`, `k = N^{1/10}`. the paper has no sentence for this conversion: its
only input-5 sentences are (`sec:prelim`, "Machine model"; `imp:batch`; `app:sources`).

The loader is a `WMX` program over unary registers (`L/Proof/Wire_3_5/FinalPassWords.lean`), using the release's
register arithmetic (`addR_spec`, `mulR_spec`, `wmove_spec`, `Runs.rep`). This file: state algebra and the first
phases (header width, binary → unary).
-/

namespace NearCubicGates.Adapters.Williams.Load

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {ns nr : ℕ}

/-! ## State algebra -/

@[simp] theorem setv_setv (σ : WState ns nr) (r : Fin nr) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  apply WState.eq <;> simp

@[simp] theorem seth_seth (σ : WState ns nr) (i : Fin (ns + 1)) (a b : ℕ) :
    (σ.seth i a).seth i b = σ.seth i b := by
  apply WState.eq <;> simp

theorem seth_setv (σ : WState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (a b : ℕ) :
    (σ.seth i a).setv r b = (σ.setv r b).seth i a := by
  apply WState.eq <;> simp

@[simp] theorem seth_self (σ : WState ns nr) (i : Fin (ns + 1)) : σ.seth i (σ.sh i) = σ := by
  apply WState.eq <;> simp

/-! ## Zeroing a register -/

/-- `r := 0`. -/
def zeroR (r : Fin nr) : WMX ns nr := .whr r (WMX.dec r)

theorem zeroR_spec {cap : ℕ} (r : Fin nr) : ∀ (v : ℕ) (σ : WState ns nr), σ.val r = v → v ≤ cap →
    WXExec cap (zeroR r) σ (σ.setv r 0) (3 * v + 1) := by
  intro v
  induction v with
  | zero =>
    intro σ hv _
    have : σ.setv r 0 = σ := by rw [← hv, wsetv_same]
    rw [this]; exact WXExec.whrF hv
  | succ v ih =>
    intro σ hv hc
    have e1 := WXExec.dec cap r σ (by omega)
    rw [hv, Nat.add_sub_cancel] at e1
    have e2 := ih (σ.setv r v) (by simp) (by omega)
    rw [setv_setv] at e2
    exact WXExec.mono (WXExec.whrT (by omega) e1 e2) (by omega)

/-! ## Phase a: the header width -/

/-- `WD := WD + (number of `true` cells from the head of `IA`)`; the head stops on the first `false`. -/
def countOnes (IA : Fin (ns + 1)) (WD : Fin nr) : WMX ns nr := .whs IA (.seq (WMX.inc WD) (WMX.fwd IA))

theorem setv_seth_absorb (σ : WState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (a b c d : ℕ) :
    (((σ.setv r a).seth i b).setv r c).seth i d = (σ.setv r c).seth i d := by
  apply WState.eq <;> simp

theorem countOnes_spec {cap : ℕ} (IA : Fin (ns + 1)) (WD : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr),
    (∀ i < m, readTapeBit (σ.st IA) (σ.sh IA + i) = true) → readTapeBit (σ.st IA) (σ.sh IA + m) = false →
    σ.val WD + m ≤ cap → ∀ a b, a = σ.val WD + m → b = σ.sh IA + m →
    WXExec cap (countOnes IA WD) σ ((σ.setv WD a).seth IA b) (m * 7 + 1) := by
  intro m
  induction m with
  | zero =>
    intro σ _ hf _ a b ha hb
    subst ha hb
    simp only [Nat.add_zero, wsetv_same, seth_self]
    exact WXExec.whsF (by simpa [wbit] using hf)
  | succ m ih =>
    intro σ ht hf hc a b ha hb
    have hb0 : wbit σ IA = true := by simpa [wbit] using ht 0 (by omega)
    have e1 := WXExec.inc cap WD σ (by omega)
    have e2 := WXExec.fwd (cap := cap) IA (σ.setv WD (σ.val WD + 1))
    have e3 := ih ((σ.setv WD (σ.val WD + 1)).seth IA ((σ.setv WD (σ.val WD + 1)).sh IA + 1))
      (by
        intro i hi
        have h := ht (i + 1) (by omega)
        simp only [WState.seth_st, WState.seth_sh, WState.setv_st, WState.setv_sh, Function.update_self]
        rwa [show σ.sh IA + 1 + i = σ.sh IA + (i + 1) by omega])
      (by
        simp only [WState.seth_st, WState.seth_sh, WState.setv_st, WState.setv_sh, Function.update_self]
        rwa [show σ.sh IA + 1 + m = σ.sh IA + (m + 1) by omega])
      (by simp; omega) a b (by simp; omega) (by simp; omega)
    rw [setv_seth_absorb] at e3
    exact WXExec.mono (WXExec.whsT hb0 (WXExec.seq e1 e2) e3) (by omega)

/-! ## Phase b: binary → unary -/

theorem mod_two_pow_succ (N i : ℕ) :
    N % 2 ^ (i + 1) = N % 2 ^ i + (if N.testBit i then 2 ^ i else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (N / 2 ^ i) with h | h <;> simp [h]

/-- One bit of the binary → unary pass. -/
def toUnaryBody (IA : Fin (ns + 1)) (RN POW T T2 : Fin nr) : WMX ns nr :=
  .seq (.ifs IA (addR POW RN T) WMX.skip) (.seq (addR POW T2 T) (.seq (.wm (WM.move T2 POW)) (WMX.fwd IA)))

/-- `RN := RN + value of the `WD` bits from the head of `IA`` (least significant first); `POW` ends at `2^WD`. -/
def toUnary (IA : Fin (ns + 1)) (RN POW T T2 WD WD2 : Fin nr) : WMX ns nr :=
  .seq (WMX.inc POW) (repK WD WD2 (toUnaryBody IA RN POW T T2))

/-- Cost of one bit, uniform in the bit index. -/
def toUnaryCost (W : ℕ) : ℕ := 43 * 2 ^ W + 20

set_option hygiene false in
/-- Register-update normalization with the six distinct registers of `toUnary_spec`. -/
local macro "upd" : tactic => `(tactic| simp [Function.update_apply, hRP, hRT, hRT2, hRW, hRW2, hPT, hPT2, hPW,
  hPW2, hTT2, hTW, hTW2, hT2W, hT2W2, hWW2, Ne.symm hRP, Ne.symm hRT, Ne.symm hRT2, Ne.symm hRW, Ne.symm hRW2,
  Ne.symm hPT, Ne.symm hPT2, Ne.symm hPW, Ne.symm hPW2, Ne.symm hTT2, Ne.symm hTW, Ne.symm hTW2, Ne.symm hT2W,
  Ne.symm hT2W2, Ne.symm hWW2])

theorem toUnary_spec {cap : ℕ} (IA : Fin (ns + 1)) {RN POW T T2 WD WD2 : Fin nr}
    (hR : [RN, POW, T, T2, WD, WD2].Nodup) (L : List Bool) (h0 W N : ℕ) (hN : N < 2 ^ W)
    (hbits : ∀ j < W, readTapeBit L (h0 + j) = N.testBit j) (σ : WState ns nr) (hL : σ.st IA = L)
    (hh : σ.sh IA = h0) (hWD : σ.val WD = W) (hWD2 : σ.val WD2 = 0) (hRN : σ.val RN = 0) (hPOW : σ.val POW = 0)
    (hT : σ.val T = 0) (hT2 : σ.val T2 = 0) (hcap : 2 ^ (W + 2) + 2 * W + 1 ≤ cap) :
    Runs cap (toUnary IA RN POW T T2 WD WD2) σ (3 + 1 + (W * (toUnaryCost W + 8) + 7 * W + 3))
      (fun τ => τ.val RN = N ∧ τ.val T = 0 ∧ τ.val T2 = 0 ∧ τ.st IA = L ∧ τ.sh IA = h0 + W ∧ τ.val WD = W ∧
        τ.val WD2 = 0 ∧ SameExcept σ τ [IA] [RN, POW, T2, WD, WD2]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨hRP, hRT, hRT2, hRW, hRW2⟩, ⟨hPT, hPT2, hPW, hPW2⟩, ⟨hTT2, hTW, hTW2⟩, ⟨hT2W, hT2W2⟩, hWW2⟩ := hR
  have hpow : 2 ^ W ≤ 2 ^ (W + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow1 : 2 * 2 ^ W ≤ 2 ^ (W + 2) := by rw [pow_succ, pow_succ]; omega
  let Rg : List (Fin nr) := [RN, POW, T2, WD, WD2]
  let Inv : ℕ → WState ns nr → Prop := fun i τ =>
    τ.val RN = N % 2 ^ i ∧ τ.val POW = 2 ^ i ∧ τ.val T = 0 ∧ τ.val T2 = 0 ∧ τ.st IA = L ∧
      τ.sh IA = h0 + i ∧ SameExcept σ τ [IA] Rg
  have e0 := WXExec.inc cap POW σ (by omega)
  refine Runs.seqE e0 ?_
  have hrep := Runs.rep (cap := cap) (K := WD) (K2 := WD2) (body := toUnaryBody IA RN POW T T2) hWW2
    (toUnaryCost W) W Inv (by omega)
    (by
      rintro k τ v ⟨a1, a2, a3, a4, a5, a6, a7⟩
      exact ⟨by upd; exact a1, by upd; exact a2, by upd; exact a3, by upd; exact a4, a5, a6,
        a7.trans (sameExcept_setv τ (r := WD) (by simp [Rg]) v)⟩)
    (by
      rintro k τ v ⟨a1, a2, a3, a4, a5, a6, a7⟩
      exact ⟨by upd; exact a1, by upd; exact a2, by upd; exact a3, by upd; exact a4, a5, a6,
        a7.trans (sameExcept_setv τ (r := WD2) (by simp [Rg]) v)⟩)
    (by
      rintro k hk τ ⟨a1, a2, a3, a4, a5, a6, a7⟩
      have hNk : N % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
      have hk2 : 2 ^ k ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hbit : wbit τ IA = N.testBit k := by simp only [wbit, a5, a6]; exact hbits k hk
      have s1 : Runs cap (.ifs IA (addR POW RN T) WMX.skip) τ (18 * 2 ^ k + 4)
          (fun τ1 => τ1 = τ.setv RN (N % 2 ^ (k + 1))) := by
        rw [mod_two_pow_succ]
        cases hb : N.testBit k
        · refine (Runs.ifsF (by rw [hbit, hb]) (Runs.of (WXExec.skip (cap := cap) τ) ?_)).cost (by omega)
          simp only [Bool.false_eq_true, if_false, Nat.add_zero, ← a1, wsetv_same]
        · have e := addR_spec cap (Ne.symm hRP) hPT hRT τ a3 (by rw [a1, a2]; omega)
          rw [a2, a1] at e
          refine Runs.ifsT (by rw [hbit, hb]) (Runs.of e ?_)
          simp
      refine (Runs.seq (c2 := 18 * 2 ^ k + 3 + 1 + (7 * 2 ^ k + 1 + 1 + 1)) s1 fun τ1 h1 => ?_).mono
        (by unfold toUnaryCost; omega) (fun ρ hρ => hρ)
      subst h1
      have v1 : (τ.setv RN (N % 2 ^ (k + 1))).val POW = 2 ^ k := by upd; exact a2
      have v2 : (τ.setv RN (N % 2 ^ (k + 1))).val T = 0 := by upd; exact a3
      have v3 : (τ.setv RN (N % 2 ^ (k + 1))).val T2 = 0 := by upd; exact a4
      have e2 := addR_spec cap hPT2 hPT (Ne.symm hTT2) (τ.setv RN (N % 2 ^ (k + 1))) v2 (by rw [v1, v3]; omega)
      rw [v1, v3, Nat.zero_add] at e2
      refine Runs.seqE e2 ?_
      set τ2 := (τ.setv RN (N % 2 ^ (k + 1))).setv T2 (2 ^ k) with hτ2
      have w1 : τ2.val T2 = 2 ^ k := by simp [hτ2]
      have w2 : τ2.val POW = 2 ^ k := by rw [hτ2]; upd; exact a2
      have e3 := WXExec.wm (wmove_spec (cap := cap) T2 POW (Ne.symm hPT2) (2 ^ k) τ2 w1 (by omega)
        (by rw [w1, w2]; omega))
      refine Runs.seqE e3 ?_
      set τ3 := (τ2.setv T2 0).setv POW (τ2.val POW + τ2.val T2) with hτ3
      refine Runs.of (WXExec.fwd (cap := cap) IA τ3) ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [hτ3, hτ2]; upd
      · rw [hτ3, w1, w2]; simp [pow_succ]; ring
      · rw [hτ3, hτ2]; upd; exact a3
      · rw [hτ3]; upd
      · rw [hτ3, hτ2]; simp [a5]
      · rw [hτ3, hτ2]; simp [a6]; omega
      · refine a7.trans ?_
        refine SameExcept.trans (sameExcept_setv τ (r := RN) (by simp [Rg]) (N % 2 ^ (k + 1))) ?_
        refine SameExcept.trans (sameExcept_setv _ (r := T2) (by simp [Rg]) (2 ^ k)) ?_
        refine SameExcept.trans (sameExcept_setv τ2 (r := T2) (by simp [Rg]) 0) ?_
        refine SameExcept.trans (sameExcept_setv (τ2.setv T2 0) (r := POW) (by simp [Rg])
          (τ2.val POW + τ2.val T2)) ?_
        exact sameExcept_seth τ3 (by simp) _
      · rw [hτ3, hτ2]; upd
      · rw [hτ3, hτ2]; upd)
  have hstart : Inv 0 (σ.setv POW (σ.val POW + 1)) := by
    refine ⟨by upd; simp [hRN, Nat.mod_one, pow_zero], by simp [hPOW], by upd; exact hT, by upd; exact hT2, by simp [hL], by simp [hh],
      sameExcept_setv σ (r := POW) (by simp [Rg]) _⟩
  refine (hrep _ hstart (by upd; exact hWD) (by upd; exact hWD2)).post ?_
  rintro τ ⟨⟨a1, -, a3, a4, a5, a6, a7⟩, hK, hK2⟩
  refine ⟨by rw [a1, Nat.mod_eq_of_lt hN], a3, a4, a5, a6, ?_, hK2, a7⟩
  rw [hK]

/-! ## Phase c: the tenth root `k` of `N` -/

theorem wstate_val_eq {σ τ : WState ns nr} (h1 : σ.sh = τ.sh) (h2 : σ.st = τ.st) (h4 : σ.cell = τ.cell)
    (h3 : ∀ r, σ.val r = τ.val r) : σ = τ := WState.eq h1 h2 (funext h3) h4

/-- Equal register files after `setv` chains on distinct registers. -/
macro "regeq" : tactic => `(tactic| (refine wstate_val_eq rfl rfl rfl (fun r => ?_); simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all))

set_option hygiene false in
/-- Register reads through `setv` chains with the 21 distinctness facts `h1 … h21` of the root search. -/
local macro "upr" : tactic => `(tactic| simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
  h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
  Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13,
  Ne.symm h14, Ne.symm h15, Ne.symm h16, Ne.symm h17, Ne.symm h18, Ne.symm h19, Ne.symm h20, Ne.symm h21])

set_option hygiene false in
/-- Destructure the distinctness of the root-search registers into `h1 … h21`. -/
local macro "nodup7" : tactic => `(tactic| (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, not_false_eq_true] at hR; obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩, ⟨h16, h17, h18⟩, ⟨h19, h20⟩, h21⟩ := hR))

section Root
variable {cap : ℕ} {KC PC PC2 TMP DIFF T RN : Fin nr}

/-- `PC := PC · KC` (through `TMP`). -/
def mulStep (KC PC PC2 TMP T : Fin nr) : WMX ns nr :=
  .seq (mulR PC PC2 KC TMP T) (.seq (zeroR PC) (.wm (WM.move TMP PC)))

/-- `n` multiplications by `KC`. -/
def powLoop (KC PC PC2 TMP T : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | n + 1 => .seq (powLoop KC PC PC2 TMP T n) (mulStep KC PC PC2 TMP T)

/-- `DIFF := RN - KC^10` (truncated), every other register restored. -/
def powDiff (KC PC PC2 TMP DIFF T RN : Fin nr) : WMX ns nr :=
  .seq (WMX.inc PC) (.seq (powLoop KC PC PC2 TMP T 10) (.seq (addR RN DIFF T)
    (.seq (repK PC PC2 (WMX.dec DIFF)) (zeroR PC))))

/-- The search: `KC := 1`, then `KC := KC + 1` while `RN - KC^10 > 0`. -/
def rootSearch (KC PC PC2 TMP DIFF T RN : Fin nr) : WMX ns nr :=
  .seq (WMX.inc KC) (.seq (powDiff KC PC PC2 TMP DIFF T RN)
    (.whr DIFF (.seq (zeroR DIFF) (.seq (WMX.inc KC) (powDiff KC PC PC2 TMP DIFF T RN)))))

variable (hR : [KC, PC, PC2, TMP, DIFF, T, RN].Nodup)
include hR

theorem mulStep_spec (σ : WState ns nr) (c v N : ℕ) (hKC : σ.val KC = c) (hPC2 : σ.val PC2 = 0)
    (hTMP : σ.val TMP = 0) (hT : σ.val T = 0) (hvc : v * c ≤ N) (hv : v ≤ N) (hcap : 2 * N ≤ cap) :
    WXExec cap (mulStep KC PC PC2 TMP T) (σ.setv PC v) (σ.setv PC (v * c)) (25 * N + 21 * N + 7) := by
  nodup7
  have hl : [PC, PC2, KC, TMP, T].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]; upr
  have e1 := mulR_spec cap hl (σ.setv PC v) (by upr; exact hPC2) (by upr; exact hT)
    (by upr; rw [hTMP, hKC]; omega) (by simp; omega)
  have va : (σ.setv PC v).val TMP = 0 := by upr; exact hTMP
  have vb : (σ.setv PC v).val KC = c := by upr; exact hKC
  rw [va, vb, Nat.zero_add, show (σ.setv PC v).val PC = v by simp] at e1
  have e2 := zeroR_spec (cap := cap) PC v ((σ.setv PC v).setv TMP (v * c)) (by upr) (by omega)
  have e3 := wmove_spec (cap := cap) TMP PC (Ne.symm h8) (v * c) (((σ.setv PC v).setv TMP (v * c)).setv PC 0)
    (by upr) (by upr; omega) (by upr; omega)
  have e := WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))
  refine WXExec.mono (WXExec.cast cap e ?_ le_rfl) ?_
  · regeq
  · have : v * (18 * c + 3 + 8) + 7 * v + 3 = 18 * (v * c) + 18 * v + 3 := by ring
    rw [this]; omega

theorem powLoop_spec (σ : WState ns nr) (c N : ℕ) (hc : 1 ≤ c) (hcN : c ^ 10 ≤ N) (hKC : σ.val KC = c)
    (hPC2 : σ.val PC2 = 0) (hTMP : σ.val TMP = 0) (hT : σ.val T = 0) (hcap : 2 * N ≤ cap) :
    ∀ n ≤ 10, WXExec cap (powLoop KC PC PC2 TMP T n) (σ.setv PC 1) (σ.setv PC (c ^ n)) (n * (46 * N + 8)) := by
  intro n
  induction n with
  | zero => intro _; rw [pow_zero]; exact WXExec.cast cap (WXExec.skip cap (σ.setv PC 1)) rfl (by simp)
  | succ n ih =>
    intro hn
    have hpow : c ^ (n + 1) ≤ N := le_trans (Nat.pow_le_pow_right hc hn) hcN
    have hpow' : c ^ n ≤ N := le_trans (Nat.pow_le_pow_right hc (by omega)) hpow
    have e := mulStep_spec hR σ c (c ^ n) N hKC hPC2 hTMP hT (by rw [← pow_succ]; exact hpow) hpow' hcap
    rw [← pow_succ] at e
    have hc : (n + 1) * (46 * N + 8) = n * (46 * N + 8) + (46 * N + 8) := by ring
    exact WXExec.mono (WXExec.seq (ih (by omega)) e) (by omega)

/-- Uniform cost bound of `powDiff`. -/
def powDiffCost (N : ℕ) : ℕ := 500 * N + 100

theorem powDiff_spec (σ : WState ns nr) (c N : ℕ) (hc : 1 ≤ c) (hcN : c ^ 10 ≤ N) (hKC : σ.val KC = c)
    (hPC : σ.val PC = 0) (hPC2 : σ.val PC2 = 0) (hTMP : σ.val TMP = 0) (hDIFF : σ.val DIFF = 0)
    (hT : σ.val T = 0) (hRN : σ.val RN = N) (hcap : 2 * N + 2 ≤ cap) :
    WXExec cap (powDiff KC PC PC2 TMP DIFF T RN) σ (σ.setv DIFF (N - c ^ 10)) (powDiffCost N) := by
  have hR' := hR
  nodup7
  have e1 := WXExec.inc cap PC σ (by rw [hPC]; omega)
  rw [hPC, Nat.zero_add] at e1
  have e2 := powLoop_spec (cap := cap) hR' σ c N hc hcN hKC hPC2 hTMP hT (by omega) 10 le_rfl
  have e3 := addR_spec cap (Ne.symm h20) (Ne.symm h21) h19 (σ.setv PC (c ^ 10)) (by upr; exact hT)
    (by upr; rw [hDIFF, hRN]; omega)
  have v3a : (σ.setv PC (c ^ 10)).val DIFF = 0 := by upr; exact hDIFF
  have v3b : (σ.setv PC (c ^ 10)).val RN = N := by upr; exact hRN
  rw [v3a, v3b, Nat.zero_add] at e3
  let st : ℕ → WState ns nr := fun j => (σ.setv PC (c ^ 10)).setv DIFF (N - j)
  have e4 := Runs.repE (cap := cap) (K := PC) (K2 := PC2) (body := WMX.dec DIFF) h7 1 (c ^ 10) st
    (by omega) (fun j => by simp only [st]; upr) (fun j => by simp only [st]; upr)
    (by
      intro j _ v1 v2
      have e := WXExec.dec cap DIFF (((st j).setv PC v1).setv PC2 v2) (by simp only [st]; upr; omega)
      refine WXExec.cast cap e ?_ le_rfl
      have hv : (((st j).setv PC v1).setv PC2 v2).val DIFF - 1 = N - (j + 1) := by simp only [st]; upr; omega
      rw [hv]
      simp only [st]
      regeq)
    (by simp only [st]; upr) (by simp only [st]; upr; exact hPC2)
  have e4' : WXExec cap (repK PC PC2 (WMX.dec DIFF)) ((σ.setv PC (c ^ 10)).setv DIFF N)
      ((σ.setv PC (c ^ 10)).setv DIFF (N - c ^ 10)) (c ^ 10 * (1 + 8) + 7 * c ^ 10 + 3) := by
    simpa [st] using e4
  have e5 := zeroR_spec (cap := cap) PC (c ^ 10) ((σ.setv PC (c ^ 10)).setv DIFF (N - c ^ 10)) (by upr) (by omega)
  have e := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4' e5)))
  refine WXExec.mono (WXExec.cast cap e ?_ le_rfl) (by unfold powDiffCost; omega)
  regeq

/-- Cost of one round of the search. -/
def roundCost (N : ℕ) : ℕ := powDiffCost N + 3 * N + 10

/-- **The tenth root.** From `KC = 0` and `RN = N = k^10`, the search ends with `KC = k`. -/
theorem rootSearch_spec (σ : WState ns nr) (k N : ℕ) (hk : 1 ≤ k) (hN : N = k ^ 10) (hKC : σ.val KC = 0)
    (hPC : σ.val PC = 0) (hPC2 : σ.val PC2 = 0) (hTMP : σ.val TMP = 0) (hDIFF : σ.val DIFF = 0)
    (hT : σ.val T = 0) (hRN : σ.val RN = N) (hcap : 2 * N + 2 ≤ cap) :
    WXExec cap (rootSearch KC PC PC2 TMP DIFF T RN) σ (σ.setv KC k)
      (3 + 1 + (powDiffCost N + 1 + (k * (roundCost N + 2) + 1))) := by
  have hR' := hR
  nodup7
  have hkN : k ≤ N := by rw [hN]; exact Nat.le_self_pow (by norm_num) k
  have hpk : ∀ c ≤ k, c ^ 10 ≤ N := fun c hc => hN ▸ Nat.pow_le_pow_left hc 10
  let Inv : ℕ → WState ns nr → Prop := fun m τ =>
    m < k ∧ τ = (σ.setv KC (k - m)).setv DIFF (N - (k - m) ^ 10)
  have hloop := Runs.whr (cap := cap) (r := DIFF)
    (P := .seq (zeroR DIFF) (.seq (WMX.inc KC) (powDiff KC PC PC2 TMP DIFF T RN))) Inv (roundCost N)
    (fun τ => τ = σ.setv KC k)
    (by
      rintro τ ⟨_, rfl⟩
      refine ⟨by simp [hN], ?_⟩
      rw [Nat.sub_zero, hN, Nat.sub_self]
      regeq)
    (by
      rintro m τ ⟨hm, rfl⟩
      set c := k - (m + 1) with hcdef
      have hc1 : 1 ≤ c := by omega
      have hck : c < k := by omega
      have hlt : c ^ 10 < N := hN ▸ Nat.pow_lt_pow_left hck (by norm_num)
      refine ⟨by upr; omega, ?_⟩
      have e1 := zeroR_spec (cap := cap) DIFF (N - c ^ 10) ((σ.setv KC c).setv DIFF (N - c ^ 10)) (by simp)
        (by omega)
      have e2 := WXExec.inc cap KC (((σ.setv KC c).setv DIFF (N - c ^ 10)).setv DIFF 0) (by upr; omega)
      have e3 := powDiff_spec hR' (σ.setv KC (c + 1)) (c + 1) N (by omega) (hpk _ (by omega)) (by simp)
        (by upr; exact hPC) (by upr; exact hPC2) (by upr; exact hTMP) (by upr; exact hDIFF) (by upr; exact hT)
        (by upr; exact hRN) hcap
      have hs : (((σ.setv KC c).setv DIFF (N - c ^ 10)).setv DIFF 0).setv KC
          ((((σ.setv KC c).setv DIFF (N - c ^ 10)).setv DIFF 0).val KC + 1) = σ.setv KC (c + 1) := by
        have : (((σ.setv KC c).setv DIFF (N - c ^ 10)).setv DIFF 0).val KC = c := by upr
        rw [this]; regeq
      rw [hs] at e2
      refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) (by unfold roundCost; omega), by omega, ?_⟩
      rw [show k - m = c + 1 by omega])
  have e1 := WXExec.inc cap KC σ (by omega)
  rw [hKC, Nat.zero_add] at e1
  have e2 := powDiff_spec hR' (σ.setv KC 1) 1 N le_rfl (by simpa using hpk 1 hk) (by simp) (by upr; exact hPC)
    (by upr; exact hPC2) (by upr; exact hTMP) (by upr; exact hDIFF) (by upr; exact hT) (by upr; exact hRN) hcap
  obtain ⟨τ, e3, hτ⟩ := hloop (k - 1) _ ⟨by omega, by rw [show k - (k - 1) = 1 by omega]⟩
  subst hτ
  exact WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) (by
    have : (k - 1) * (roundCost N + 2) ≤ k * (roundCost N + 2) := Nat.mul_le_mul_right _ (by omega)
    omega)

end Root

/-! ## Phases e–h: writing blocks -/

@[simp] theorem sets_sets' (σ : WState ns nr) (i : Fin (ns + 1)) (x y : List Bool) :
    (σ.sets i x).sets i y = σ.sets i y := by
  apply WState.eq <;> simp

theorem seth_sets (σ : WState ns nr) (i j : Fin (ns + 1)) (a : ℕ) (l : List Bool) :
    (σ.seth i a).sets j l = (σ.sets j l).seth i a := by
  apply WState.eq <;> simp

/-- Append `bs` at the end of stream `S` (head on the end). -/
def writeBits (S : Fin (ns + 1)) : List Bool → WMX ns nr
  | [] => WMX.skip
  | b :: bs => .seq (.seq (WMX.wr S b) (WMX.fwd S)) (writeBits S bs)

theorem writeBits_spec {cap : ℕ} (S : Fin (ns + 1)) : ∀ (bs : List Bool) (σ : WState ns nr),
    σ.sh S = (σ.st S).length →
    WXExec cap (writeBits S bs) σ ((σ.sets S (σ.st S ++ bs)).seth S ((σ.st S).length + bs.length)) (4 * bs.length)
  | [], σ, h => by
    simp only [List.append_nil, List.length_nil, Nat.add_zero, Nat.mul_zero]
    have : (σ.sets S (σ.st S)).seth S (σ.st S).length = σ := by rw [← h]; apply WState.eq <;> simp
    rw [this]; exact WXExec.skip cap σ
  | b :: bs, σ, h => by
    have e1 := WXExec.wr (cap := cap) S b σ
    rw [h, Format.writeTapeBit_end] at e1
    have e2 := WXExec.fwd (cap := cap) S (σ.sets S (σ.st S ++ [b]))
    set σ2 := (σ.sets S (σ.st S ++ [b])).seth S ((σ.sets S (σ.st S ++ [b])).sh S + 1) with hσ2
    have h2 : σ2.sh S = (σ2.st S).length := by simp [hσ2, h]
    have e3 := writeBits_spec (cap := cap) S bs σ2 h2
    have hfin : (σ2.sets S (σ2.st S ++ bs)).seth S ((σ2.st S).length + bs.length) =
        (σ.sets S (σ.st S ++ b :: bs)).seth S ((σ.st S).length + (b :: bs).length) := by
      have hs2 : σ2.st S = σ.st S ++ [b] := by simp [hσ2]
      rw [hs2, hσ2]
      apply WState.eq
      · simp only [WState.seth_sh, WState.sets_sh, Function.update_idem]
        congr 1
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp [List.append_assoc]
      · simp
      · simp
    rw [hfin] at e3
    exact WXExec.mono (WXExec.seq (WXExec.seq e1 e2) e3) (by simp; omega)

theorem flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatMap f = (l.take j).flatMap f ++ f l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Copy `PP` bits of stream `IX` to the end of `SIM`, bit `b` as the block `blk b`. -/
def copyBits (IX SIM : Fin (ns + 1)) (PP PP2 : Fin nr) (blk : Bool → List Bool) : WMX ns nr :=
  repK PP PP2 (.seq (.ifs IX (writeBits SIM (blk true)) (writeBits SIM (blk false))) (WMX.fwd IX))

theorem copyBits_spec {cap : ℕ} {IX SIM : Fin (ns + 1)} {PP PP2 : Fin nr} (hIS : IX ≠ SIM) (hPP : PP ≠ PP2)
    (blk : Bool → List Bool) (w : ℕ) (hw : ∀ b, (blk b).length = w) (LX : List Bool) (h : ℕ) (bits : List Bool)
    (hbits : ∀ j (hj : j < bits.length), readTapeBit LX (h + j) = bits[j]) (σ : WState ns nr)
    (hX : σ.st IX = LX) (hXh : σ.sh IX = h) (hS : σ.sh SIM = (σ.st SIM).length)
    (hK : σ.val PP = bits.length) (hK2 : σ.val PP2 = 0) (hcap : 2 * bits.length ≤ cap) :
    Runs cap (copyBits IX SIM PP PP2 blk) σ (bits.length * (4 * w + 3 + 8) + 7 * bits.length + 3)
      (fun τ => τ.st SIM = σ.st SIM ++ bits.flatMap blk ∧ τ.sh SIM = (τ.st SIM).length ∧ τ.st IX = LX ∧
        τ.sh IX = h + bits.length ∧ τ.val PP = bits.length ∧ τ.val PP2 = 0 ∧
        SameExcept σ τ [SIM, IX] [PP, PP2]) := by
  let Inv : ℕ → WState ns nr → Prop := fun j τ =>
    τ.st SIM = σ.st SIM ++ (bits.take j).flatMap blk ∧ τ.sh SIM = (τ.st SIM).length ∧ τ.st IX = LX ∧
      τ.sh IX = h + j ∧ SameExcept σ τ [SIM, IX] [PP, PP2]
  have hrep := Runs.rep (cap := cap) (K := PP) (K2 := PP2)
    (body := .seq (.ifs IX (writeBits SIM (blk true)) (writeBits SIM (blk false))) (WMX.fwd IX)) hPP
    (4 * w + 3) bits.length Inv hcap
    (fun j τ v ⟨a1, a2, a3, a4, a5⟩ => ⟨a1, a2, a3, a4, a5.trans (sameExcept_setv τ (r := PP) (by simp) v)⟩)
    (fun j τ v ⟨a1, a2, a3, a4, a5⟩ => ⟨a1, a2, a3, a4, a5.trans (sameExcept_setv τ (r := PP2) (by simp) v)⟩)
    (by
      rintro j hj τ ⟨a1, a2, a3, a4, a5⟩
      have hb : wbit τ IX = bits[j] := by simp only [wbit, a3, a4]; exact hbits j hj
      have key : ∀ b, bits[j] = b → Runs cap (.ifs IX (writeBits SIM (blk true)) (writeBits SIM (blk false))) τ
          (4 * w + 1) (fun ρ => ρ = (τ.sets SIM (τ.st SIM ++ blk b)).seth SIM ((τ.st SIM).length + w)) := by
        intro b hbj
        have e1 := writeBits_spec (cap := cap) SIM (blk b) τ a2
        rw [hw] at e1
        cases b
        · exact Runs.ifsF (by rw [hb, hbj]) (Runs.of e1 rfl)
        · exact Runs.ifsT (by rw [hb, hbj]) (Runs.of e1 rfl)
      refine (Runs.seq (c2 := 1) (key _ rfl) fun ρ hρ => ?_).mono (by omega) (fun _ h => h)
      subst hρ
      set τ1 := (τ.sets SIM (τ.st SIM ++ blk bits[j])).seth SIM ((τ.st SIM).length + w) with hτ1
      refine Runs.of (WXExec.fwd (cap := cap) IX τ1) ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
      · simp [hτ1, a1, flatMap_take_succ bits blk j hj, List.append_assoc]
      · simp [hτ1, Function.update_of_ne (Ne.symm hIS), hw]
      · simp [hτ1, Function.update_of_ne hIS, a3]
      · simp [hτ1, Function.update_of_ne hIS, a4]; omega
      · refine a5.trans ?_
        refine SameExcept.trans (sameExcept_sets τ (X := SIM) (by simp) (τ.st SIM ++ blk bits[j])) ?_
        refine SameExcept.trans (sameExcept_seth (τ.sets SIM (τ.st SIM ++ blk bits[j])) (X := SIM) (by simp)
          ((τ.st SIM).length + w)) ?_
        exact sameExcept_seth τ1 (X := IX) (by simp) (τ1.sh IX + 1))
  obtain ⟨τ, e, ⟨a1, a2, a3, a4, a5⟩, hK', hK2'⟩ := hrep σ ⟨by simp, hS, hX, by simp [hXh],
    SameExcept.refl σ _ _⟩ hK hK2
  rw [List.take_length] at a1
  exact ⟨τ, e, a1, a2, a3, a4, hK', hK2', a5⟩

/-! ## The rewind and the block word -/

/-- `n` backward moves. -/
def bwdN (i : Fin (ns + 1)) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | n + 1 => .seq (WMX.bwd i) (bwdN i n)

theorem bwdN_spec {cap : ℕ} (i : Fin (ns + 1)) : ∀ (n : ℕ) (σ : WState ns nr),
    WXExec cap (bwdN i n) σ (σ.seth i (σ.sh i - n)) (2 * n)
  | 0, σ => WXExec.cast cap (WXExec.skip cap σ) (by simp) le_rfl
  | n + 1, σ => by
    have e := WXExec.seq (WXExec.bwd (cap := cap) i σ) (bwdN_spec i n (σ.seth i (σ.sh i - 1)))
    simp only [WState.seth_sh, Function.update_self, seth_seth] at e
    rw [show σ.sh i - 1 - n = σ.sh i - (n + 1) by omega] at e
    exact WXExec.mono e (by omega)

/-- Move the head of `S` back by `PP · w` cells. -/
def backBlocks (S : Fin (ns + 1)) (PP PP2 : Fin nr) (w : ℕ) : WMX ns nr := repK PP PP2 (bwdN S w)

theorem backBlocks_spec {cap : ℕ} {S : Fin (ns + 1)} {PP PP2 : Fin nr} (hPP : PP ≠ PP2) (w n : ℕ)
    (σ : WState ns nr) (hK : σ.val PP = n) (hK2 : σ.val PP2 = 0) (hcap : 2 * n ≤ cap) :
    Runs cap (backBlocks S PP PP2 w) σ (n * (2 * w + 8) + 7 * n + 3)
      (fun τ => τ.sh S = σ.sh S - n * w ∧ τ.st S = σ.st S ∧ τ.val PP = n ∧ τ.val PP2 = 0 ∧
        SameExcept σ τ [S] [PP, PP2]) := by
  let Inv : ℕ → WState ns nr → Prop := fun j τ =>
    τ.sh S = σ.sh S - j * w ∧ τ.st S = σ.st S ∧ SameExcept σ τ [S] [PP, PP2]
  obtain ⟨τ, e, ⟨a1, a0, a2⟩, h1, h2⟩ := Runs.rep (cap := cap) (K := PP) (K2 := PP2) (body := bwdN S w) hPP
    (2 * w) n Inv hcap (fun j τ v ⟨a1, a0, a2⟩ => ⟨a1, a0, a2.trans (sameExcept_setv τ (r := PP) (by simp) v)⟩)
    (fun j τ v ⟨a1, a0, a2⟩ => ⟨a1, a0, a2.trans (sameExcept_setv τ (r := PP2) (by simp) v)⟩)
    (by
      rintro j _ τ ⟨a1, a0, a2⟩
      refine Runs.of (bwdN_spec (cap := cap) S w τ) ⟨⟨?_, by simp [a0],
        a2.trans (sameExcept_seth τ (X := S) (by simp) _)⟩, rfl, rfl⟩
      simp [a1, Nat.succ_mul, Nat.sub_sub])
    σ ⟨by simp, rfl, SameExcept.refl σ _ _⟩ hK hK2
  exact ⟨τ, e, a1, a0, h1, h2, a2⟩

/-- The block of a symbol: its `w = x + 4` code bits. -/
def blockOf {x : ℕ} (s : Symbol x) : List Bool := List.ofFn fun j : Fin (x + 4) => code s j.val

theorem blockOf_length {x : ℕ} (s : Symbol x) : (blockOf s).length = x + 4 := by simp [blockOf]

/-- A word written block by block holds the word (the W04 → W03 interface). -/
theorem holds_flatMap {x : ℕ} : ∀ (ws : List (Symbol x)), Holds (fun p => ws.getD p Symbol.blank) (ws.flatMap blockOf)
  | [] => by intro p j _; simp [readTapeBit]
  | s :: ws => by
    intro p j hj
    rw [List.flatMap_cons]
    cases p with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, readTapeBit]
      rw [List.getD_append _ _ _ _ (by rw [blockOf_length]; exact hj),
        List.getD_eq_getElem _ _ (by rw [blockOf_length]; exact hj)]
      simp only [blockOf, List.getElem_ofFn]
    | succ p =>
      simp only [List.getD_cons_succ, readTapeBit]
      rw [List.getD_append_right _ _ _ _ (by rw [blockOf_length, Nat.mul_succ]; omega), blockOf_length,
        show (x + 4) * (p + 1) + j - (x + 4) = (x + 4) * p + j by rw [Nat.mul_succ]; omega]
      exact holds_flatMap ws p j hj

end NearCubicGates.Adapters.Williams.Load
