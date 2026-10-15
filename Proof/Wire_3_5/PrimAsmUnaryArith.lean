import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

variable {ns nr : ℕ} (cap : ℕ)

/-- `a` times: decrement `b`, or set the flag `f` if `b` is already `0`. -/
def decAgainstW (a b f : Fin nr) : WM ns nr := .whr a (.seq (.dec a) (.ifr b (.dec b) (WM.setF f)))

theorem decAgainstW_spec (a b f : Fin nr) (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) (hcap : 1 ≤ cap) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → n ≤ cap → σ.val b ≤ cap → σ.val f ≤ 1 →
      WExec cap (decAgainstW a b f) σ
        (((σ.setv a 0).setv b (σ.val b - n)).setv f (if σ.val b < n then 1 else σ.val f)) (9 * n + 1)
  | 0, σ, h0, _, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b - 0)).setv f (if σ.val b < 0 then 1 else σ.val f) = σ := by
      simp only [Nat.sub_zero, Nat.not_lt_zero, if_false]
      wgen_eq [h0]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hc, hb, hf => by
    have h1 := WExec.dec (cap := cap) a σ (by omega)
    have hb1 : (σ.setv a (σ.val a - 1)).val b = σ.val b := wsetv_val_ne _ _ (Ne.symm hab)
    have hf1 : (σ.setv a (σ.val a - 1)).val f = σ.val f := wsetv_val_ne _ _ (Ne.symm haf)
    by_cases hb0 : σ.val b = 0
    · have h2 := wsetF_spec cap f (σ.setv a (σ.val a - 1)) (by rw [hf1]; exact hf) hcap
      have h2' := WExec.ifrF (P := .dec b) (by rw [hb1]; exact hb0) h2
      have ih := decAgainstW_spec a b f hab haf hbf hcap n ((σ.setv a (σ.val a - 1)).setv f 1)
        (by simp [Function.update_apply, haf]; omega) (by omega) (by simp [Function.update_apply, hbf, Ne.symm hab]; omega)
        (by simp)
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2') ih) ?_ (by omega)
      wgen_eq [hb0, hn]
    · have h2 := WExec.dec (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [hb1]; exact hb)
      have h2' := WExec.ifrT (Q := WM.setF f) (by rw [hb1]; exact hb0) h2
      have ih := decAgainstW_spec a b f hab haf hbf hcap n
        ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b - 1))
        (by simp [Function.update_apply, hab, Ne.symm hab]; omega) (by omega)
        (by simp [Function.update_apply, hab, Ne.symm hab]; omega)
        (by simp [Function.update_apply, Ne.symm hbf, Ne.symm haf]; omega)
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2') ih) ?_ (by omega)
      wgen_eq [hb0, hn]

/-! ## Compare, subtract, multiply-add, power of two (registers as embeddings) -/

/-- `f := [a > b]` (from `f = 0`), keeping `a` and `b`; `R = (a, b, f, t, u, w)`, scratch `t, u, w` at `0`. -/
def gtFlagW (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 0) (R 3) (R 5)) (.seq (FinalPass.Hash4.wcopyR (R 1) (R 4) (R 5))
    (.seq (decAgainstW (R 3) (R 4) (R 2)) (WM.clear (R 4))))

theorem gtFlagW_spec (R : Fin 6 ↪ Fin nr) (σ : WState ns nr) (hf : σ.val (R 2) = 0) (ht : σ.val (R 3) = 0)
    (hu : σ.val (R 4) = 0) (hw : σ.val (R 5) = 0) (ha : σ.val (R 0) ≤ cap) (hb : σ.val (R 1) ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (gtFlagW R) σ (σ.setv (R 2) (if σ.val (R 1) < σ.val (R 0) then 1 else 0))
      (30 * σ.val (R 0) + 30 * σ.val (R 1) + 20) := by
  have hne : ∀ {i j : Fin 6}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 3) (R 5) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ ht hw ha
  have h2 := FinalPass.Hash4.wcopyR_spec cap (R 1) (R 4) (R 5) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (σ.setv (R 3) (σ.val (R 0))) (by simp [Function.update_apply, hne (show (4 : Fin 6) ≠ 3 by decide), hu])
    (by simp [Function.update_apply, hne (show (5 : Fin 6) ≠ 3 by decide), hw])
    (by simp [Function.update_apply, hne (show (1 : Fin 6) ≠ 3 by decide)]; omega)
  set σ2 := (σ.setv (R 3) (σ.val (R 0))).setv (R 4) ((σ.setv (R 3) (σ.val (R 0))).val (R 1)) with hσ2
  have h3 := decAgainstW_spec cap (R 3) (R 4) (R 2) (hne (by decide)) (hne (by decide)) (hne (by decide)) hcap
    (σ.val (R 0)) σ2 (by simp [σ2, Function.update_apply, hne (show (3 : Fin 6) ≠ 4 by decide)])
    ha (by simp [σ2, Function.update_apply, hne (show (1 : Fin 6) ≠ 3 by decide)]; omega)
    (by simp [σ2, Function.update_apply, hne (show (2 : Fin 6) ≠ 4 by decide),
      hne (show (2 : Fin 6) ≠ 3 by decide), hf])
  have hσ2b : σ2.val (R 4) = σ.val (R 1) := by
    simp [σ2, Function.update_apply, hne (show (1 : Fin 6) ≠ 3 by decide)]
  have hσ2f : σ2.val (R 2) = 0 := by
    simp [σ2, Function.update_apply, hne (show (2 : Fin 6) ≠ 4 by decide), hne (show (2 : Fin 6) ≠ 3 by decide), hf]
  rw [hσ2b, hσ2f] at h3
  have h4 := wclear_spec cap (R 4) (σ.val (R 1) - σ.val (R 0))
    (((σ2.setv (R 3) 0).setv (R 4) (σ.val (R 1) - σ.val (R 0))).setv (R 2)
      (if σ.val (R 1) < σ.val (R 0) then 1 else 0))
    (by simp [Function.update_apply, hne (show (4 : Fin 6) ≠ 2 by decide)])
    (by simp [Function.update_apply, hne (show (4 : Fin 6) ≠ 2 by decide)]; omega)
  have hc2 : (σ.setv (R 3) (σ.val (R 0))).val (R 1) = σ.val (R 1) := by
    simp [Function.update_apply, hne (show (1 : Fin 6) ≠ 3 by decide)]
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  wgen_eq [σ2, ht, hu]

/-- `a := a − b`, keeping `b`; `R = (a, b, t, w)`, scratch at `0`. -/
def subW (R : Fin 4 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 1) (R 2) (R 3)) (.whr (R 2) (.seq (.dec (R 2)) (.dec (R 0))))

theorem subW_spec (R : Fin 4 ↪ Fin nr) (σ : WState ns nr) (ht : σ.val (R 2) = 0) (hw : σ.val (R 3) = 0)
    (ha : σ.val (R 0) ≤ cap) (hb : σ.val (R 1) ≤ cap) :
    WExec cap (subW R) σ (σ.setv (R 0) (σ.val (R 0) - σ.val (R 1))) (30 * σ.val (R 1) + 10) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 1) (R 2) (R 3) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ ht hw hb
  set σ1 := σ.setv (R 2) (σ.val (R 1)) with hσ1
  set m := σ.val (R 1) with hm
  let S : ℕ → WState ns nr := fun k => (σ1.setv (R 2) (m - k)).setv (R 0) (σ.val (R 0) - k)
  have hS0 : S 0 = σ1 := by
    simp only [S, Nat.sub_zero]
    wgen_eq [σ1, hne (show (0 : Fin 4) ≠ 2 by decide)]
  have hloop := UnionMachine.Round.wloop cap (R 2) (.dec (R 0)) 1 m S
    (fun k _ => by simp [S, Function.update_apply, hne (show (2 : Fin 4) ≠ 0 by decide)])
    (by omega)
    (fun k hk => by
      refine WExec.cast cap (WExec.dec (R 0) _ (by simp [S, Function.update_apply]; omega)) ?_ le_rfl
      simp only [S]
      wgen_eq)
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq h1 hloop) ?_ (by omega)
  simp only [S]
  wgen_eq [σ1, ht]

/-- `c := c + a·b`, keeping `a` and `b`; `R = (a, b, c, t, w)`, scratch at `0`. -/
def mulAddW (R : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (R 1) (R 3) (R 4)) (.whr (R 3) (.seq (.dec (R 3)) (addTo (R 0) (R 2) (R 4))))

theorem mulAddW_spec (R : Fin 5 ↪ Fin nr) (σ : WState ns nr) (ht : σ.val (R 3) = 0) (hw : σ.val (R 4) = 0)
    (hb : σ.val (R 1) ≤ cap) (hcap : σ.val (R 2) + σ.val (R 0) * σ.val (R 1) ≤ cap) (ha : σ.val (R 0) ≤ cap) :
    WExec cap (mulAddW R) σ (σ.setv (R 2) (σ.val (R 2) + σ.val (R 0) * σ.val (R 1)))
      (σ.val (R 1) * (18 * σ.val (R 0) + 8) + 18 * σ.val (R 1) + 10) := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 1) (R 3) (R 4) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ ht hw hb
  set σ1 := σ.setv (R 3) (σ.val (R 1)) with hσ1
  set m := σ.val (R 1) with hm
  let S : ℕ → WState ns nr := fun k => (σ1.setv (R 3) (m - k)).setv (R 2) (σ.val (R 2) + k * σ.val (R 0))
  have hS0 : S 0 = σ1 := by
    simp only [S, Nat.sub_zero, Nat.zero_mul, Nat.add_zero]
    wgen_eq [σ1, hne (show (2 : Fin 5) ≠ 3 by decide)]
  have hloop := UnionMachine.Round.wloop cap (R 3) (addTo (R 0) (R 2) (R 4)) (18 * σ.val (R 0) + 3) m S
    (fun k _ => by simp [S, Function.update_apply, hne (show (3 : Fin 5) ≠ 2 by decide)])
    (by omega)
    (fun k hk => by
      have hk1 : (k + 1) * σ.val (R 0) ≤ m * σ.val (R 0) := Nat.mul_le_mul_right _ (by omega)
      have h := addTo_spec cap (R 0) (R 2) (R 4) (hne (by decide)) (hne (by decide)) (hne (by decide))
        ((S k).setv (R 3) (m - k - 1))
        (by simp [S, σ1, Function.update_apply, hne (show (4 : Fin 5) ≠ 3 by decide),
          hne (show (4 : Fin 5) ≠ 2 by decide), hw])
        (by simp [S, σ1, Function.update_apply, hne (show (0 : Fin 5) ≠ 3 by decide),
          hne (show (0 : Fin 5) ≠ 2 by decide)]; omega)
        (by simp [S, σ1, Function.update_apply, hne (show (0 : Fin 5) ≠ 3 by decide),
          hne (show (0 : Fin 5) ≠ 2 by decide), hne (show (2 : Fin 5) ≠ 3 by decide)]; nlinarith)
      refine WExec.cast cap h ?_ (by simp [S, σ1, Function.update_apply, hne (show (0 : Fin 5) ≠ 3 by decide),
        hne (show (0 : Fin 5) ≠ 2 by decide)])
      simp only [S]
      wgen_eq [σ1, hne (show (0 : Fin 5) ≠ 3 by decide), hne (show (0 : Fin 5) ≠ 2 by decide), Nat.succ_mul])
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq h1 hloop) ?_ (by nlinarith)
  simp only [S]
  wgen_eq [σ1, ht, Nat.mul_comm]

/-- `p := 2^s` (from `p = 0`), keeping `s`; `R = (s, p, t, w)`, scratch at `0`. -/
def pow2W (R : Fin 4 ↪ Fin nr) : WM ns nr :=
  .seq (.inc (R 1)) (.seq (FinalPass.Hash4.wcopyR (R 0) (R 2) (R 3)) (.whr (R 2) (.seq (.dec (R 2)) (dbl (R 1) (R 3)))))

theorem pow2W_spec (R : Fin 4 ↪ Fin nr) (σ : WState ns nr) (hp : σ.val (R 1) = 0) (ht : σ.val (R 2) = 0)
    (hw : σ.val (R 3) = 0) (hcap : 2 ^ (σ.val (R 0) + 1) ≤ cap) :
    WExec cap (pow2W R) σ (σ.setv (R 1) (2 ^ σ.val (R 0))) (σ.val (R 0) * (18 * 2 ^ σ.val (R 0) + 7) + 18 * σ.val (R 0) + 20) := by
  have hne : ∀ {i j : Fin 4}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  set m := σ.val (R 0) with hm
  have hm1 : m < 2 ^ (m + 1) := by have := Nat.lt_two_pow_self (n := m + 1); omega
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h0 := WExec.inc (cap := cap) (R 1) σ (by omega)
  set σ0 := σ.setv (R 1) (σ.val (R 1) + 1) with hσ0
  have h1 := FinalPass.Hash4.wcopyR_spec cap (R 0) (R 2) (R 3) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ0 (by simp [σ0, Function.update_apply, hne (show (2 : Fin 4) ≠ 1 by decide), ht])
    (by simp [σ0, Function.update_apply, hne (show (3 : Fin 4) ≠ 1 by decide), hw])
    (by simp [σ0, Function.update_apply, hne (show (0 : Fin 4) ≠ 1 by decide)]; omega)
  set σ1 := σ0.setv (R 2) (σ0.val (R 0)) with hσ1
  let S : ℕ → WState ns nr := fun k => (σ1.setv (R 2) (m - k)).setv (R 1) (2 ^ k)
  have hS0 : S 0 = σ1 := by
    simp only [S, Nat.sub_zero, pow_zero]
    wgen_eq [σ1, σ0, hp, hne (show (0 : Fin 4) ≠ 1 by decide)]
  have hloop := UnionMachine.Round.wloop cap (R 2) (dbl (R 1) (R 3)) (18 * 2 ^ m + 3) m S
    (fun k _ => by simp [S, Function.update_apply, hne (show (2 : Fin 4) ≠ 1 by decide)])
    (by omega)
    (fun k hk => by
      have hk1 : 2 ^ (k + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hk
      have h := dbl_spec cap (R 1) (R 3) (hne (by decide)) ((S k).setv (R 2) (m - k - 1))
        (by simp [S, σ1, σ0, Function.update_apply, hne (show (3 : Fin 4) ≠ 2 by decide),
          hne (show (3 : Fin 4) ≠ 1 by decide), hw])
        (by simp [S, Function.update_apply, hne (show (1 : Fin 4) ≠ 2 by decide)]; rw [pow_succ] at hk1; omega)
      refine WExec.cast cap h ?_ (by
        simp [S, Function.update_apply, hne (show (1 : Fin 4) ≠ 2 by decide)]
        have : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      simp only [S]
      wgen_eq [pow_succ, Nat.mul_comm])
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq h0 (WExec.seq h1 hloop)) ?_ (by simp [σ0]; nlinarith)
  simp only [S]
  wgen_eq [σ1, σ0, ht, hp]

/-! ## Division -/

/-- The division's register maps: `R = (a, b, q, go, g, t, u, w, _)`. -/
def eG : Fin 6 ↪ Fin 9 := ⟨![1, 0, 4, 5, 6, 7], by decide⟩
def eS : Fin 4 ↪ Fin 9 := ⟨![0, 1, 5, 7], by decide⟩

@[simp] theorem eG_apply (i : Fin 6) : eG i = ![1, 0, 4, 5, 6, 7] i := rfl
@[simp] theorem eS_apply (i : Fin 4) : eS i = ![0, 1, 5, 7] i := rfl

/-- `go := [b ≤ a]` (from `go = g = 0`), through `g := [a < b]`, which is `0` again at the end. -/
def decideGo (R : Fin 9 ↪ Fin nr) : WM ns nr :=
  .seq (gtFlagW (eG.trans R)) (.ifr (R 4) (WM.clear (R 4)) (.inc (R 3)))

theorem decideGo_spec (R : Fin 9 ↪ Fin nr) (σ : WState ns nr) (hgo : σ.val (R 3) = 0) (hg : σ.val (R 4) = 0)
    (ht : σ.val (R 5) = 0) (hu : σ.val (R 6) = 0) (hw : σ.val (R 7) = 0) (ha : σ.val (R 0) ≤ cap)
    (hb : σ.val (R 1) ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap (decideGo R) σ (σ.setv (R 3) (if σ.val (R 1) ≤ σ.val (R 0) then 1 else 0))
      (30 * σ.val (R 0) + 30 * σ.val (R 1) + 30) := by
  have hne : ∀ {i j : Fin 9}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h1 := gtFlagW_spec cap (eG.trans R) σ hg ht hu hw hb ha hcap
  simp only [Function.Embedding.trans_apply] at h1
  have e0 : eG 0 = 1 := rfl
  have e1 : eG 1 = 0 := rfl
  have e2 : eG 2 = 4 := rfl
  rw [e0, e1, e2] at h1
  by_cases hab : σ.val (R 0) < σ.val (R 1)
  · rw [if_pos hab] at h1
    have h2 := wclear_spec cap (R 4) 1 (σ.setv (R 4) 1) (by simp) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrT (by simp) h2)) ?_ (by omega)
    rw [if_neg (by omega)]
    wgen_eq [hgo, hg, hne (show (3 : Fin 9) ≠ 4 by decide)]
  · rw [if_neg hab] at h1
    have e : σ.setv (R 4) 0 = σ := by rw [← hg, wsetv_same]
    rw [e] at h1
    have h2 := WExec.inc (cap := cap) (R 3) σ (by omega)
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrF hg h2)) ?_ (by omega)
    rw [if_pos (by omega), hgo]

/-- **Division**: `q += ⌊a/b⌋`, `a := a mod b` (for `b ≥ 1`), `b` kept; `R = (a, b, q, go, g, t, u, w, _)`. -/
def divW (R : Fin 9 ↪ Fin nr) : WM ns nr :=
  .seq (decideGo R) (.whr (R 3) (.seq (.dec (R 3)) (.seq (subW (eS.trans R)) (.seq (.inc (R 2)) (decideGo R)))))

theorem divLoop_spec (R : Fin 9 ↪ Fin nr) (hcap1 : 1 ≤ cap) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val (R 0) = m → 1 ≤ σ.val (R 1) →
      σ.val (R 3) = (if σ.val (R 1) ≤ m then 1 else 0) → σ.val (R 4) = 0 → σ.val (R 5) = 0 → σ.val (R 6) = 0 →
      σ.val (R 7) = 0 → m ≤ cap → σ.val (R 1) ≤ cap → σ.val (R 2) + m / σ.val (R 1) ≤ cap →
      WExec cap (.whr (R 3) (.seq (.dec (R 3)) (.seq (subW (eS.trans R)) (.seq (.inc (R 2)) (decideGo R))))) σ
        (((σ.setv (R 0) (m % σ.val (R 1))).setv (R 2) (σ.val (R 2) + m / σ.val (R 1))).setv (R 3) 0)
        ((m + 1) * (90 * m + 90 * σ.val (R 1) + 60)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro σ ha hb1 hgo hg ht hu hw hmc hbc hqc
    have hne : ∀ {i j : Fin 9}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
    by_cases hmb : (σ.val (R 1)) ≤ m
    · rw [if_pos hmb] at hgo
      have hdiv := Nat.div_eq_sub_div (show 0 < (σ.val (R 1)) by omega) hmb
      have hmod := Nat.mod_eq_sub_mod hmb
      have h1 := WExec.dec (cap := cap) (R 3) σ (by omega)
      set σ1 := σ.setv (R 3) (σ.val (R 3) - 1) with hσ1
      have hs := subW_spec cap (eS.trans R) σ1
        (by simp [σ1, Function.update_apply, hne (show (5 : Fin 9) ≠ 3 by decide), ht])
        (by simp [σ1, Function.update_apply, hne (show (7 : Fin 9) ≠ 3 by decide), hw])
        (by simp [σ1, Function.update_apply, hne (show (0 : Fin 9) ≠ 3 by decide)]; omega)
        (by simp [σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide)]; omega)
      simp only [Function.Embedding.trans_apply] at hs
      have eS0 : eS 0 = 0 := rfl
      have eS1 : eS 1 = 1 := rfl
      rw [eS0, eS1] at hs
      have hσ1a : σ1.val (R 0) = m := by simp [σ1, Function.update_apply, hne (show (0 : Fin 9) ≠ 3 by decide), ha]
      have hσ1b : σ1.val (R 1) = (σ.val (R 1)) := by simp [σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide)]
      rw [hσ1a, hσ1b] at hs
      set σ2 := σ1.setv (R 0) (m - (σ.val (R 1))) with hσ2
      have hi := WExec.inc (cap := cap) (R 2) σ2 (by
        have hq1 : 1 ≤ m / (σ.val (R 1)) := Nat.div_pos hmb (by omega)
        simp [σ2, σ1, Function.update_apply, hne (show (2 : Fin 9) ≠ 0 by decide), hne (show (2 : Fin 9) ≠ 3 by decide)]
        omega)
      set σ3 := σ2.setv (R 2) (σ2.val (R 2) + 1) with hσ3
      have hd := decideGo_spec cap R σ3
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (3 : Fin 9) ≠ 2 by decide),
          hne (show (3 : Fin 9) ≠ 0 by decide), hgo])
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (4 : Fin 9) ≠ 2 by decide),
          hne (show (4 : Fin 9) ≠ 0 by decide), hne (show (4 : Fin 9) ≠ 3 by decide), hg])
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (5 : Fin 9) ≠ 2 by decide),
          hne (show (5 : Fin 9) ≠ 0 by decide), hne (show (5 : Fin 9) ≠ 3 by decide), ht])
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (6 : Fin 9) ≠ 2 by decide),
          hne (show (6 : Fin 9) ≠ 0 by decide), hne (show (6 : Fin 9) ≠ 3 by decide), hu])
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (7 : Fin 9) ≠ 2 by decide),
          hne (show (7 : Fin 9) ≠ 0 by decide), hne (show (7 : Fin 9) ≠ 3 by decide), hw])
        (by simp [σ3, σ2, Function.update_apply, hne (show (0 : Fin 9) ≠ 2 by decide)]; omega)
        (by simp [σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 2 by decide),
          hne (show (1 : Fin 9) ≠ 0 by decide), hne (show (1 : Fin 9) ≠ 3 by decide)]; omega) hcap1
      have hσ3a : σ3.val (R 0) = m - (σ.val (R 1)) := by simp [σ3, σ2, Function.update_apply, hne (show (0 : Fin 9) ≠ 2 by decide)]
      have hσ3b : σ3.val (R 1) = (σ.val (R 1)) := by
        simp [σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 2 by decide),
          hne (show (1 : Fin 9) ≠ 0 by decide), hne (show (1 : Fin 9) ≠ 3 by decide)]
      rw [hσ3a, hσ3b] at hd
      set σ4 := σ3.setv (R 3) (if (σ.val (R 1)) ≤ m - (σ.val (R 1)) then 1 else 0) with hσ4
      have hσ4q : σ4.val (R 2) = σ.val (R 2) + 1 := by
        simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (2 : Fin 9) ≠ 3 by decide),
          hne (show (2 : Fin 9) ≠ 0 by decide)]
      have ihc := ih (m - (σ.val (R 1))) (by omega) σ4
        (by simp [σ4, σ3, σ2, Function.update_apply, hne (show (0 : Fin 9) ≠ 3 by decide),
          hne (show (0 : Fin 9) ≠ 2 by decide)])
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide),
          hne (show (1 : Fin 9) ≠ 2 by decide), hne (show (1 : Fin 9) ≠ 0 by decide)]; omega)
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide),
          hne (show (1 : Fin 9) ≠ 2 by decide), hne (show (1 : Fin 9) ≠ 0 by decide)])
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (4 : Fin 9) ≠ 3 by decide),
          hne (show (4 : Fin 9) ≠ 2 by decide), hne (show (4 : Fin 9) ≠ 0 by decide), hg])
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (5 : Fin 9) ≠ 3 by decide),
          hne (show (5 : Fin 9) ≠ 2 by decide), hne (show (5 : Fin 9) ≠ 0 by decide), ht])
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (6 : Fin 9) ≠ 3 by decide),
          hne (show (6 : Fin 9) ≠ 2 by decide), hne (show (6 : Fin 9) ≠ 0 by decide), hu])
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (7 : Fin 9) ≠ 3 by decide),
          hne (show (7 : Fin 9) ≠ 2 by decide), hne (show (7 : Fin 9) ≠ 0 by decide), hw])
        (by omega)
        (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide),
          hne (show (1 : Fin 9) ≠ 2 by decide), hne (show (1 : Fin 9) ≠ 0 by decide)]; omega)
        (by rw [hσ4q]
            simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide),
              hne (show (1 : Fin 9) ≠ 2 by decide), hne (show (1 : Fin 9) ≠ 0 by decide)]
            rw [hdiv] at hqc; omega)
      have hσ4b : σ4.val (R 1) = (σ.val (R 1)) := by
        simp [σ4, σ3, σ2, σ1, Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide),
          hne (show (1 : Fin 9) ≠ 2 by decide), hne (show (1 : Fin 9) ≠ 0 by decide)]
      rw [hσ4b, hσ4q] at ihc
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq hs (WExec.seq hi hd))) ihc) ?_ ?_
      · rw [hmod, hdiv]
        refine WState.eq rfl rfl ?_ rfl
        funext j
        by_cases h3 : j = R 3
        · subst h3; simp [Function.update_apply]
        · by_cases h2 : j = R 2
          · subst h2; simp [σ4, σ3, σ2, σ1, Function.update_apply, h3, hne (show (2 : Fin 9) ≠ 0 by decide)]; omega
          · by_cases h0 : j = R 0
            · subst h0; simp [Function.update_apply, h3, h2]
            · simp [σ4, σ3, σ2, σ1, Function.update_apply, h3, h2, h0]
      · have hmb' : m - (σ.val (R 1)) + 1 ≤ m := by omega
        nlinarith
    · rw [if_neg hmb] at hgo
      have hdiv : m / (σ.val (R 1)) = 0 := Nat.div_eq_of_lt (by omega)
      have hmod : m % (σ.val (R 1)) = m := Nat.mod_eq_of_lt (by omega)
      have e : ((σ.setv (R 0) (m % (σ.val (R 1)))).setv (R 2) (σ.val (R 2) + m / (σ.val (R 1)))).setv (R 3) 0 = σ := by
        rw [hdiv, hmod, Nat.add_zero, ← ha, ← hgo, wsetv_same, wsetv_same, wsetv_same]
      rw [e]
      exact WExec.mono (WExec.whrF hgo) (by nlinarith)

theorem divW_spec (R : Fin 9 ↪ Fin nr) (σ : WState ns nr) (hb1 : 1 ≤ σ.val (R 1)) (hgo : σ.val (R 3) = 0)
    (hg : σ.val (R 4) = 0) (ht : σ.val (R 5) = 0) (hu : σ.val (R 6) = 0) (hw : σ.val (R 7) = 0)
    (ha : σ.val (R 0) ≤ cap) (hb : σ.val (R 1) ≤ cap) (hq : σ.val (R 2) + σ.val (R 0) ≤ cap) (hcap1 : 1 ≤ cap) :
    WExec cap (divW R) σ ((σ.setv (R 0) (σ.val (R 0) % σ.val (R 1))).setv (R 2)
      (σ.val (R 2) + σ.val (R 0) / σ.val (R 1)))
      ((σ.val (R 0) + 2) * (90 * σ.val (R 0) + 90 * σ.val (R 1) + 60)) := by
  have hne : ∀ {i j : Fin 9}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hdle : σ.val (R 0) / σ.val (R 1) ≤ σ.val (R 0) := Nat.div_le_self _ _
  have h1 := decideGo_spec cap R σ hgo hg ht hu hw ha hb hcap1
  have h2 := divLoop_spec cap R hcap1 (σ.val (R 0)) (σ.setv (R 3) (if σ.val (R 1) ≤ σ.val (R 0) then 1 else 0))
    (by simp [Function.update_apply, hne (show (0 : Fin 9) ≠ 3 by decide)])
    (by simp [Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide)]; omega)
    (by simp [Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide)])
    (by simp [Function.update_apply, hne (show (4 : Fin 9) ≠ 3 by decide), hg])
    (by simp [Function.update_apply, hne (show (5 : Fin 9) ≠ 3 by decide), ht])
    (by simp [Function.update_apply, hne (show (6 : Fin 9) ≠ 3 by decide), hu])
    (by simp [Function.update_apply, hne (show (7 : Fin 9) ≠ 3 by decide), hw])
    ha (by simp [Function.update_apply, hne (show (1 : Fin 9) ≠ 3 by decide)]; omega)
    (by simp [Function.update_apply, hne (show (2 : Fin 9) ≠ 3 by decide), hne (show (1 : Fin 9) ≠ 3 by decide)]
        omega)
  simp only [WState.setv_val, Function.update_apply, if_neg (hne (show (1 : Fin 9) ≠ 3 by decide)),
    if_neg (hne (show (2 : Fin 9) ≠ 3 by decide))] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by nlinarith)
  wgen_eq [hgo]

end NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
