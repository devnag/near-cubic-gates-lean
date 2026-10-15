import Proof.Gates.Succinct.EvalMain
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-! ## Powers -/

def mulStep (X X2 P Y T : Fin nr) : WMX ns nr :=
  .seq (mulR X X2 P Y T) (.seq (.wm (WM.clear X)) (.wm (WM.move Y X)))

theorem mulStep_spec (cap : ℕ) (X X2 P Y T : Fin nr) (hR : [X, X2, P, Y, T].Nodup) (σ : WState ns nr)
    (hX2 : σ.val X2 = 0) (hY : σ.val Y = 0) (hT : σ.val T = 0) (hcap : σ.val X * σ.val P + 2 * σ.val X + 1 ≤ cap) :
    WXExec cap (mulStep X X2 P Y T) σ (σ.setv X (σ.val X * σ.val P))
      (30 * (σ.val X + 1) * (σ.val P + 1)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
  have e1 := mulR_spec cap hR σ hX2 hT (by rw [hY]; omega) (by omega)
  set σ1 := σ.setv Y (σ.val Y + σ.val X * σ.val P) with hσ1
  have e2 := wclear_spec cap X (σ.val X) σ1 (by simp [σ1, Function.update_apply, h3]) (by simp [σ1, Function.update_apply, h3]; omega)
  have e3 := wmove_spec cap Y X (Ne.symm h3) (σ.val X * σ.val P) (σ1.setv X 0)
    (by simp [σ1, Function.update_apply, Ne.symm h3, hY]) (by simp [σ1, Function.update_apply, Ne.symm h3, hY]; omega)
    (by simp [σ1, Function.update_apply, Ne.symm h3, hY]; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))) ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext r; simp only [σ1, WState.setv_val, Function.update_apply]
    by_cases hrX : r = X
    · subst hrX; simp [h3, Ne.symm h3, hY]
    · by_cases hrY : r = Y
      · subst hrY; simp [hrX, hY]
      · simp [hrX, hrY]
  · nlinarith [Nat.zero_le (σ.val X * σ.val P)]

/-- `e` multiplication steps. -/
def powLoop (X X2 P Y T : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | e + 1 => .seq (powLoop X X2 P Y T e) (mulStep X X2 P Y T)

theorem powLoop_spec (cap : ℕ) (X X2 P Y T : Fin nr) (hR : [X, X2, P, Y, T].Nodup) (p E : ℕ)
    (hcap : 3 * (p + 1) ^ E + 1 ≤ cap) :
    ∀ e (σ : WState ns nr), e ≤ E → σ.val X = 1 → σ.val P = p → σ.val X2 = 0 → σ.val Y = 0 → σ.val T = 0 →
      WXExec cap (powLoop X X2 P Y T e) σ (σ.setv X (p ^ e)) (e * (61 * (p + 1) ^ E)) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
  intro e
  induction e with
  | zero =>
    intro σ _ hX _ _ _ _
    rw [pow_zero, ← hX, wsetv_same]; exact WXExec.mono (WXExec.skip cap σ) (by omega)
  | succ e ih =>
    intro σ he hX hP hX2 hY hT
    have e1 := ih σ (by omega) hX hP hX2 hY hT
    have hq : p ^ e ≤ (p + 1) ^ e := Nat.pow_le_pow_left (by omega) e
    have hq2 : (p + 1) ^ e * (p + 1) ≤ (p + 1) ^ E := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hqE : (p + 1) ^ e ≤ (p + 1) ^ E := Nat.pow_le_pow_right (by omega) (by omega)
    have hQ1 : 1 ≤ (p + 1) ^ E := Nat.one_le_pow _ _ (by omega)
    have hpe1 : p ^ e * p + 2 * p ^ e + 1 ≤ 3 * (p + 1) ^ E := by
      have : p ^ e * p + 2 * p ^ e ≤ 2 * ((p + 1) ^ e * (p + 1)) :=
        calc p ^ e * p + 2 * p ^ e = p ^ e * (p + 2) := by ring
          _ ≤ (p + 1) ^ e * (p + 2) := Nat.mul_le_mul_right _ hq
          _ ≤ (p + 1) ^ e * (2 * (p + 1)) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * ((p + 1) ^ e * (p + 1)) := by ring
      omega
    have e2 := mulStep_spec cap X X2 P Y T hR (σ.setv X (p ^ e)) (by simp [Function.update_apply, Ne.symm h1, hX2])
      (by simp [Function.update_apply, Ne.symm h3, hY]) (by simp [Function.update_apply, Ne.symm h4, hT])
      (by simp [Function.update_apply, Ne.symm h2, hP]; omega)
    refine WXExec.cast cap (WXExec.seq e1 e2) ?_ ?_
    · simp [Function.update_apply, Ne.symm h2, hP, wsetv_setv, pow_succ]
    · have hv1 : (σ.setv X (p ^ e)).val X = p ^ e := by simp
      have hv2 : (σ.setv X (p ^ e)).val P = p := by simp [Function.update_apply, Ne.symm h2, hP]
      rw [hv1, hv2]
      have hA : 30 * (p ^ e + 1) * (p + 1) ≤ 60 * (p + 1) ^ E := by
        have h1' : 1 ≤ (p + 1) ^ e := Nat.one_le_pow _ _ (by omega)
        have : (p ^ e + 1) * (p + 1) ≤ 2 * ((p + 1) ^ e * (p + 1)) :=
          calc (p ^ e + 1) * (p + 1) ≤ ((p + 1) ^ e + (p + 1) ^ e) * (p + 1) :=
                Nat.mul_le_mul_right _ (by omega)
            _ = 2 * ((p + 1) ^ e * (p + 1)) := by ring
        have e30 : 30 * (p ^ e + 1) * (p + 1) = 30 * ((p ^ e + 1) * (p + 1)) := by ring
        rw [e30]; omega
      generalize 30 * (p ^ e + 1) * (p + 1) = A at hA ⊢
      generalize (p + 1) ^ E = Q at hA hQ1 ⊢
      have hm : (e + 1) * (61 * Q) = e * (61 * Q) + 61 * Q := by ring
      rw [hm]
      generalize e * (61 * Q) = M
      omega

/-- `X := p^e` from `X = 0`. -/
def powW (X X2 P Y T : Fin nr) (e : ℕ) : WMX ns nr := .seq (WMX.inc X) (powLoop X X2 P Y T e)

/-- **Powers** (paper lem:succinct-verifier, stage (1): `ν^{G+2}`; stage (4): `N^{k+2}`). -/
theorem powW_spec (cap : ℕ) (X X2 P Y T : Fin nr) (hR : [X, X2, P, Y, T].Nodup) (p e : ℕ) (σ : WState ns nr)
    (hX : σ.val X = 0) (hP : σ.val P = p) (hX2 : σ.val X2 = 0) (hY : σ.val Y = 0) (hT : σ.val T = 0)
    (hcap : 3 * (p + 1) ^ e + 1 ≤ cap) :
    WXExec cap (powW X X2 P Y T e) σ (σ.setv X (p ^ e)) (e * (61 * (p + 1) ^ e) + 4) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR'
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hR'
  have h1' : 1 ≤ (p + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have e1 := WXExec.inc cap X σ (by omega)
  have e2 := powLoop_spec cap X X2 P Y T hR p e hcap e (σ.setv X (σ.val X + 1)) le_rfl (by simp [hX])
    (by simp [Function.update_apply, Ne.symm h2, hP]) (by simp [Function.update_apply, Ne.symm h1, hX2])
    (by simp [Function.update_apply, Ne.symm h3, hY]) (by simp [Function.update_apply, Ne.symm h4, hT])
  refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by omega)
  simp [wsetv_setv]

/-! ## Comparison -/

/-- `F := [A ≤ B]` from `F = 0` (`A`, `B` kept; `G`, `H`, `Z`, `T` scratch). -/
def leW (A B G H Z F T : Fin nr) : WMX ns nr :=
  .seq (.wm (addTo A G T)) (.seq (.wm (addTo B H T)) (.seq (.wm (.whr G (.seq (.dec G) (.ifr H (.dec H) (WM.setF Z)))))
    (.seq (.wm (WM.clear H)) (.wm (.ifr Z (.dec Z) (.inc F))))))

/-- **Comparison** (paper lem:succinct-verifier, stage (1): is `(ν+1)^{G+2} ≤ n`?). -/
theorem leW_spec (cap : ℕ) (A B G H Z F T : Fin nr) (hR : [A, B, G, H, Z, F, T].Nodup) (σ : WState ns nr)
    (hG : σ.val G = 0) (hH : σ.val H = 0) (hZ : σ.val Z = 0) (hF : σ.val F = 0) (hT : σ.val T = 0)
    (hcap : σ.val A + σ.val B + 2 ≤ cap) :
    WXExec cap (leW A B G H Z F T) σ (σ.setv F (if σ.val A ≤ σ.val B then 1 else 0))
      (30 * (σ.val A + σ.val B) + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨g1, g2, g3, g4⟩, ⟨h1, h2, h3⟩, ⟨z1, z2⟩, f1⟩ := hR
  have n1 := Ne.symm a1; have n2 := Ne.symm a2; have n3 := Ne.symm a3; have n4 := Ne.symm a4
  have n5 := Ne.symm a5; have n6 := Ne.symm a6; have n7 := Ne.symm b1; have n8 := Ne.symm b2
  have n9 := Ne.symm b3; have n10 := Ne.symm b4; have n11 := Ne.symm b5; have n12 := Ne.symm g1
  have n13 := Ne.symm g2; have n14 := Ne.symm g3; have n15 := Ne.symm g4; have n16 := Ne.symm h1
  have n17 := Ne.symm h2; have n18 := Ne.symm h3; have n19 := Ne.symm z1; have n20 := Ne.symm z2
  have n21 := Ne.symm f1
  generalize ha : σ.val A = a at hcap ⊢
  generalize hb : σ.val B = b at hcap ⊢
  have e1 := addTo_spec cap A G T a2 a6 g4 σ hT (by omega) (by omega)
  rw [ha, hG, Nat.zero_add] at e1
  have e2 := addTo_spec cap B H T b2 b5 h3 (σ.setv G a) (by simp [Function.update_apply, n15, hT])
    (by simp [Function.update_apply, b1, hb]; omega) (by simp [Function.update_apply, b1, g1, n12, hH, hb]; omega)
  have hv : ((σ.setv G a).setv H ((σ.setv G a).val H + (σ.setv G a).val B)) =
      (σ.setv G a).setv H b := by simp [Function.update_apply, b1, n12, hH, hb]
  rw [hv, show (σ.setv G a).val B = b by simp [Function.update_apply, b1, hb]] at e2
  have e3 := guard_step cap G H Z g1 g2 h1 ((σ.setv G a).setv H b) a b (by simp [Function.update_apply, g1])
    (by simp) (by simp [Function.update_apply, n16, n13, hZ]) (by omega)
  have e4 := wclear_spec cap H (b - a) ((((σ.setv G a).setv H b).setv G 0).setv H (b - a) |>.setv Z
    (if b < a then 1 else 0)) (by simp [Function.update_apply, h1]) (by simp [Function.update_apply, h1]; omega)
  set σ4 := ((((((σ.setv G a).setv H b).setv G 0).setv H (b - a)).setv Z (if b < a then 1 else 0)).setv H 0)
    with hσ4
  have hσ4Z : σ4.val Z = if b < a then 1 else 0 := by simp [σ4, Function.update_apply, n16]
  have hσ4F : σ4.val F = 0 := by simp [σ4, Function.update_apply, n17, n19, n14, hF]
  have e5 : WExec cap (.ifr Z (.dec Z) (.inc F)) σ4 (σ.setv F (if a ≤ b then 1 else 0)) 4 := by
    by_cases hab : b < a
    · have := WExec.dec (cap := cap) Z σ4 (by rw [hσ4Z, if_pos hab]; omega)
      refine WExec.mono (WExec.cast cap (WExec.ifrT (by rw [hσ4Z, if_pos hab]; omega) this) ?_ le_rfl) (by omega)
      rw [hσ4Z, if_pos hab, if_neg (by omega)]
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ4, WState.setv_val, Function.update_apply]
      by_cases hrZ : r = Z
      · subst hrZ; simp [z1, hZ]
      · by_cases hrH : r = H
        · subst hrH; simp [hrZ, hH, n17]
        · by_cases hrG : r = G
          · subst hrG; simp [hrZ, hrH, hG, n14]
          · by_cases hrF : r = F
            · subst hrF; simp [hrZ, hrH, hrG, hF]
            · simp [hrZ, hrH, hrG, hrF]
    · have := WExec.inc (cap := cap) F σ4 (by rw [hσ4F]; omega)
      refine WExec.mono (WExec.cast cap (WExec.ifrF (by rw [hσ4Z, if_neg hab]) this) ?_ le_rfl) (by omega)
      rw [hσ4F, if_pos (by omega)]
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ4, WState.setv_val, Function.update_apply]
      by_cases hrF : r = F
      · subst hrF; simp
      · by_cases hrZ : r = Z
        · subst hrZ; simp [hrF, hZ, hab]
        · by_cases hrH : r = H
          · subst hrH; simp [hrF, hrZ, hH]
          · by_cases hrG : r = G
            · subst hrG; simp [hrF, hrZ, hrH, hG]
            · simp [hrF, hrZ, hrH, hrG]
  refine WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.wm e5))))) ?_
  omega

/-! ## Halving counts -/

/-- The number of halvings of `x` down to `0` (paper lem:succinct-verifier: the guard bounds of stages (2)–(3)). -/
def hc : ℕ → ℕ
  | 0 => 0
  | x + 1 => hc ((x + 1) / 2) + 1
decreasing_by omega

theorem hc_succ (x : ℕ) : hc (x + 1) = hc ((x + 1) / 2) + 1 := by rw [hc]

theorem lt_two_pow_hc : ∀ x, x < 2 ^ hc x
  | 0 => by simp [hc]
  | x + 1 => by
    rw [hc_succ, pow_succ]
    have h := lt_two_pow_hc ((x + 1) / 2)
    generalize 2 ^ hc ((x + 1) / 2) = P at h ⊢
    omega

theorem two_pow_hc_le_two_mul : ∀ x, 1 ≤ x → 2 ^ hc x ≤ 2 * x
  | 0 => by simp
  | x + 1 => by
    intro _
    rw [hc_succ, pow_succ]
    rcases Nat.eq_zero_or_pos ((x + 1) / 2) with h0 | hpos
    · rw [h0]; simp [hc]
    · have h := two_pow_hc_le_two_mul ((x + 1) / 2) hpos
      generalize 2 ^ hc ((x + 1) / 2) = P at h ⊢
      omega

theorem two_pow_hc_le (x : ℕ) : 2 ^ hc x ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [hc]
  · have := two_pow_hc_le_two_mul x hx; omega

theorem hc_le (x : ℕ) : hc x ≤ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [hc]
  · have h1 := two_pow_hc_le_two_mul x hx
    rcases Nat.eq_zero_or_pos (hc x) with h0 | hp
    · omega
    · have h2 : hc x - 1 < 2 ^ (hc x - 1) := Nat.lt_two_pow_self
      have h3 : 2 ^ hc x = 2 ^ (hc x - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      omega

/-- `X := X / 2` (`H` scratch). -/
def halveW (X H : Fin nr) : WM ns nr :=
  .seq (.whr X (.seq (.dec X) (.ifr X (.seq (.dec X) (.inc H)) .skip))) (WM.move H X)

theorem halveLoop_spec (cap : ℕ) (X H : Fin nr) (hXH : X ≠ H) :
    ∀ x (σ : WState ns nr), σ.val X = x → σ.val H + x / 2 ≤ cap → x ≤ cap →
      WExec cap (.whr X (.seq (.dec X) (.ifr X (.seq (.dec X) (.inc H)) .skip))) σ
        ((σ.setv X 0).setv H (σ.val H + x / 2)) (5 * x + 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro σ hx hc1 hc2
    rcases x with _ | _ | x
    · have e : (σ.setv X 0).setv H (σ.val H + 0 / 2) = σ := by
        rw [Nat.zero_div, Nat.add_zero, ← hx, wsetv_same, wsetv_same]
      rw [e]; exact WExec.whrF hx
    · have e1 := WExec.dec (cap := cap) X σ (by omega)
      have h0 : (σ.setv X (σ.val X - 1)).val X = 0 := by simp [hx]
      have e2 := WExec.whrF (cap := cap) (P := .seq (.dec X) (.ifr X (.seq (.dec X) (.inc H)) .skip)) h0
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.ifrF h0 (WExec.skip _))) e2) ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      by_cases hrH : r = H
      · subst hrH; simp [Ne.symm hXH]
      · by_cases hrX : r = X
        · subst hrX; simp [hrH, hx]
        · simp [hrH, hrX]
    · have e1 := WExec.dec (cap := cap) X σ (by omega)
      set σ1 := σ.setv X (σ.val X - 1) with hσ1
      have h1 : σ1.val X = x + 1 := by simp [σ1, hx]
      have e2 := WExec.dec (cap := cap) X σ1 (by omega)
      set σ2 := σ1.setv X (σ1.val X - 1) with hσ2
      have e3 := WExec.inc (cap := cap) H σ2 (by
        simp [σ2, σ1, Function.update_apply, Ne.symm hXH]
        have : (x + 2) / 2 = x / 2 + 1 := by omega
        omega)
      set σ3 := σ2.setv H (σ2.val H + 1) with hσ3
      have ih' := ih x (by omega) σ3 (by simp [σ3, σ2, σ1, Function.update_apply, hXH, hx])
        (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hXH]; have : (x + 2) / 2 = x / 2 + 1 := by omega
            omega) (by omega)
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.ifrT (by omega) (WExec.seq e2 e3))) ih') ?_
        (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [σ3, σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases hrH : r = H
      · subst hrH; simp [Ne.symm hXH]; omega
      · by_cases hrX : r = X
        · subst hrX; simp [hrH]
        · simp [hrH, hrX]

theorem halveW_spec (cap : ℕ) (X H : Fin nr) (hXH : X ≠ H) (σ : WState ns nr) (hH : σ.val H = 0)
    (hcap : σ.val X ≤ cap) :
    WExec cap (halveW X H) σ (σ.setv X (σ.val X / 2)) (13 * σ.val X + 3) := by
  have e1 := halveLoop_spec cap X H hXH (σ.val X) σ rfl (by rw [hH]; omega) hcap
  have e2 := wmove_spec cap H X (Ne.symm hXH) (σ.val X / 2) ((σ.setv X 0).setv H (σ.val H + σ.val X / 2))
    (by simp [hH]) (by simp [hH]; omega) (by simp [Function.update_apply, hXH, hH]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r; simp only [WState.setv_val, Function.update_apply]
  by_cases hrX : r = X
  · subst hrX; simp [hXH, hH]
  · by_cases hrH : r = H
    · subst hrH; simp [hrX, hH]
    · simp [hrX, hrH]

/-- `R += hc X`, `X := 0` (`H` scratch). -/
def hcW (X R H : Fin nr) : WM ns nr := .whr X (.seq (halveW X H) (.inc R))

/-- **The halving count** (paper lem:succinct-verifier: the guard bounds). -/
theorem hcW_spec (cap : ℕ) (X R H : Fin nr) (hXR : X ≠ R) (hXH : X ≠ H) (hRH : R ≠ H) :
    ∀ x (σ : WState ns nr), σ.val X = x → σ.val H = 0 → σ.val R + hc x < cap → x ≤ cap →
      WExec cap (hcW X R H) σ ((σ.setv X 0).setv R (σ.val R + hc x)) (30 * x + 20 * hc x + 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro σ hx hH hc1 hc2
    rcases x with _ | x
    · have e : (σ.setv X 0).setv R (σ.val R + hc 0) = σ := by
        rw [show hc 0 = 0 by simp [hc], Nat.add_zero, ← hx, wsetv_same, wsetv_same]
      rw [e]; exact WExec.mono (WExec.whrF hx) (by omega)
    · have hhc : hc (x + 1) = hc ((x + 1) / 2) + 1 := hc_succ x
      have e1 := halveW_spec cap X H hXH σ hH (by omega)
      have e2 := WExec.inc (cap := cap) R (σ.setv X (σ.val X / 2)) (by
        simp [Function.update_apply, Ne.symm hXR]; omega)
      set σ2 := (σ.setv X (σ.val X / 2)).setv R ((σ.setv X (σ.val X / 2)).val R + 1) with hσ2
      have ih' := ih ((x + 1) / 2) (by omega) σ2 (by simp [σ2, Function.update_apply, hXR, hx])
        (by simp [σ2, Function.update_apply, Ne.symm hRH, Ne.symm hXH, hH])
        (by simp [σ2, Function.update_apply, Ne.symm hXR]; omega) (by omega)
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih') ?_ ?_
      · refine WState.eq rfl rfl ?_ rfl
        funext r; simp only [σ2, WState.setv_val, Function.update_apply]
        by_cases hrR : r = R
        · subst hrR; simp [Ne.symm hXR]; omega
        · by_cases hrX : r = X
          · subst hrX; simp [hrR]
          · simp [hrR, hrX]
      · rw [hx, hhc]; omega

/-! ## Powers of two -/

def pow2W (N NU NU2 T : Fin nr) : WMX ns nr := .seq (WMX.inc N) (repK NU NU2 (.wm (dbl N T)))

/-- **Powers of two** (paper lem:succinct-verifier, stage (3): `N = 2^ν`). -/
theorem pow2W_spec (cap : ℕ) (N NU NU2 T : Fin nr) (hR : [N, NU, NU2, T].Nodup) (σ : WState ns nr)
    (hN : σ.val N = 0) (hNU2 : σ.val NU2 = 0) (hT : σ.val T = 0) (hcap : 2 * 2 ^ σ.val NU + 2 * σ.val NU + 1 ≤ cap) :
    WXExec cap (pow2W N NU NU2 T) σ (σ.setv N (2 ^ σ.val NU)) (σ.val NU * (18 * 2 ^ σ.val NU + 11) + 7 * σ.val NU + 7) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨n1, n2, n3⟩, ⟨u1, u2⟩, v1⟩ := hR
  set ν := σ.val NU with hν
  have e1 := WXExec.inc cap N σ (by omega)
  have hpow : ∀ k ≤ ν, 2 ^ k ≤ 2 ^ ν := fun k hk => Nat.pow_le_pow_right (by norm_num) hk
  have e2 := Runs.repE (cap := cap) (K := NU) (K2 := NU2) (body := .wm (dbl N T)) u1 (18 * 2 ^ ν + 3) ν
    (fun k => σ.setv N (2 ^ k)) (by omega) (fun k => by simp [Function.update_apply, Ne.symm n1])
    (fun k => by simp [Function.update_apply, Ne.symm n2])
    (fun k hk v1' v2' => by
      have := dbl_spec cap N T n3 (((σ.setv N (2 ^ k)).setv NU v1').setv NU2 v2')
        (by simp [Function.update_apply, Ne.symm n3, Ne.symm u2, Ne.symm v1, hT])
        (by simp [Function.update_apply, n1, n2]; have := hpow (k + 1) hk; rw [pow_succ] at this; omega)
      refine WXExec.wm (WExec.cast cap this ?_ ?_)
      · refine WState.eq rfl rfl ?_ rfl
        funext r; simp only [WState.setv_val, Function.update_apply]
        by_cases hrN : r = N
        · subst hrN; simp [n1, n2, pow_succ]; ring
        · simp [hrN]
      · simp [Function.update_apply, n1, n2]; have := hpow k hk.le; omega)
    (by simp [Function.update_apply, Ne.symm n1]; rfl) (by simp [Function.update_apply, Ne.symm n2, hNU2])
  have e0 : σ.setv N (σ.val N + 1) = σ.setv N (2 ^ 0) := by simp [hN]
  rw [e0] at e1
  refine WXExec.cast cap (WXExec.seq e1 e2) (by simp [wsetv_setv]) (by ring_nf; omega)

end NearCubicGates.Close.Succinct
