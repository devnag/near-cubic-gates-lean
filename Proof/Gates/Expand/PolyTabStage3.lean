import Proof.Gates.Expand.PolyTabStage2b

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length unaryBody skipPairs unary_loop skipPairs_spec
  read_pre read_enc_bit natWord_getD_one natWord_getD_zero natWord_length off off_le stp_eq)
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wdup wdup_spec)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- `d := d + natBitLength x` and skip the marked field `natWord x` (`f c T` scratch). -/
def lenNat (i : Fin (ns + 1)) (f c d T : Fin nr) : WM ns nr :=
  .seq (.inc f) (.seq (.whr f (unaryBody true i f c)) (.seq (wdup c d T) (skipPairs true i T)))

theorem lenNat_spec (i : Fin (ns + 1)) (f c d T : Fin nr) (hfc : f ≠ c) (hfd : f ≠ d) (hfT : f ≠ T) (hcd : c ≠ d)
    (hcT : c ≠ T) (hdT : d ≠ T) (x : ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ enc true (natWord x) ++ rest) (hsh : σ.sh i = pre.length)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hT : σ.val T = 0) (hcap : σ.val d + natBitLength x + 1 ≤ cap) :
    WExec cap (lenNat i f c d T) σ ((σ.seth i (pre.length + 2 * (natWord x).length)).setv d (σ.val d + natBitLength x))
      (30 * natBitLength x + 30) := by
  have hf1 := WExec.inc (cap := cap) f σ (by omega)
  have hlen := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length x
  have hread : ∀ k, k < (natWord x).length →
      readTapeBit ((σ.setv f (σ.val f + 1)).st i) ((σ.setv f (σ.val f + 1)).sh i + stp true * k + off true) =
        (natWord x).getD k false := by
    intro k hk
    have e : (σ.setv f (σ.val f + 1)).st i = pre ++ (enc true (natWord x) ++ rest) := by
      simp [hst, List.append_assoc]
    rw [e, show (σ.setv f (σ.val f + 1)).sh i = pre.length by simp [hsh], Nat.add_assoc, read_pre]
    exact read_enc_bit true rest _ k hk
  have h2 := unary_loop cap true i f c hfc (by omega) (natBitLength x) (σ.setv f (σ.val f + 1)) (by simp [hf])
    (fun k hk => by rw [hread k (by omega)]; exact natWord_getD_one x k hk)
    (by rw [hread (natBitLength x) (by omega)]; exact natWord_getD_zero x)
    (by simp [Function.update_of_ne (Ne.symm hfc), hc]; omega)
  set σ2 := (((σ.setv f (σ.val f + 1)).seth i ((σ.setv f (σ.val f + 1)).sh i + stp true * natBitLength x +
    stp true)).setv c ((σ.setv f (σ.val f + 1)).val c + natBitLength x)).setv f 0 with hσ2
  have v2c : σ2.val c = natBitLength x := by simp [σ2, Function.update_of_ne (Ne.symm hfc), hc]
  have v2d : σ2.val d = σ.val d := by
    simp [σ2, Function.update_of_ne (Ne.symm hfd), Function.update_of_ne (Ne.symm hcd)]
  have v2T : σ2.val T = 0 := by
    simp [σ2, Function.update_of_ne (Ne.symm hfT), Function.update_of_ne (Ne.symm hcT), hT]
  have h3 := wdup_spec (cap := cap) c d T hcd hcT hdT (natBitLength x) σ2 v2c (by omega) (by rw [v2d]; omega)
    (by rw [v2T]; omega)
  set σ3 := ((σ2.setv c 0).setv d (σ2.val d + natBitLength x)).setv T (σ2.val T + natBitLength x) with hσ3
  have v3T : σ3.val T = natBitLength x := by simp [σ3, v2T]
  have h4 := skipPairs_spec cap true i T (natBitLength x) σ3 v3T (by rw [v3T]; omega)
  refine WExec.cast cap (WExec.seq hf1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hji : j = i
    · subst hji; simp [σ3, σ2, hsh, hlen, stp]; ring
    · simp [σ3, σ2, Function.update_of_ne hji]
  · rfl
  · funext q
    by_cases hq1 : q = f
    · subst hq1; simp [σ3, σ2, Function.update_of_ne hfc, Function.update_of_ne hfd, Function.update_of_ne hfT, hf]
    · by_cases hq2 : q = c
      · subst hq2; simp [σ3, σ2, Function.update_of_ne hcd, Function.update_of_ne hcT, hc]
      · by_cases hq3 : q = d
        · subst hq3; simp [σ3, σ2, Function.update_of_ne hdT, Function.update_of_ne hq1, Function.update_of_ne hq2]
        · by_cases hq4 : q = T
          · subst hq4; simp [σ3, σ2, Function.update_of_ne hq1, Function.update_of_ne hq2,
              Function.update_of_ne hq3, hT]
          · simp [σ3, σ2, Function.update_of_ne hq1, Function.update_of_ne hq2, Function.update_of_ne hq3,
              Function.update_of_ne hq4]
  · rfl

def maxR (a b T1 T2 t : Fin nr) : WMX ns nr :=
  .seq (addR b T1 t) (.seq (addR a T2 t) (.seq (.whr T2 (.seq (WMX.dec T2) (WMX.dec T1)))
    (.seq (addR T1 a t) (.seq (.wm (WM.clear T1)) (.wm (WM.clear b))))))

theorem dec_loop (T1 T2 : Fin nr) (h12 : T1 ≠ T2) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val T2 = n → n ≤ cap → σ.val T1 ≤ cap →
      WXExec cap (.whr T2 (.seq (WMX.dec T2) (WMX.dec T1))) σ ((σ.setv T2 0).setv T1 (σ.val T1 - n)) (8 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv T2 0).setv T1 (σ.val T1 - 0) = σ := by
      apply WState.eq <;> try rfl
      funext q; by_cases h1 : q = T1
      · subst h1; simp
      · by_cases h2 : q = T2
        · subst h2; simp [h1, h0]
        · simp [h1, h2]
    rw [e]; exact WXExec.mono (WXExec.whrF h0) (by omega)
  | n + 1, σ, hn, hc, hc1 => by
    have h21 := Ne.symm h12
    have e1 := WXExec.dec cap T2 σ (by omega)
    have e2 := WXExec.dec cap T1 (σ.setv T2 (σ.val T2 - 1)) (by simp [Function.update_apply, h12]; omega)
    have ih := dec_loop T1 T2 h12 n ((σ.setv T2 (σ.val T2 - 1)).setv T1 ((σ.setv T2 (σ.val T2 - 1)).val T1 - 1))
      (by simp [Function.update_apply, h12, h21]; omega) (by omega)
      (by simp [Function.update_apply, h12, h21]; omega)
    refine WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 e2) ih) ?_ (by omega)
    apply WState.eq <;> try rfl
    funext q; by_cases h1 : q = T1
    · subst h1; simp [Function.update_apply, h12]; omega
    · by_cases h2 : q = T2
      · subst h2; simp [Function.update_apply, h1]
      · simp [Function.update_apply, h1, h2]

theorem maxR_spec (a b T1 T2 t : Fin nr) (hab : a ≠ b) (ha1 : a ≠ T1) (ha2 : a ≠ T2) (hat : a ≠ t) (hb1 : b ≠ T1)
    (hb2 : b ≠ T2) (hbt : b ≠ t) (h12 : T1 ≠ T2) (h1t : T1 ≠ t) (h2t : T2 ≠ t) (σ : WState ns nr) (x y : ℕ)
    (ha : σ.val a = x) (hb : σ.val b = y) (h1 : σ.val T1 = 0) (h2 : σ.val T2 = 0) (ht : σ.val t = 0)
    (hcap : x + y + 1 ≤ cap) :
    WXExec cap (maxR a b T1 T2 t) σ ((σ.setv a (max x y)).setv b 0) (60 * (x + y) + 30) := by
  have hba := Ne.symm hab; have h1a := Ne.symm ha1; have h2a := Ne.symm ha2; have hta := Ne.symm hat
  have h1b := Ne.symm hb1; have h2b := Ne.symm hb2; have htb := Ne.symm hbt; have h21 := Ne.symm h12
  have ht1 := Ne.symm h1t; have ht2 := Ne.symm h2t
  have e1 := addR_spec cap (A := b) (B := T1) (T := t) hb1 hbt h1t σ ht (by rw [h1, hb]; omega)
  rw [h1, hb, zero_add] at e1
  have e2 := addR_spec cap (A := a) (B := T2) (T := t) ha2 hat h2t (σ.setv T1 y)
    (by simp [Function.update_apply, ht1, ht]) (by simp [Function.update_apply, h21, h2, h1a, ha1, ha]; omega)
  have va : (σ.setv T1 y).val a = x := by simp [Function.update_apply, ha1, ha]
  have v2 : (σ.setv T1 y).val T2 = 0 := by simp [Function.update_apply, h21, h2]
  rw [va, v2, zero_add] at e2
  have e3 := dec_loop cap T1 T2 h12 x ((σ.setv T1 y).setv T2 x) (by simp) (by omega)
    (by simp [Function.update_apply, h12]; omega)
  have v3 : ((σ.setv T1 y).setv T2 x).val T1 = y := by simp [Function.update_apply, h12]
  rw [v3] at e3
  have e4 := addR_spec cap (A := T1) (B := a) (T := t) h1a h1t hat ((((σ.setv T1 y).setv T2 x).setv T2 0).setv T1 (y - x))
    (by simp [Function.update_apply, ht1, ht2, ht]) (by simp [Function.update_apply, ha1, ha2, ha]; omega)
  have v4a : ((((σ.setv T1 y).setv T2 x).setv T2 0).setv T1 (y - x)).val a = x := by
    simp [Function.update_apply, ha1, ha2, ha]
  have v41 : ((((σ.setv T1 y).setv T2 x).setv T2 0).setv T1 (y - x)).val T1 = y - x := by simp
  rw [v4a, v41] at e4
  have e5 := wclear_spec (cap := cap) T1 (y - x) (((((σ.setv T1 y).setv T2 x).setv T2 0).setv T1 (y - x)).setv a
    (x + (y - x))) (by simp [Function.update_apply, h1a]) (by simp [Function.update_apply, h1a]; omega)
  have e6 := wclear_spec (cap := cap) b y ((((((σ.setv T1 y).setv T2 x).setv T2 0).setv T1 (y - x)).setv a
    (x + (y - x))).setv T1 0) (by simp [Function.update_apply, hb1, hb2, hba, hb])
    (by simp [Function.update_apply, hb1, hb2, hba, hb]; omega)
  refine WXExec.cast cap (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <|
    WXExec.seq (WXExec.wm e5) (WXExec.wm e6)) ?_ (by omega)
  apply WState.eq <;> try rfl
  funext q
  simp only [WState.setv_val, Function.update_apply]
  by_cases qa : q = a
  · subst qa; simp [hab, ha1, ha2]; omega
  · by_cases qb : q = b
    · subst qb; simp [qa, hb1, hb2]
    · by_cases q1 : q = T1
      · subst q1; simp [qa, qb, h1]
      · by_cases q2 : q = T2
        · subst q2; simp [qa, qb, q1, h2]
        · simp [qa, qb, q1, q2]

end Gen

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

section Steps
variable {σ0 : WState (NSx te qa) NRk} {X : Fin (NSx te qa + 1)} {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ}
  {rest : List Bool}

/-- Measure the next field into `rX j` (scratch `rX 36–38`). -/
def lnF (X : Fin (NSx te qa + 1)) (j : Fin 64) : WX := .wm (lenNat X (rX 36) (rX 37) (rX j) (rX 38))

theorem ps_len (cap : ℕ) (j : Fin 64) (hj : j.val ∉ [36, 37, 38]) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (hi : i < L.length) (h36 : f 36 = 0) (h37 : f 37 = 0) (h38 : f 38 = 0)
    (hcap : f j + natBitLength L[i] + 1 ≤ cap) :
    Runs cap (lnF X j) σ (30 * natBitLength L[i] + 30)
      (PS σ0 X Sx L rest (i + 1) (Function.update f j (f j + natBitLength L[i]))) := by
  have n36 : rX 36 ≠ rX j := fun e => hj (by rw [← rX.injective e]; simp)
  have n37 : rX 37 ≠ rX j := fun e => hj (by rw [← rX.injective e]; simp)
  have n38 : rX 38 ≠ rX j := fun e => hj (by rw [← rX.injective e]; simp)
  have e := lenNat_spec cap X (rX 36) (rX 37) (rX j) (rX 38) (by polyTabNe) n36 (by polyTabNe) n37 (by polyTabNe) (Ne.symm n38)
    L[i] (encN (L.take i)) (encN (L.drop (i + 1)) ++ rest) σ
    (by rw [h.pos.1, encN_split L i hi]; simp [List.append_assoc]) h.pos.2 (by rw [h.x, h36]) (by rw [h.x, h37])
    (by rw [h.x, h38]) (by rw [h.x]; exact hcap)
  rw [h.x] at e
  refine ⟨_, WXExec.wm e, ⟨⟨by simp [h.pos.1], ?_⟩, upd_x h.x j _ (by simp) fun k hk => ?_,
    se_ext h.fr (se_hv σ X _ (rX j) _) (by simp) (by simp [rX_mem])⟩⟩
  · simp only [WState.setv_sh, WState.seth_sh, Function.update_self]
    rw [encN_take_succ L i hi]
  · show Function.update σ.val (rX j) _ (rX k) = σ.val (rX k)
    rw [Function.update_of_ne (rX_ne hk)]

/-- `rX a := max (rX a) (rX b)`, `rX b := 0` (scratch `rX 34`, `rX 35`, `rX 7`). -/
def mxF (a b : Fin 64) : WX := maxR (rX a) (rX b) (rX 34) (rX 35) (rX 7)

theorem ps_max (cap : ℕ) (a b : Fin 64) (hd : [a, b, 34, 35, 7].Nodup) {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (h : PS σ0 X Sx L rest i f σ) (h34 : f 34 = 0) (h35 : f 35 = 0) (h7 : f 7 = 0) (hcap : f a + f b + 1 ≤ cap) :
    Runs cap (mxF a b) σ (60 * (f a + f b) + 30)
      (PS σ0 X Sx L rest i (Function.update (Function.update f a (max (f a) (f b))) b 0)) := by
  have hR : [rX a, rX b, rX 34, rX 35, rX 7].Nodup := by
    have := hd.map rX.injective; simpa using this
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hR
  obtain ⟨⟨hab, ha1, ha2, hat⟩, ⟨hb1, hb2, hbt⟩, ⟨h12, h1t⟩, h2t, -⟩ := hR
  have e := maxR_spec cap (rX a) (rX b) (rX 34) (rX 35) (rX 7) hab ha1 ha2 hat hb1 hb2 hbt h12 h1t h2t σ (f a) (f b)
    (h.x a) (h.x b) (by rw [h.x, h34]) (by rw [h.x, h35]) (by rw [h.x, h7]) hcap
  exact ⟨_, e, ps_reg (ps_reg h a _ rfl) b 0 rfl⟩

end Steps

end NearCubicGates.Close.Expand.PolyTab
