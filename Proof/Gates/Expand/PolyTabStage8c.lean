import Proof.Gates.Expand.PolyTabStage8b

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- Append `U 4` to the occurrence table. -/
theorem tsg_append {Wb : ℕ} {inp : List Bool} {hd : ℕ} {TB : List Bool} {σA : WSt} {outV : List Bool} (cap : ℕ)
    (x : ℕ) (hx : x < 2 ^ Wb) (τ : WSt) (h : TSg Wb inp hd TB σA outV 0 (· = x) τ)
    (hcap : outV.length + 2 * Wb + 2 ≤ cap) :
    Runs cap (appendRecX (U0 4) (sS 4) (rX 29) (rX 20)) τ (40 * Wb + 11)
      (fun ρ => TS Wb inp hd TB σA (outV ++ frame (binary Wb x)) ρ ∧
        ∀ j : Fin 64, j ≠ 20 → ρ.val (rX j) = τ.val (rX j)) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq⟩, hO, h0, h1, h9, h3, h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := h
  have hN4 := hv.num 4 (by decide)
  rw [hq] at hN4
  have hbl : (binary Wb x).length = Wb := binary_length _ _
  have e := appendRec_spec cap (Src := U0 4) (O := sS 4) (CS := rX 29) (CO := rX 20) (ne4 4) (by polyTabNe) τ
    (binary Wb x) [] outV [] (by rw [hN4.1, frame_eq_frameP]) hN4.2 h29 hO (by rw [hbl]; omega)
  refine ⟨_, WXExec.mono (WXExec.wm e) (by rw [hbl]), ⟨⟨v, evv_out hv _ ne4 _ _ 20 (by decide) _, hv8, hv9, trivial⟩,
    ⟨by simp [overlay], by simp, by simp⟩, by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4],
    by simp [h6], by simp [h5], by simp [h29], by simp [h7], ?_, ?_, ?_⟩, fun j hj => by
      simp [Function.update_of_ne (rX_ne hj)]⟩
  · simp [Function.update_of_ne (show sS 3 ≠ sS 4 by polyTabNe), htb]
  · simp [Function.update_of_ne (show sS 3 ≠ sS 4 by polyTabNe), htbh]
  · refine se_ext (S' := [sS 4]) (R' := [rX 20]) hfr ⟨fun y hy => ?_, fun q hq => ?_, rfl⟩ (by simp)
      (fun q hq => ?_)
    · simp only [List.mem_singleton] at hy; simp [Function.update_of_ne hy]
    · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]
    · simp only [List.mem_singleton] at hq; subst hq; unfold RVL; simp

/-! ## Register steps inside the table phase -/

/-- All PolyTab registers outside `S` keep their values. -/
def KeepS (S : List ℕ) (τ ρ : WSt) : Prop := ∀ j : Fin 64, j.val ∉ S → ρ.val (rX j) = τ.val (rX j)

theorem KeepS.trans {S S' : List ℕ} {τ ρ μ : WSt} (h1 : KeepS S τ ρ) (h2 : KeepS S' ρ μ) (hS : ∀ x ∈ S', x ∈ S) :
    KeepS S τ μ := fun j hj => (h2 j (fun hm => hj (hS _ hm))).trans (h1 j hj)

theorem keepS_setv (τ : WSt) (j : Fin 64) (y : ℕ) (S : List ℕ) (hj : j.val ∈ S) : KeepS S τ (τ.setv (rX j) y) :=
  fun i hi => by
    have hij : i ≠ j := fun e => hi (by rw [e]; exact hj)
    simp [Function.update_of_ne (rX_ne hij)]

section RegSteps
variable {Wb : ℕ} {inp : List Bool} {hd : ℕ} {TB : List Bool} {σA : WState (NSx te qa) NRk} {outV : List Bool}

theorem ts_inc (cap : ℕ) (j : Fin 64) (hj : j.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26]) (x : ℕ) (τ : WSt)
    (h : TS Wb inp hd TB σA outV τ) (hx : τ.val (rX j) = x) (hcap : x < cap) :
    Runs cap (WMX.inc (rX j)) τ 3 (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX j) = x + 1 ∧ KeepS [j.val] τ ρ) := by
  have e := WXExec.inc cap (rX j) τ (by rw [hx]; exact hcap)
  rw [hx] at e
  exact ⟨_, e, ts_reg h j hj _, by simp, keepS_setv τ j _ _ (by simp)⟩

theorem ts_dec (cap : ℕ) (j : Fin 64) (hj : j.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26]) (x : ℕ) (τ : WSt)
    (h : TS Wb inp hd TB σA outV τ) (hx : τ.val (rX j) = x) (hcap : x ≤ cap) :
    Runs cap (WMX.dec (rX j)) τ 1 (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX j) = x - 1 ∧ KeepS [j.val] τ ρ) := by
  have e := WXExec.dec cap (rX j) τ (by rw [hx]; exact hcap)
  rw [hx] at e
  exact ⟨_, e, ts_reg h j hj _, by simp, keepS_setv τ j _ _ (by simp)⟩

theorem ts_clr (cap : ℕ) (j : Fin 64) (hj : j.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26]) (x : ℕ) (τ : WSt)
    (h : TS Wb inp hd TB σA outV τ) (hx : τ.val (rX j) = x) (hcap : x ≤ cap) :
    Runs cap (.wm (WM.clear (rX j))) τ (3 * x + 1)
      (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX j) = 0 ∧ KeepS [j.val] τ ρ) := by
  have e := wclear_spec (cap := cap) (rX j) x τ hx (by rw [hx]; exact hcap)
  exact ⟨_, WXExec.wm e, ts_reg h j hj _, by simp, keepS_setv τ j _ _ (by simp)⟩

/-- `rX a += rX b`. -/
theorem ts_add (cap : ℕ) (a b : Fin 64) (ha : a.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26]) (hab : a ≠ b)
    (hb7 : b ≠ 7) (x y : ℕ) (τ : WSt) (h : TS Wb inp hd TB σA outV τ) (hx : τ.val (rX a) = x) (hy : τ.val (rX b) = y)
    (hcap : x + y ≤ cap) :
    Runs cap (addR (rX b) (rX a) (rX 7)) τ (18 * y + 3)
      (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX a) = x + y ∧ KeepS [a.val] τ ρ) := by
  have ha7 : a ≠ 7 := by intro e; subst e; simp at ha
  have e := addR_spec cap (A := rX b) (B := rX a) (T := rX 7) (rX_ne (Ne.symm hab)) (rX_ne hb7) (rX_ne ha7) τ h.z7
    (by rw [hx, hy]; exact hcap)
  rw [hx, hy] at e
  exact ⟨_, e, ts_reg h a ha _, by simp, keepS_setv τ a _ _ (by simp)⟩

/-- `rX c += rX a · rX b` (`rX a2` scratch `0`). -/
theorem ts_mul (cap : ℕ) (a a2 b c : Fin 64) (hc : c.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26])
    (hd' : [a, a2, b, c, 7].Nodup) (x y z : ℕ) (τ : WSt) (h : TS Wb inp hd TB σA outV τ) (hx : τ.val (rX a) = x)
    (hy : τ.val (rX b) = y) (hz : τ.val (rX c) = z) (h2 : τ.val (rX a2) = 0) (hcap : z + x * y ≤ cap)
    (hcapA : 2 * x ≤ cap) :
    Runs cap (mulR (rX a) (rX a2) (rX b) (rX c) (rX 7)) τ (x * (18 * y + 3 + 8) + 7 * x + 3)
      (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX c) = z + x * y ∧ KeepS [c.val] τ ρ) := by
  have hR : [rX a, rX a2, rX b, rX c, rX 7].Nodup := by
    have := List.Nodup.map rX.injective hd'; simpa using this
  have e := mulR_spec cap hR τ h2 h.z7 (by rw [hz, hx, hy]; exact hcap) (by rw [hx]; exact hcapA)
  rw [hz, hx, hy] at e
  exact ⟨_, e, ts_reg h c hc _, by simp, keepS_setv τ c _ _ (by simp)⟩

end RegSteps

def vA1 : WX :=
  .seq (fetchR 43 16) <| .seq (WMX.inc (rX 43)) <| .seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX 43) (rX 9)) <|
  .seq (appendRecX (U0 4) (sS 4) (rX 29) (rX 20)) (WMX.inc (rX 43))

def vA1Cost (Wb N : ℕ) : ℕ := fetchCost Wb N N + 1 + (3 + 1 + (gaCost Wb N + 1 + (40 * Wb + 11 + 1 + 3)))

theorem vA1_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (v : Fin r.V) (hBn : r.n < 2 ^ Wb) (hGW : r.G < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h43 : τ.val (rX 43) = pV r + 1 + 2 * v.val) (h16 : τ.val (rX 16) = 0)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length + 4 * Wb + 40 ≤ cap) :
    Runs cap vA1 τ (vA1Cost Wb (preN r).length)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ frame (binary Wb (if (r.role v).reference then 1 else 0))) ρ ∧ ρ.val (rX 43) = pV r + 1 + 2 * v.val + 2 ∧
        ρ.val (rX 16) = (r.role v).gate.val ∧ KeepS [5, 20, 16, 43] τ ρ) := by
  obtain ⟨hg, hrf⟩ := preN_role r v
  have hrf1 : (if (r.role v).reference then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hlenP := preN_length r
  have hgG := (r.role v).gate.isLt
  have hvV := v.isLt
  have hG3 : r.G ≤ r.G * (2 * r.n + 3) := Nat.le_mul_of_pos_right _ (by omega)
  have hk2 := Nat.two_pow_pos r.k
  have hpVe : pV r = 5 + r.G * (2 * r.n + 3) + r.k + 1 + r.s + 1 + 2 ^ r.k + 1 := rfl
  obtain ⟨τ1, e1, h1, v1_16, k1⟩ := fetchR_spec cap Wb r hW inp hd σA outV 43 16 (by decide) (by decide)
    (by unfold RVL; simp) (by decide) _ _ hg (by omega) τ hI h43 h16 (by omega)
  have e1' := WXExec.mono e1 (fetchCost_mono Wb (preN r).length (show (r.role v).gate.val ≤ (preN r).length by omega))
  have v1_43 : τ1.val (rX 43) = pV r + 1 + 2 * v.val := by rw [k1 43 (by decide) (by decide), h43]
  obtain ⟨τ2, e2, h2, v2_43, k2⟩ := ts_inc cap 43 (by simp) _ τ1 h1 v1_43 (by omega)
  obtain ⟨τ3, e3, h3, v3_43, k3⟩ := tsg_getAt cap Wb r hW inp hd σA outV 0 (fun _ => True) 43 (by decide)
    (pV r + 1 + 2 * v.val + 1) _ hrf (lt_of_le_of_lt hrf1 (Nat.one_lt_two_pow (by omega))) τ2 h2 v2_43 (by omega)
  obtain ⟨τ4, e4, h4, k4⟩ := tsg_append cap _ (lt_of_le_of_lt hrf1 (Nat.one_lt_two_pow (by omega))) τ3 h3 (by omega)
  have v4_43 : τ4.val (rX 43) = pV r + 1 + 2 * v.val + 1 := by rw [k4 43 (by decide), v3_43]
  obtain ⟨τ5, e5, h5, v5_43, k5⟩ := ts_inc cap 43 (by simp) _ τ4 h4 v4_43 (by omega)
  refine ⟨τ5, WXExec.mono (WXExec.seq e1' <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 e5)
    (by unfold vA1Cost; omega), h5, by rw [v5_43], ?_, fun j hj => ?_⟩
  · rw [k5 16 (by decide), k4 16 (by decide), k3 16 (by decide) (by decide), k2 16 (by decide), v1_16]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    have j5 : j ≠ 5 := fun e => hj.1 (by rw [e]; rfl)
    have j20 : j ≠ 20 := fun e => hj.2.1 (by rw [e]; rfl)
    have j16 : j ≠ 16 := fun e => hj.2.2.1 (by rw [e]; rfl)
    have j43 : j ≠ 43 := fun e => hj.2.2.2 (by rw [e]; rfl)
    rw [k5 j (by simp; omega), k4 j j20, k3 j (by simp; omega) j43, k2 j (by simp; omega), k1 j j16 j5]

def vA2 : WX :=
  .seq (mulR (rX 16) (rX 22) (rX 15) (rX 17) (rX 7)) <| .seq (WMX.inc (rX 17)) <| .seq (WMX.inc (rX 17)) <|
  .seq (WMX.inc (rX 17)) <| .seq (WMX.inc (rX 17)) <| .seq (WMX.inc (rX 17)) (.wm (WM.clear (rX 16)))

def vA2Cost (G n : ℕ) : ℕ :=
  G * (18 * (2 * n + 3) + 3 + 8) + 7 * G + 3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 + (3 * G + 1))))))

theorem vA2_spec (cap Wb : ℕ) (r : TabReq) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (τ : WSt) (hI : TS Wb inp hd TB σA outV τ)
    (h16 : τ.val (rX 16) = g.val) (h17 : τ.val (rX 17) = 0) (h22 : τ.val (rX 22) = 0)
    (h15 : τ.val (rX 15) = 2 * r.n + 3) (hcap : r.G * (2 * r.n + 3) + 10 ≤ cap) :
    Runs cap vA2 τ (vA2Cost r.G r.n)
      (fun ρ => TS Wb inp hd TB σA outV ρ ∧ ρ.val (rX 17) = 5 + g.val * (2 * r.n + 3) ∧ ρ.val (rX 16) = 0 ∧
        KeepS [16, 17] τ ρ) := by
  have hgG := g.isLt
  have hmc : g.val * (2 * r.n + 3) ≤ r.G * (2 * r.n + 3) := Nat.mul_le_mul_right _ hgG.le
  have hG3 : 3 * r.G ≤ r.G * (2 * r.n + 3) := by nlinarith
  obtain ⟨τ1, e1, h1, v1, k1⟩ := ts_mul cap 16 22 15 17 (by simp) (by decide) g.val (2 * r.n + 3) 0 τ hI h16 h15 h17
    h22 (by omega) (by omega)
  rw [zero_add] at v1
  obtain ⟨τ2, e2, h2, v2, k2⟩ := ts_inc cap 17 (by simp) _ τ1 h1 v1 (by omega)
  obtain ⟨τ3, e3, h3, v3, k3⟩ := ts_inc cap 17 (by simp) _ τ2 h2 v2 (by omega)
  obtain ⟨τ4, e4, h4, v4, k4⟩ := ts_inc cap 17 (by simp) _ τ3 h3 v3 (by omega)
  obtain ⟨τ5, e5, h5, v5, k5⟩ := ts_inc cap 17 (by simp) _ τ4 h4 v4 (by omega)
  obtain ⟨τ6, e6, h6, v6, k6⟩ := ts_inc cap 17 (by simp) _ τ5 h5 v5 (by omega)
  have v6_16 : τ6.val (rX 16) = g.val := by
    rw [k6 16 (by decide), k5 16 (by decide), k4 16 (by decide), k3 16 (by decide), k2 16 (by decide),
      k1 16 (by decide), h16]
  obtain ⟨τ7, e7, h7, v7, k7⟩ := ts_clr cap 16 (by simp) _ τ6 h6 v6_16 (by omega)
  refine ⟨τ7, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <|
    WXExec.seq e6 e7) (by unfold vA2Cost; nlinarith), h7, by rw [k7 17 (by decide), v6]; ring, v7, fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [k7 j (by simp; omega), k6 j (by simp; omega), k5 j (by simp; omega), k4 j (by simp; omega),
    k3 j (by simp; omega), k2 j (by simp; omega), k1 j (by simp; omega)]

def vB : WX :=
  .seq (addR (rX 17) (rX 21) (rX 7)) <| .seq (addR (rX 15) (rX 21) (rX 7)) <| .seq (WMX.dec (rX 21)) <|
  .seq (WMX.dec (rX 21)) <| .seq (emitW 21) (.wm (WM.clear (rX 21)))

def vBCost (Wb N : ℕ) : ℕ := 18 * N + 3 + 1 + (18 * N + 3 + 1 + (1 + 1 + (1 + 1 + (emitCost Wb N + 1 + (3 * N + 1)))))

theorem vB_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h17 : τ.val (rX 17) = 5 + g.val * (2 * r.n + 3)) (h21 : τ.val (rX 21) = 0) (h15 : τ.val (rX 15) = 2 * r.n + 3)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length + 4 * Wb + 40 ≤ cap) :
    Runs cap vB τ (vBCost Wb (preN r).length)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ frame (binary Wb (encS (r.gates g).threshold))) ρ ∧ ρ.val (rX 21) = 0 ∧ KeepS [5, 20, 21] τ ρ) := by
  have hs := preN_tsign r g
  have hm := preN_tmag r g
  have hlenP := preN_length r
  have hpN : 5 + g.val * (2 * r.n + 3) + (2 + 2 * r.n) < (preN r).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; exact absurd hm (by simp)
  have htB := (r.hB g).2
  obtain ⟨τ1, e1, h1, v1, k1⟩ := ts_add cap 21 17 (by simp) (by decide) (by decide) 0 _ τ hI h21 h17 (by omega)
  have v1_15 : τ1.val (rX 15) = 2 * r.n + 3 := by rw [k1 15 (by decide), h15]
  obtain ⟨τ2, e2, h2, v2, k2⟩ := ts_add cap 21 15 (by simp) (by decide) (by decide) _ _ τ1 h1 v1 v1_15 (by omega)
  obtain ⟨τ3, e3, h3, v3, k3⟩ := ts_dec cap 21 (by simp) _ τ2 h2 v2 (by omega)
  obtain ⟨τ4, e4, h4, v4, k4⟩ := ts_dec cap 21 (by simp) _ τ3 h3 v3 (by omega)
  have v4' : τ4.val (rX 21) = 5 + g.val * (2 * r.n + 3) + (1 + 2 * r.n) := by rw [v4]; omega
  have hm' : (preN r)[5 + g.val * (2 * r.n + 3) + (1 + 2 * r.n) + 1]? = some (r.gates g).threshold.natAbs := by
    have e : 5 + g.val * (2 * r.n + 3) + (1 + 2 * r.n) + 1 = 5 + g.val * (2 * r.n + 3) + (2 + 2 * r.n) := by ring
    rw [e]; exact hm
  obtain ⟨τ5, e5, h5, v5, k5⟩ := emitW_spec cap Wb r hW inp hd σA outV 21 (by decide) (by unfold RVL; simp) (by decide)
    _ _ _ hs hm' (by unfold wSign; split_ifs <;> omega) (by omega) τ4 h4 v4' (by omega)
  obtain ⟨τ6, e6, h6, v6, k6⟩ := ts_clr cap 21 (by simp) _ τ5 h5 v5 (by omega)
  refine ⟨τ6, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 e6)
    (by unfold vBCost; omega), by rw [encS_eq]; exact h6, v6, fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [k6 j (by simp; omega), k5 j (by simp; omega), k4 j (by simp; omega), k3 j (by simp; omega),
    k2 j (by simp; omega), k1 j (by simp; omega)]

def vC1 : WX := .seq (addR (rX 25) (rX 23) (rX 7)) <| .seq (addR (rX 11) (rX 24) (rX 7)) coordLoop
def vC2 : WX :=
  .seq (WMX.inc (rX 23)) <| .seq (addR (rX 12) (rX 24) (rX 7)) <| .seq coordLoop <|
  .seq (.wm (WM.clear (rX 23))) (.wm (WM.clear (rX 17)))
def vC : WX := .seq vC1 vC2

/-- The inner and outer coordinates as weight indices. -/
def innerIds (r : TabReq) : Fin r.k → Fin r.n := fun j => r.layout.symm (.inl j)
def outerIds (r : TabReq) : Fin r.s → Fin r.n := fun t => r.layout.symm (.inr t)

theorem crecs_length (Wb : ℕ) (r : TabReq) (g : Fin r.G) {m : ℕ} (ids : Fin m → Fin r.n) (k : ℕ) :
    (crecs Wb r g ids k).length ≤ k * (2 * Wb + 1) := by
  unfold crecs; rw [List.length_flatMap]
  have : ∀ x ∈ (List.ofFn ids).take k, (frame (binary Wb (encS ((r.gates g).weight x)))).length = 2 * Wb + 1 :=
    fun x _ => by rw [frame_length, binary_length]
  rw [List.map_congr_left this]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (List.length_take_le _ _)

def vC1Cost (Wb N k : ℕ) : ℕ := 18 * N + 3 + 1 + (18 * N + 3 + 1 + (k * (coordCost Wb N + 4) + 1))
def vC2Cost (Wb N s : ℕ) : ℕ :=
  3 + 1 + (18 * N + 3 + 1 + (s * (coordCost Wb N + 4) + 1 + 1 + (3 * N + 1 + 1 + (3 * N + 1))))

theorem vC1_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h17 : τ.val (rX 17) = 5 + g.val * (2 * r.n + 3)) (h16 : τ.val (rX 16) = 0) (h21 : τ.val (rX 21) = 0)
    (h44 : τ.val (rX 23) = 0) (h24 : τ.val (rX 24) = 0) (h25 : τ.val (rX 25) = pk r + 1) (h11 : τ.val (rX 11) = r.k)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length +
      (r.k + r.s) * (2 * Wb + 1) + 4 * Wb + 40 ≤ cap) :
    Runs cap vC1 τ (vC1Cost Wb (preN r).length r.k)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ crecs Wb r g (innerIds r) r.k) ρ ∧ ρ.val (rX 17) = 5 + g.val * (2 * r.n + 3) ∧
        ρ.val (rX 23) = pk r + 1 + r.k ∧ ρ.val (rX 16) = 0 ∧ ρ.val (rX 21) = 0 ∧ ρ.val (rX 24) = 0 ∧
        KeepS [5, 20, 16, 21, 23, 24] τ ρ) := by
  have hlenP := preN_length r
  have hk2 := Nat.two_pow_pos r.k
  have hpVe : pV r = 5 + r.G * (2 * r.n + 3) + r.k + 1 + r.s + 1 + 2 ^ r.k + 1 := rfl
  have hpk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  obtain ⟨τ1, e1, h1, v1, k1⟩ := ts_add cap 23 25 (by simp) (by decide) (by decide) 0 _ τ hI h44 h25 (by omega)
  have v1_11 : τ1.val (rX 11) = r.k := by rw [k1 11 (by decide), h11]
  obtain ⟨τ2, e2, h2, v2, k2⟩ := ts_add cap 24 11 (by simp) (by decide) (by decide) 0 _ τ1 h1 (by rw [k1 24 (by decide),
    h24]) v1_11 (by omega)
  rw [zero_add] at v1 v2
  have kk2 : KeepS [23, 24] τ τ2 := fun j hj => by
    rw [k2 j (by simp at hj ⊢; omega), k1 j (by simp at hj ⊢; omega)]
  have v2_44 : τ2.val (rX 23) = pk r + 1 := by rw [k2 23 (by decide), v1]
  obtain ⟨τ3, e3, h3, v3_44, v3_17, v3_16, v3_21, v3_24, k3⟩ := coordLoop_spec cap Wb r hW inp hd σA outV g (pk r + 1)
    r.k (innerIds r) (fun j => preN_inner r j) hWb hBn τ2 h2 v2 v2_44 (by rw [kk2 17 (by decide), h17])
    (by rw [kk2 16 (by decide), h16]) (by rw [kk2 21 (by decide), h21]) (by nlinarith)
  refine ⟨τ3, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 e3) (by unfold vC1Cost; omega), h3, v3_17, v3_44, v3_16,
    v3_21, v3_24, fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [k3 j (by simp; omega), kk2 j (by simp; omega)]

theorem vC2_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h17 : τ.val (rX 17) = 5 + g.val * (2 * r.n + 3)) (h16 : τ.val (rX 16) = 0) (h21 : τ.val (rX 21) = 0)
    (h44 : τ.val (rX 23) = pk r + 1 + r.k) (h24 : τ.val (rX 24) = 0) (h12 : τ.val (rX 12) = r.s)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length +
      r.s * (2 * Wb + 1) + 4 * Wb + 40 + r.G * (2 * r.n + 3) ≤ cap) :
    Runs cap vC2 τ (vC2Cost Wb (preN r).length r.s)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ crecs Wb r g (outerIds r) r.s) ρ ∧ ρ.val (rX 17) = 0 ∧
        ρ.val (rX 23) = 0 ∧ ρ.val (rX 16) = 0 ∧ ρ.val (rX 21) = 0 ∧ ρ.val (rX 24) = 0 ∧
        KeepS [5, 20, 16, 17, 21, 23, 24] τ ρ) := by
  have hlenP := preN_length r
  have hk2 := Nat.two_pow_pos r.k
  have hpVe : pV r = 5 + r.G * (2 * r.n + 3) + r.k + 1 + r.s + 1 + 2 ^ r.k + 1 := rfl
  have hpk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  have hps : ps r = pk r + r.k + 1 := rfl
  have hgG := g.isLt
  have hmc : g.val * (2 * r.n + 3) ≤ r.G * (2 * r.n + 3) := Nat.mul_le_mul_right _ hgG.le
  obtain ⟨τ4, e4, h4, v4, k4⟩ := ts_inc cap 23 (by simp) _ τ hI h44 (by omega)
  have v4_12 : τ4.val (rX 12) = r.s := by rw [k4 12 (by decide), h12]
  obtain ⟨τ5, e5, h5, v5, k5⟩ := ts_add cap 24 12 (by simp) (by decide) (by decide) 0 _ τ4 h4
    (by rw [k4 24 (by decide), h24]) v4_12 (by omega)
  rw [zero_add] at v5
  have v5_44 : τ5.val (rX 23) = ps r + 1 := by rw [k5 23 (by decide), v4]; omega
  obtain ⟨τ6, e6, h6, v6_44, v6_17, v6_16, v6_21, v6_24, k6⟩ := coordLoop_spec cap Wb r hW inp hd σA _ g (ps r + 1)
    r.s (outerIds r) (fun t => preN_outer r t) hWb hBn τ5 h5 v5 v5_44
    (by rw [k5 17 (by decide), k4 17 (by decide), h17]) (by rw [k5 16 (by decide), k4 16 (by decide), h16])
    (by rw [k5 21 (by decide), k4 21 (by decide), h21]) (by omega)
  obtain ⟨τ7, e7, h7, v7, k7⟩ := ts_clr cap 23 (by simp) _ τ6 h6 v6_44 (by omega)
  have v7_17 : τ7.val (rX 17) = 5 + g.val * (2 * r.n + 3) := by rw [k7 17 (by decide), v6_17]
  obtain ⟨τ8, e8, h8, v8, k8⟩ := ts_clr cap 17 (by simp) _ τ7 h7 v7_17 (by omega)
  refine ⟨τ8, WXExec.mono (WXExec.seq e4 <| WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 e8)
    (by unfold vC2Cost; omega), h8, v8, by rw [k8 23 (by decide), v7], by rw [k8 16 (by decide), k7 16 (by decide), v6_16],
    by rw [k8 21 (by decide), k7 21 (by decide), v6_21], by rw [k8 24 (by decide), k7 24 (by decide), v6_24],
    fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rw [k8 j (by simp; omega), k7 j (by simp; omega), k6 j (by simp; omega), k5 j (by simp; omega),
    k4 j (by simp; omega)]

end NearCubicGates.Close.Expand.PolyTab
