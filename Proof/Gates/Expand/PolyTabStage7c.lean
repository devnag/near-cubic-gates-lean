import Proof.Gates.Expand.PolyTabStage7b

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
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- The state inside the point loop. -/
structure HS (Wb : ℕ) (r : TabReq) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt) (o b5 v3 r2 y19 : ℕ)
    (τ : WSt) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB Wb inp hd 0 v τ ∧ v 3 = v3 ∧ v 4 = 0 ∧ v 8 = 1 ∧ v 9 = 0
  out : OutOn τ (sZ 57) (rX 39) (hOut Wb r o) []
  r5 : τ.val (rX 5) = b5
  r2 : τ.val (rX 2) = r2
  z0 : τ.val (rX 0) = 0
  z1 : τ.val (rX 1) = 0
  z9 : τ.val (rX 9) = 0
  z3 : τ.val (rX 3) = 0
  z4 : τ.val (rX 4) = 0
  z6 : τ.val (rX 6) = 0
  z29 : τ.val (rX 29) = 0
  tb : τ.st (sS 3) = TB
  tbh : τ.sh (sS 3) = 0
  y19 : τ.val (rX 19) = y19
  fr : SameExcept σA τ (sZ 57 :: List.ofFn ubv) (rX 2 :: rX 5 :: rX 39 :: rX 19 :: List.ofFn RB)

theorem ubv_mem (i : Fin 10) (hi : i.val ≠ 0) : U0 (te := te) (qa := qa) i ∈ sZ 57 :: List.ofFn ubv := by
  rw [UB_succ _ _ i hi]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_, rfl⟩)

/-- Fetch bit `c` and move it into `rX 5`. -/
theorem hStepA (cap Wb : ℕ) (r : TabReq) (hW : r.k + 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (c y19 : ℕ) (hc : c < 2 ^ r.k) (τ : WSt)
    (hI : HS Wb r inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA c 0 c (pN r + 1 + c) y19 τ)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 2 * (preN r).length + 2 * Wb + 10 ≤ cap) :
    Runs cap (.seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX 2) (rX 9)) (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4)
      (rX 6))) τ (((preN r).length + 1) * (40 * Wb + 40) + 10 * ((preN r).length + 1) * (2 * Wb + 1) + 10 + 1 +
        (1 * (83 * Wb + 30) + 41 * Wb + 14))
      (HS Wb r inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA c ((bitsL r).getD c 0) c
        (pN r + 1 + c) y19) := by
  obtain ⟨⟨v, hv, hv3, hv4, hv8, hv9⟩, hO, h5, h2, h0, h1, h9, h3, h4, h6, h29, htb, htbh, h19, hfr⟩ := hI
  have hWpos : 1 ≤ Wb := by omega
  have hlenP := preN_length r
  have hpN : pN r + 1 + c < (preN r).length := by
    have : pV r = pN r + 2 ^ r.k + 1 := rfl
    omega
  set xs := (preN r).map (· % 2 ^ Wb) with hxs
  have hxl : xs.length = (preN r).length := by simp [hxs]
  set b := (bitsL r).getD c 0 with hb
  have hb1 : b ≤ 1 := by
    rw [hb, List.getD_eq_getElem _ _ (by simp [bitsL]; exact hc)]; exact bitsL_le r c _
  have hbW : b < 2 ^ Wb := lt_of_le_of_lt hb1 (Nat.one_lt_two_pow (by omega))
  have hxv : xs[pN r + 1 + c]'(by rw [hxl]; exact hpN) = b := by
    have e1 := preN_bit r c hc
    have hbit : (bitsL r)[c]? = some b := by
      rw [hb, List.getD_eq_getElem _ _ (by simp [bitsL]; exact hc)]; simp
    rw [hbit] at e1
    simp only [hxs, List.getElem_map]
    rw [getElem_of_getElem? e1]
    exact Nat.mod_eq_of_lt hbW
  have hN4 := hv.num 4 (by decide)
  rw [hv4] at hN4
  have e1 := getAt_spec cap (A := sS 3) (Wk := U0 4) (CA := rX 0) (CW := rX 1) (N := rX 2) (K2 := rX 9)
    (Ne.symm (ne3 4)) (by polyTabNe) Wb hWpos xs (pN r + 1 + c) (by rw [hxl]; exact hpN) τ []
    (by rw [htb, List.append_nil]) htbh h0 hN4.2 (by rw [hN4.1, frame_length, binary_length]) h1 h2 h9
    (by rw [hxl]; omega)
  rw [hxv] at e1
  have hv1 := hv.sets 4 (by decide) b
  have hN8 := hv1.num 8 (by decide)
  have hN9 := hv1.num 9 (by decide)
  have hN4' := hv1.num 4 (by decide)
  simp only [Function.update_self, Function.update_of_ne (show (8 : Fin 10) ≠ 4 by decide),
    Function.update_of_ne (show (9 : Fin 10) ≠ 4 by decide), hv8, hv9] at hN8 hN9 hN4'
  have e2 := toReg_spec cap Wb (X := U0 4) (ONE := U0 8) (Z := U0 9) (R := rX 5) (NZ := rX 3) (F := rX 4) (Rr := rX 6)
    (by simp) (by polyTabNe) _ b 0 0 hN4' hN8 hN9 (by simp [h5]) (by simp [h3]) (by simp [h4]) (by simp [h6]) hbW
    (by omega) (by omega)
  refine ⟨_, WXExec.mono (WXExec.seq e1 e2) (by nlinarith), ⟨Function.update (Function.update v 4 b) 4 0,
    evv_setv (hv1.sets 4 (by decide) 0) 5 (by decide) _, by simp [hv3], by simp, by simp [hv8], by simp [hv9]⟩,
    ⟨?_, ?_, ?_⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (ne57 4).symm, hO.1]
  · simp [hO.2.1]
  · simp [hO.2.2]
  · simp [h2]
  · simp [h0]
  · simp [h1]
  · simp [h9]
  · simp [h3]
  · simp [h4]
  · simp [h6]
  · simp [h29]
  · simp [Function.update_of_ne (ne3 4).symm, htb]
  · simp [htbh]
  · simp [h19]
  · refine se_ext (S' := [U0 4]) (R' := [rX 5]) hfr ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩ (fun x hx => ?_)
      (fun q hq => ?_)
    · simp only [List.mem_singleton] at hx
      simp [Function.update_of_ne hx]
    · simp only [List.mem_singleton] at hq
      simp [Function.update_of_ne hq]
    · simp only [List.mem_singleton] at hx; subst hx; exact ubv_mem 4 (by decide)
    · simp only [List.mem_singleton] at hq; subst hq; simp

/-- Append the point when its bit is set. -/
theorem hStepB (cap Wb : ℕ) (r : TabReq) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt)
    (c y19 r2 : ℕ) (hc : c < 2 ^ r.k) (τ : WSt)
    (hI : HS Wb r inp hd TB σA c ((bitsL r).getD c 0) c r2 y19 τ)
    (hcap : 2 ^ r.k * (2 * Wb + 1) + 2 * Wb + 10 ≤ cap) :
    Runs cap (.ifr (rX 5) (appendRecX (U0 3) (sZ 57) (rX 29) (rX 39)) WMX.skip) τ (40 * Wb + 11 + 1)
      (HS Wb r inp hd TB σA (c + 1) ((bitsL r).getD c 0) c r2 y19) := by
  obtain ⟨⟨v, hv, hv3, hv4, hv8, hv9⟩, hO, h5, h2, h0, h1, h9, h3, h4, h6, h29, htb, htbh, h19, hfr⟩ := hI
  have hOl : (hOut Wb r c).length ≤ c * (2 * Wb + 1) := by
    unfold hOut; rw [List.length_flatMap]
    have : ∀ x ∈ (List.range c).filter (fun c' => (bitsL r).getD c' 0 ≠ 0), (frame (binary Wb x)).length =
        2 * Wb + 1 := fun x _ => by rw [frame_length, binary_length]
    rw [List.map_congr_left this]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (by simp))
  have hc2 : c * (2 * Wb + 1) ≤ 2 ^ r.k * (2 * Wb + 1) := Nat.mul_le_mul_right _ hc.le
  refine Runs.ifr (fun hT => ?_) (fun hF => ?_)
  · have hb0 : (bitsL r).getD c 0 ≠ 0 := by rw [← h5]; exact hT
    have hN3 := hv.num 3 (by decide)
    rw [hv3] at hN3
    have e := appendRec_spec cap (Src := U0 3) (O := sZ 57) (CS := rX 29) (CO := rX 39) (ne57 3) (by polyTabNe) τ
      (binary Wb c) [] (hOut Wb r c) [] (by rw [hN3.1, frame_eq_frameP]) hN3.2 h29 hO (by rw [binary_length]; omega)
    refine ⟨_, WXExec.mono (WXExec.wm e) (by rw [binary_length]), ⟨v, evv_out hv _ ne57 _ _ 39 (by decide) _,
      hv3, hv4, hv8, hv9⟩, ⟨?_, ?_, ?_⟩, by simp [h5], by simp [h2], by simp [h0], by simp [h1], by simp [h9],
      by simp [h3], by simp [h4], by simp [h6], by simp [h29], ?_, ?_, by simp [h19], ?_⟩
    · rw [hOut_succ, if_pos hb0]; simp [overlay]
    · rw [hOut_succ, if_pos hb0]; simp
    · rw [hOut_succ, if_pos hb0]; simp
    · simp [Function.update_of_ne (show sS 3 ≠ sZ 57 by polyTabNe), htb]
    · simp [Function.update_of_ne (show sS 3 ≠ sZ 57 by polyTabNe), htbh]
    · refine se_ext (S' := [sZ 57]) (R' := [rX 39]) hfr ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩ (by simp) (by simp)
      · simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx]
      · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]
  · have hb0 : (bitsL r).getD c 0 = 0 := by rw [← h5]; exact hF
    refine ⟨τ, WXExec.mono (WXExec.skip cap τ) (by omega), ⟨v, hv, hv3, hv4, hv8, hv9⟩, ?_, h5, h2, h0, h1, h9, h3, h4, h6,
      h29, htb, htbh, h19, hfr⟩
    rw [hOut_succ, if_neg (by omega), List.append_nil]; exact hO

/-- Clear the bit, count the point. -/
theorem hStepC (cap Wb : ℕ) (r : TabReq) (hW : r.k + 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (TB : List Bool)
    (σA : WSt) (c y19 r2 : ℕ) (hc : c < 2 ^ r.k) (τ : WSt)
    (hI : HS Wb r inp hd TB σA (c + 1) ((bitsL r).getD c 0) c r2 y19 τ) (hcap : 2 * Wb + r2 + 10 ≤ cap) :
    Runs cap (.seq (.wm (WM.clear (rX 5))) (.seq (BinW.inc (U0 3) (U0 9) (RB 2) (RB 3)) (WMX.inc (rX 2)))) τ
      (3 * 1 + 1 + 1 + (41 * Wb + 7 + 1 + 3)) (HS Wb r inp hd TB σA (c + 1) 0 (c + 1) (r2 + 1) y19) := by
  obtain ⟨⟨v, hv, hv3, hv4, hv8, hv9⟩, hO, h5, h2, h0, h1, h9, h3, h4, h6, h29, htb, htbh, h19, hfr⟩ := hI
  have hb1 : (bitsL r).getD c 0 ≤ 1 := by
    rw [List.getD_eq_getElem _ _ (by simp [bitsL]; exact hc)]; exact bitsL_le r c _
  have e4 := wclear_spec (cap := cap) (rX 5) ((bitsL r).getD c 0) τ h5 (by omega)
  have hv4' := evv_setv hv 5 (by decide) 0
  have hN3' := hv4'.num 3 (by decide)
  have hN9' := hv4'.num 9 (by decide)
  rw [hv3] at hN3'; rw [hv9] at hN9'
  have hRB2 : (τ.setv (rX 5) 0).val (RB 2) = 0 := hv4'.zero 2 (by decide) (by decide)
  have hRB3 : (τ.setv (rX 5) 0).val (RB 3) = 0 := hv4'.zero 3 (by decide) (by decide)
  have hck : c + 1 < 2 ^ Wb := by
    have : 2 ^ r.k < 2 ^ Wb := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have e5 := BinW.inc_spec cap Wb (A := U0 3) (B := U0 9) (F := RB 2) (R := RB 3) (by simp)
    (by intro e; exact absurd (RB.injective e) (by decide)) (τ.setv (rX 5) 0) c 0 hN3' hN9' hRB2 hRB3 hck (by omega)
  have e6 := WXExec.inc cap (rX 2) ((τ.setv (rX 5) 0).sets (U0 3) (frame (binary Wb (c + 1)))) (by simp [h2]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e4) (WXExec.seq e5 e6)) (by omega), ⟨Function.update v 3 (c + 1),
    evv_setv (hv4'.sets 3 (by decide) (c + 1)) 2 (by decide) _, by simp, by simp [hv4], by simp [hv8], by simp [hv9]⟩,
    ⟨?_, ?_, ?_⟩, by simp, by simp [h2], by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4],
    by simp [h6], by simp [h29], ?_, by simp [htbh], by simp [h19], ?_⟩
  · simp [Function.update_of_ne (ne57 3).symm, hO.1]
  · simp [hO.2.1]
  · simp [hO.2.2]
  · simp [Function.update_of_ne (ne3 3).symm, htb]
  · refine se_ext (S' := [U0 3]) (R' := [rX 5, rX 2]) hfr ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩ (fun x hx => ?_)
      (fun q hq => ?_)
    · simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx]
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hq
      simp [Function.update_of_ne hq.1, Function.update_of_ne hq.2]
    · simp only [List.mem_singleton] at hx; subst hx; exact ubv_mem 3 (by decide)
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp

def hBody' : WX :=
  .seq (.seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX 2) (rX 9)) (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4)
    (rX 6))) (.seq (.ifr (rX 5) (appendRecX (U0 3) (sZ 57) (rX 29) (rX 39)) WMX.skip)
      (.seq (.wm (WM.clear (rX 5))) (.seq (BinW.inc (U0 3) (U0 9) (RB 2) (RB 3)) (WMX.inc (rX 2)))))

def hLoop : WX := .whr (rX 19) (.seq (WMX.dec (rX 19)) hBody')

def st7b : WX := .seq hLoop (closeOutX (sZ 57) (rX 39))

def hCost (Wb : ℕ) (r : TabReq) : ℕ :=
  ((preN r).length + 1) * (40 * Wb + 40) + 10 * ((preN r).length + 1) * (2 * Wb + 1) + 10 + 1 +
    (1 * (83 * Wb + 30) + 41 * Wb + 14) + 1 + (40 * Wb + 11 + 1 + 1 + (3 * 1 + 1 + 1 + (41 * Wb + 7 + 1 + 3)))

theorem HS.setv19 {Wb : ℕ} {r : TabReq} {inp : List Bool} {hd : ℕ} {TB : List Bool} {σA : WSt}
    {o b5 v3 r2 y : ℕ} {τ : WSt} (h : HS Wb r inp hd TB σA o b5 v3 r2 y τ) (x : ℕ) :
    HS Wb r inp hd TB σA o b5 v3 r2 x (τ.setv (rX 19) x) := by
  obtain ⟨⟨v, hv, hv3, hv4, hv8, hv9⟩, hO, h5, h2, h0, h1, h9, h3, h4, h6, h29, htb, htbh, h19, hfr⟩ := h
  exact ⟨⟨v, evv_setv hv 19 (by decide) x, hv3, hv4, hv8, hv9⟩, ⟨by simp [hO.1], by simp [hO.2.1], by simp [hO.2.2]⟩,
    by simp [h5], by simp [h2], by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4], by simp [h6],
    by simp [h29], by simp [htb], by simp [htbh], by simp,
    se_ext hfr (sameExcept_setv (S := []) τ (List.mem_singleton_self _) x) (by simp) (by simp)⟩

theorem hsK_eq (E : ExpandMachine) (r : TabReq) :
    hsK E r = (List.range (2 ^ r.k)).filter fun c => (bitsL r).getD c 0 ≠ 0 := by
  unfold hsK hList code
  apply List.filter_congr
  intro c hc
  rw [List.mem_range] at hc
  rw [List.getD_eq_getElem _ _ (by simp; exact hc), List.getD_eq_getElem _ _ (by simp [bitsL]; exact hc)]
  simp [bitsL, tabT]

/-- After the point loop. -/
structure HEnd (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt)
    (τ : WSt) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB Wb inp hd 0 v τ ∧ v 4 = 0 ∧ v 8 = 1 ∧ v 9 = 0
  z57 : τ.st (sZ 57) = recStream ((hsK E r).map (binary Wb))
  z57h : τ.sh (sZ 57) = 0
  z39 : τ.val (rX 39) = 0
  z5 : τ.val (rX 5) = 0
  z0 : τ.val (rX 0) = 0
  z1 : τ.val (rX 1) = 0
  z9 : τ.val (rX 9) = 0
  z3 : τ.val (rX 3) = 0
  z4 : τ.val (rX 4) = 0
  z6 : τ.val (rX 6) = 0
  z29 : τ.val (rX 29) = 0
  z19 : τ.val (rX 19) = 0
  tb : τ.st (sS 3) = TB
  tbh : τ.sh (sS 3) = 0
  fr : SameExcept σA τ (sZ 57 :: List.ofFn ubv) (rX 2 :: rX 5 :: rX 39 :: rX 19 :: List.ofFn RB)
  r2 : τ.val (rX 2) = pV r

theorem st7b_spec (cap Wb : ℕ) (E : ExpandMachine) (r : TabReq) (hW : r.k + 1 ≤ Wb) (inp : List Bool) (hd : ℕ)
    (σA σ : WSt) (hI : HS Wb r inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA 0 0 0 (pN r + 1)
      (2 ^ r.k) σ)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 2 * (preN r).length + 2 ^ r.k * (2 * Wb + 1) + 2 * Wb + 10 ≤ cap) :
    Runs cap st7b σ (2 ^ r.k * (hCost Wb r + 4) + 1 + 1 + (5 * (2 ^ r.k * (2 * Wb + 1)) + 3))
      (HEnd Wb E r inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA) := by
  have hlenP := preN_length r
  have hpV : pV r = pN r + 2 ^ r.k + 1 := rfl
  set TB := recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb)) with hTB
  let Inv : ℕ → WSt → Prop := fun c τ => HS Wb r inp hd TB σA c 0 c (pN r + 1 + c) (τ.val (rX 19)) τ
  have hI0 : Inv 0 σ := by
    show HS Wb r inp hd TB σA 0 0 0 (pN r + 1 + 0) (σ.val (rX 19)) σ
    rw [hI.y19, Nat.add_zero]; exact hI
  have hloop := Runs.count (cap := cap) (K := rX 19) (body := hBody') (hCost Wb r) (2 ^ r.k) Inv (by nlinarith)
    (fun c hc τ hτ hK => by
      have h0 := hτ.setv19 (2 ^ r.k - c - 1)
      have hA := hStepA cap Wb r hW inp hd σA c _ hc _ h0 (by nlinarith)
      refine (Runs.seq hA fun τ1 h1 => Runs.seq (hStepB cap Wb r inp hd _ σA c _ _ hc τ1 h1 (by nlinarith))
        fun τ2 h2 => hStepC cap Wb r hW inp hd _ σA c _ _ hc τ2 h2 (by omega)).mono (by unfold hCost; omega)
        fun ρ hρ => ⟨?_, hρ.y19⟩
      show HS Wb r inp hd TB σA (c + 1) 0 (c + 1) (pN r + 1 + (c + 1)) (ρ.val (rX 19)) ρ
      rw [hρ.y19, show pN r + 1 + (c + 1) = pN r + 1 + c + 1 by ring]; exact hρ) σ hI0 hI.y19
  refine Runs.seq hloop fun τ ⟨hτ, hK⟩ => ?_
  obtain ⟨⟨v, hv, hv3, hv4, hv8, hv9⟩, hO, h5, h2, h0, h1, h9, h3, h4, h6, h29, htb, htbh, h19, hfr⟩ := hτ
  have hOl : (hOut Wb r (2 ^ r.k)).length ≤ 2 ^ r.k * (2 * Wb + 1) := by
    unfold hOut; rw [List.length_flatMap]
    have : ∀ x ∈ (List.range (2 ^ r.k)).filter (fun c' => (bitsL r).getD c' 0 ≠ 0), (frame (binary Wb x)).length =
        2 * Wb + 1 := fun x _ => by rw [frame_length, binary_length]
    rw [List.map_congr_left this]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (by simp))
  have e := closeOut_spec cap (σ := τ) (hOut Wb r (2 ^ r.k)) [] hO (by omega)
  refine ⟨_, WXExec.mono (WXExec.wm e) (by omega), ⟨v, evv_out hv _ ne57 _ _ 39 (by decide) _, hv4, hv8, hv9⟩, ?_,
    by simp, by simp, by simp [h5], by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4], by simp [h6],
    by simp [h29], by simp [hK], ?_, ?_, ?_, ?_⟩
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, overlay, List.drop_nil,
      List.append_nil, recStream, hsK_eq E r, hOut, List.flatMap_map]
  · simp [Function.update_of_ne (show sS 3 ≠ sZ 57 by polyTabNe), htb]
  · simp [Function.update_of_ne (show sS 3 ≠ sZ 57 by polyTabNe), htbh]
  · refine se_ext (S' := [sZ 57]) (R' := [rX 39]) hfr ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩ (by simp) (by simp)
    · simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx]
    · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne (show rX 2 ≠ rX 39 by polyTabNe), h2, hpV]; omega

end NearCubicGates.Close.Expand.PolyTab
