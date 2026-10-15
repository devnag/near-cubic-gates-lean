import Proof.Gates.Expand.PolyTabStage7c
import Proof.Gates.Expand.PolyTabData2

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
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- The registers the occurrence-table phase may change. -/
def RVL : List (Fin NRk) := [rX 5, rX 20, rX 16, rX 17, rX 21, rX 22, rX 24, rX 25, rX 43, rX 23, rX 26] ++ List.ofFn RB

/-- The state of the occurrence-table phase (`rX 5 = b5`, `U 4` satisfying `q4`). -/
structure TSg (Wb : ℕ) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt) (outV : List Bool) (b5 : ℕ)
    (q4 : ℕ → Prop) (τ : WSt) : Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB Wb inp hd 0 v τ ∧ v 8 = 1 ∧ v 9 = 0 ∧ q4 (v 4)
  out : OutOn τ (sS 4) (rX 20) outV []
  z0 : τ.val (rX 0) = 0
  z1 : τ.val (rX 1) = 0
  z9 : τ.val (rX 9) = 0
  z3 : τ.val (rX 3) = 0
  z4 : τ.val (rX 4) = 0
  z6 : τ.val (rX 6) = 0
  z5 : τ.val (rX 5) = b5
  z29 : τ.val (rX 29) = 0
  z7 : τ.val (rX 7) = 0
  tb : τ.st (sS 3) = TB
  tbh : τ.sh (sS 3) = 0
  fr : SameExcept σA τ (sS 4 :: List.ofFn ubv) RVL

abbrev TS (Wb : ℕ) (inp : List Bool) (hd : ℕ) (TB : List Bool) (σA : WSt) (outV : List Bool) (τ : WSt) : Prop :=
  TSg Wb inp hd TB σA outV 0 (fun _ => True) τ

theorem ne4 (i : Fin 10) : U0 (te := te) (qa := qa) i ≠ sS 4 := U0_ne_ubv_off i _ (by simp)

theorem ubv_mem4 (i : Fin 10) (hi : i.val ≠ 0) : U0 (te := te) (qa := qa) i ∈ sS 4 :: List.ofFn ubv := by
  rw [UB_succ _ _ i hi]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_, rfl⟩)

theorem RB_memV (j : Fin 12) : RB j ∈ (RVL : List (Fin NRk)) := by
  unfold RVL; exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- Fetch the sign into `rX 5`, the magnitude into `U 4`. -/
def emitA (P : Fin 64) : WX :=
  .seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX P) (rX 9)) <|
  .seq (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4) (rX 6)) <|
  .seq (WMX.inc (rX P)) <| .seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX P) (rX 9)) (WMX.dec (rX P))

/-- `U 4 := 2·U 4 + rX 5`, append it, clear `rX 5`. -/
def emitB : WX :=
  .seq (BinW.shl (U0 4) (U0 9) (RB 2) (RB 3)) <|
  .seq (.ifr (rX 5) (BinW.inc (U0 4) (U0 9) (RB 2) (RB 3)) WMX.skip) <|
  .seq (.wm (WM.clear (rX 5))) (appendRecX (U0 4) (sS 4) (rX 29) (rX 20))

def emitW (P : Fin 64) : WX := .seq (emitA P) emitB

def gaCost (Wb N : ℕ) : ℕ := (N + 1) * (40 * Wb + 40) + 10 * (N + 1) * (2 * Wb + 1) + 10

theorem ga_le (Wb N p : ℕ) (hp : p < N + 1) :
    (p + 1) * (40 * Wb + 40) + 10 * (p + 1) * (2 * Wb + 1) + 10 ≤ gaCost Wb N := by
  unfold gaCost
  have h1 : (p + 1) * (40 * Wb + 40) ≤ (N + 1) * (40 * Wb + 40) := Nat.mul_le_mul_right _ (by omega)
  have h2 : 10 * (p + 1) * (2 * Wb + 1) ≤ 10 * (N + 1) * (2 * Wb + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  omega

def emitCost (Wb N : ℕ) : ℕ :=
  gaCost Wb N + 1 + (1 * (83 * Wb + 30) + 41 * Wb + 14 + 1 + (3 + 1 + (gaCost Wb N + 1 + 1))) + 1 +
    (41 * Wb + 8 + 1 + (41 * Wb + 7 + 1 + 1 + (3 * 1 + 1 + 1 + (40 * Wb + 11))))

/-- Registers other than `rX 5`, `rX 20` and `P` keep their values. -/
def Keep (P : Fin 64) (τ ρ : WSt) : Prop := ∀ j : Fin 64, j.val ∉ [5, 20] → j ≠ P → ρ.val (rX j) = τ.val (rX j)

theorem Keep.refl (P : Fin 64) (τ : WSt) : Keep P τ τ := fun _ _ _ => rfl
theorem Keep.trans {P : Fin 64} {τ ρ μ : WSt} (h1 : Keep P τ ρ) (h2 : Keep P ρ μ) : Keep P τ μ :=
  fun j hj hjP => (h2 j hj hjP).trans (h1 j hj hjP)

/-- Fetch field `p = rX P` of the request table into `U 4`. -/
theorem tsg_getAt (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (b5 : ℕ) (q4 : ℕ → Prop) (P : Fin 64) (hP : P.val ∉ [0, 1, 9]) (p x : ℕ)
    (hx : (preN r)[p]? = some x) (hxW : x < 2 ^ Wb) (τ : WSt)
    (hI : TSg Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV b5 q4 τ)
    (hp : τ.val (rX P) = p) (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 2 * (preN r).length ≤ cap) :
    Runs cap (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX P) (rX 9)) τ (gaCost Wb (preN r).length)
      (fun ρ => TSg Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV b5 (· = x) ρ ∧
        ρ.val (rX P) = p ∧ Keep P τ ρ) := by
  obtain ⟨⟨v, hv, hv8, hv9, -⟩, hO, h0, h1, h9, h3, h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := hI
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hP
  have rP : ∀ j : Fin 64, j.val ≠ P.val → rX j ≠ rX P := fun j hj => rX_ne (fun e => hj (by rw [e]))
  have hp1 : p < (preN r).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hx; exact absurd hx (by simp)
  have hxl : ((preN r).map (· % 2 ^ Wb)).length = (preN r).length := by simp
  have hx0 : ((preN r).map (· % 2 ^ Wb))[p]'(by rw [hxl]; omega) = x := by
    simp only [List.getElem_map]; rw [getElem_of_getElem? hx]; exact Nat.mod_eq_of_lt hxW
  have hnd : [rX 0, rX 1, rX P, rX 9].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨by polyTabNe, rP 0 (by simp; omega), by polyTabNe⟩, ⟨rP 1 (by simp; omega), by polyTabNe⟩,
      Ne.symm (rP 9 (by simp; omega)), not_false⟩
  have hN4 := hv.num 4 (by decide)
  have e1 := getAt_spec cap (A := sS 3) (Wk := U0 4) (CA := rX 0) (CW := rX 1) (N := rX P) (K2 := rX 9)
    (Ne.symm (ne3 4)) hnd Wb hW _ p (by rw [hxl]; omega) τ [] (by rw [htb, List.append_nil]) htbh h0 hN4.2
    (by rw [hN4.1, frame_length, binary_length]) h1 hp h9 (by rw [hxl]; omega)
  rw [hx0] at e1
  have u45 : sS 4 ≠ U0 (te := te) (qa := qa) 4 := (ne4 4).symm
  have u43 : sS 3 ≠ U0 (te := te) (qa := qa) 4 := (ne3 4).symm
  refine ⟨_, WXExec.mono e1 (ga_le Wb _ p (by omega)), ⟨⟨Function.update v 4 x, hv.sets 4 (by decide) x,
    by simp [hv8], by simp [hv9], by simp⟩, ⟨by simp [Function.update_of_ne u45, hO.1], by simp [hO.2.1],
    by simp [hO.2.2]⟩, by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4], by simp [h6], by simp [h5],
    by simp [h29], by simp [h7], by simp [Function.update_of_ne u43, htb], by simp [htbh], ?_⟩, by simp [hp],
    fun j _ _ => by simp⟩
  refine se_ext (S' := [U0 4]) (R' := []) hfr ⟨fun y hy => ?_, fun q _ => by simp, rfl⟩ (fun y hy => ?_) (by simp)
  · simp only [List.mem_singleton] at hy; simp [Function.update_of_ne hy]
  · simp only [List.mem_singleton] at hy; subst hy; exact ubv_mem4 4 (by decide)

section TSgSteps
variable {Wb : ℕ} {inp : List Bool} {hd : ℕ} {TB : List Bool} {σA : WState (NSx te qa) NRk} {outV : List Bool} {b5 : ℕ}
  {q4 : ℕ → Prop}

theorem TSg.setv {τ : WSt} (h : TSg Wb inp hd TB σA outV b5 q4 τ) (j : Fin 64)
    (hj : j.val ∉ [0, 1, 9, 3, 4, 6, 5, 29, 20, 7]) (hjV : rX j ∈ (RVL : List (Fin NRk))) (hj52 : j.val < 52) (y : ℕ) :
    TSg Wb inp hd TB σA outV b5 q4 (τ.setv (rX j) y) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq⟩, hO, h0, h1, h9, h3, h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  have rj : ∀ k : Fin 64, k.val ≠ j.val → rX k ≠ rX j := fun k hk => rX_ne (fun e => hk (by rw [e]))
  refine ⟨⟨v, evv_setv hv j hj52 y, hv8, hv9, hq⟩, ⟨by simp [hO.1], by simp [hO.2.1],
    by simp [Function.update_of_ne (rj 20 (by simp; omega)), hO.2.2]⟩,
    by simp [Function.update_of_ne (rj 0 (by simp; omega)), h0], by simp [Function.update_of_ne (rj 1 (by simp; omega)), h1],
    by simp [Function.update_of_ne (rj 9 (by simp; omega)), h9], by simp [Function.update_of_ne (rj 3 (by simp; omega)), h3],
    by simp [Function.update_of_ne (rj 4 (by simp; omega)), h4], by simp [Function.update_of_ne (rj 6 (by simp; omega)), h6],
    by simp [Function.update_of_ne (rj 5 (by simp; omega)), h5],
    by simp [Function.update_of_ne (rj 29 (by simp; omega)), h29], by simp [Function.update_of_ne (rj 7 (by simp; omega)), h7],
    by simp [htb], by simp [htbh], ?_⟩
  exact se_ext hfr (sameExcept_setv (S := []) τ (List.mem_singleton_self _) y) (by simp)
    (fun q hq => by simp at hq; subst hq; exact hjV)

/-- `rX 5 := U 4`, `U 4 := 0`. -/
theorem tsg_toReg (cap : ℕ) (hW : 1 ≤ Wb) (x : ℕ) (hxW : x < 2 ^ Wb) (τ : WSt)
    (h : TSg Wb inp hd TB σA outV 0 (· = x) τ) (hcap : 2 * Wb + x + 2 ≤ cap) :
    Runs cap (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4) (rX 6)) τ (x * (83 * Wb + 30) + 41 * Wb + 14)
      (fun ρ => TSg Wb inp hd TB σA outV x (· = 0) ρ ∧ ∀ j : Fin 64, j ≠ 5 → ρ.val (rX j) = τ.val (rX j)) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq⟩, hO, h0, h1, h9, h3, h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := h
  have hN4 := hv.num 4 (by decide); have hN8 := hv.num 8 (by decide); have hN9 := hv.num 9 (by decide)
  rw [hq] at hN4; rw [hv8] at hN8; rw [hv9] at hN9
  have e := toReg_spec cap Wb (X := U0 4) (ONE := U0 8) (Z := U0 9) (R := rX 5) (NZ := rX 3) (F := rX 4) (Rr := rX 6)
    (by simp) (by polyTabNe) τ x 0 0 hN4 hN8 hN9 h5 h3 h4 h6 hxW (by omega) (by omega)
  have u45 : sS 4 ≠ U0 (te := te) (qa := qa) 4 := (ne4 4).symm
  have u43 : sS 3 ≠ U0 (te := te) (qa := qa) 4 := (ne3 4).symm
  refine ⟨_, e, ⟨⟨Function.update v 4 0, evv_setv (hv.sets 4 (by decide) 0) 5 (by decide) _, by simp [hv8],
    by simp [hv9], by simp⟩, ⟨by simp [Function.update_of_ne u45, hO.1], by simp [hO.2.1], by simp [hO.2.2]⟩,
    by simp [h0], by simp [h1], by simp [h9], by simp [h3], by simp [h4], by simp [h6], by simp, by simp [h29], by simp [h7],
    by simp [Function.update_of_ne u43, htb], by simp [htbh], ?_⟩, fun j hj => by
      simp [Function.update_of_ne (rX_ne hj)]⟩
  refine se_ext (S' := [U0 4]) (R' := [rX 5]) hfr ⟨fun y hy => ?_, fun q hq => ?_, rfl⟩ (fun y hy => ?_)
    (fun q hq => ?_)
  · simp only [List.mem_singleton] at hy; simp [Function.update_of_ne hy]
  · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]
  · simp only [List.mem_singleton] at hy; subst hy; exact ubv_mem4 4 (by decide)
  · simp only [List.mem_singleton] at hq; subst hq; unfold RVL; simp

/-- `U 4 := 2·U 4 + rX 5`, then `rX 5 := 0`, then append `U 4` to the occurrence table. -/
theorem tsg_emitB (cap : ℕ) (hW : 1 ≤ Wb) (sg mag : ℕ) (hsg : sg ≤ 1) (hmW : 2 * mag + 1 < 2 ^ Wb) (τ : WSt)
    (h : TSg Wb inp hd TB σA outV sg (· = mag) τ) (hcap : outV.length + 4 * Wb + 10 ≤ cap) :
    Runs cap emitB τ (41 * Wb + 8 + 1 + (41 * Wb + 7 + 1 + 1 + (3 * 1 + 1 + 1 + (40 * Wb + 11))))
      (fun ρ => TSg Wb inp hd TB σA (outV ++ frame (binary Wb (2 * mag + sg))) 0 (fun _ => True) ρ ∧
        ∀ j : Fin 64, j.val ∉ [5, 20] → ρ.val (rX j) = τ.val (rX j)) := by
  obtain ⟨⟨v, hv, hv8, hv9, hq⟩, hO, h0, h1, h9, h3, h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := h
  have hN4 := hv.num 4 (by decide); have hN9 := hv.num 9 (by decide)
  rw [hq] at hN4; rw [hv9] at hN9
  have hRB2 := hv.zero 2 (by decide) (by decide)
  have hRB3 := hv.zero 3 (by decide) (by decide)
  have nRB : (RB 2 : Fin NRk) ≠ RB 3 := fun e => absurd (RB.injective e) (by decide)
  have e1 := BinW.shl_spec cap Wb (A := U0 4) (B := U0 9) (F := RB 2) (R := RB 3) (by simp) nRB τ mag 0 hN4 hN9
    hRB2 hRB3 (by omega)
  set τ1 := τ.sets (U0 4) (frame (binary Wb (2 * mag))) with hτ1
  have hv1 := hv.sets 4 (by decide) (2 * mag)
  have u45 : sS 4 ≠ U0 (te := te) (qa := qa) 4 := (ne4 4).symm
  have u43 : sS 3 ≠ U0 (te := te) (qa := qa) 4 := (ne3 4).symm
  -- the conditional increment
  let Q2 : WSt → Prop := fun τ2 => EvV U0 RB Wb inp hd 0 (Function.update v 4 (2 * mag + sg)) τ2 ∧
    (∀ q : Fin NRk, τ2.val q = τ1.val q) ∧ (∀ y, y ≠ U0 4 → τ2.st y = τ1.st y ∧ τ2.sh y = τ1.sh y) ∧
    τ2.cell = τ1.cell
  have e2 : Runs cap (.ifr (rX 5) (BinW.inc (U0 4) (U0 9) (RB 2) (RB 3)) WMX.skip) τ1 (41 * Wb + 7 + 1) Q2 := by
    refine Runs.ifr (fun hT => ?_) (fun hF => ?_)
    · have h5' : τ1.val (rX 5) = sg := by simp [hτ1, h5]
      have hs1 : sg = 1 := by omega
      have hN4' := hv1.num 4 (by decide); have hN9' := hv1.num 9 (by decide)
      simp only [Function.update_self, Function.update_of_ne (show (9 : Fin 10) ≠ 4 by decide), hv9] at hN4' hN9'
      have e := BinW.inc_spec cap Wb (A := U0 4) (B := U0 9) (F := RB 2) (R := RB 3) (by simp) nRB τ1 (2 * mag) 0
        hN4' hN9' (by simp [hτ1, hRB2]) (by simp [hτ1, hRB3]) (by omega) (by omega)
      refine ⟨_, WXExec.mono e le_rfl, ?_, fun q => by simp, fun y hy => by simp [Function.update_of_ne hy], by simp⟩
      rw [hs1]
      have := hv1.sets 4 (by decide) (2 * mag + 1)
      simpa [hτ1] using this
    · have h5' : τ1.val (rX 5) = sg := by simp [hτ1, h5]
      have hs0 : sg = 0 := by omega
      refine ⟨τ1, WXExec.mono (WXExec.skip cap τ1) (by omega), ?_, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩, rfl⟩
      rw [hs0, Nat.add_zero]; exact hv1
  refine Runs.seqE e1 (Runs.seq e2 fun τ2 ⟨hv2, hval2, hst2, hcell2⟩ => ?_)
  have h52 : τ2.val (rX 5) = sg := by rw [hval2]; simp [hτ1, h5]
  have e3 := wclear_spec (cap := cap) (rX 5) sg τ2 h52 (by omega)
  have hv3 := evv_setv hv2 5 (by decide) 0
  have hN4'' := hv3.num 4 (by decide)
  simp only [Function.update_self] at hN4''
  have hO3 : OutOn (τ2.setv (rX 5) 0) (sS 4) (rX 20) outV [] :=
    ⟨by simp [(hst2 _ u45).1, hτ1, Function.update_of_ne u45, hO.1], by simp [(hst2 _ u45).2, hτ1, hO.2.1],
      by simp [hval2, hτ1, hO.2.2]⟩
  have hb2W : (binary Wb (2 * mag + sg)).length = Wb := binary_length _ _
  have e4 := appendRec_spec cap (Src := U0 4) (O := sS 4) (CS := rX 29) (CO := rX 20) (ne4 4) (by polyTabNe)
    (τ2.setv (rX 5) 0) (binary Wb (2 * mag + sg)) [] outV [] (by rw [hN4''.1, frame_eq_frameP]) hN4''.2
    (by simp [hval2, hτ1, h29]) hO3 (by rw [hb2W]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)) (by rw [hb2W]; omega), ⟨⟨Function.update v 4
    (2 * mag + sg), evv_out hv3 _ ne4 _ _ 20 (by decide) _, by simp [hv8], by simp [hv9], trivial⟩, ⟨?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun j hj => ?_⟩
  · simp [overlay]
  · simp
  · simp
  · simp [hval2, hτ1, h0]
  · simp [hval2, hτ1, h1]
  · simp [hval2, hτ1, h9]
  · simp [hval2, hτ1, h3]
  · simp [hval2, hτ1, h4]
  · simp [hval2, hτ1, h6]
  · simp
  · simp [hval2, hτ1, h29]
  · simp [hval2, hτ1, h7]
  · simp [Function.update_of_ne (show sS 3 ≠ sS 4 by polyTabNe), (hst2 _ u43).1, hτ1, Function.update_of_ne u43, htb]
  · simp [Function.update_of_ne (show sS 3 ≠ sS 4 by polyTabNe), (hst2 _ u43).2, hτ1, htbh]
  · have hfr2 : SameExcept τ τ2 [U0 4] [] := ⟨fun y hy => by
        simp only [List.mem_singleton] at hy
        rw [(hst2 y hy).1, (hst2 y hy).2]; simp [hτ1, Function.update_of_ne hy],
      fun q _ => by rw [hval2]; simp [hτ1], by rw [hcell2]; simp [hτ1]⟩
    refine se_ext (S' := [sS 4]) (R' := [rX 5, rX 20]) (se_ext hfr hfr2 (fun y hy => ?_) (by simp)) ⟨fun y hy => ?_,
      fun q hq => ?_, rfl⟩ (by simp) (fun q hq => ?_)
    · simp only [List.mem_singleton] at hy; subst hy; exact ubv_mem4 4 (by decide)
    · simp only [List.mem_singleton] at hy; simp [Function.update_of_ne hy]
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hq
      simp [Function.update_of_ne hq.1, Function.update_of_ne hq.2]
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> (unfold RVL; simp)
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hj
    have j5 : rX j ≠ rX 5 := rX_ne (fun e => hj.1 (by rw [e]; rfl))
    have j20 : rX j ≠ rX 20 := rX_ne (fun e => hj.2 (by rw [e]; rfl))
    simp [Function.update_of_ne j5, Function.update_of_ne j20, hval2, hτ1]

theorem emitW_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (P : Fin 64) (hP : P.val ∉ [0, 1, 9, 3, 4, 6, 5, 29, 20, 7]) (hPV : rX P ∈ (RVL : List (Fin NRk)))
    (hP52 : P.val < 52) (p sg mag : ℕ) (hsg : (preN r)[p]? = some sg) (hmag : (preN r)[p + 1]? = some mag)
    (hsg1 : sg ≤ 1) (hmW : 2 * mag + 1 < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ) (hp : τ.val (rX P) = p)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 2 * (preN r).length + outV.length + 4 * Wb + p + 20 ≤ cap) :
    Runs cap (emitW P) τ (emitCost Wb (preN r).length)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ frame (binary Wb (2 * mag + sg))) ρ ∧ ρ.val (rX P) = p ∧
        ∀ j : Fin 64, j.val ∉ [5, 20] → ρ.val (rX j) = τ.val (rX j)) := by
  have hP' := hP
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hP'
  obtain ⟨n0, n1, n9, n3, n4, n6, n5, n29, n20, n7⟩ := hP'
  have hsgW : sg < 2 ^ Wb := lt_of_le_of_lt hsg1 (Nat.one_lt_two_pow (by omega))
  have hmW' : mag < 2 ^ Wb := by omega
  obtain ⟨τ1, e1, h1, hp1, hk1⟩ :=
    tsg_getAt cap Wb r hW inp hd σA outV 0 (fun _ => True) P (by simp; omega) p sg hsg hsgW τ hI hp (by omega)
  obtain ⟨τ2, e2, h2, hk2⟩ := tsg_toReg cap hW sg hsgW τ1 h1 (by omega)
  have hp2 : τ2.val (rX P) = p := by rw [hk2 P (fun e => n5 (by rw [e]; rfl)), hp1]
  have e3 := WXExec.inc cap (rX P) τ2 (by rw [hp2]; omega)
  rw [hp2] at e3
  have h3 := h2.setv P hP hPV hP52 (p + 1)
  obtain ⟨τ4, e4, h4, hp4, hk4⟩ := tsg_getAt cap Wb r hW inp hd σA outV sg (· = 0) P (by simp; omega) (p + 1) mag
    hmag hmW' _ h3 (by simp) (by omega)
  have e5 := WXExec.dec cap (rX P) τ4 (by rw [hp4]; omega)
  rw [hp4, Nat.add_sub_cancel] at e5
  have h5 := h4.setv P hP hPV hP52 p
  obtain ⟨τ6, e6, h6, hk6⟩ := tsg_emitB cap hW sg mag hsg1 hmW _ h5 (by omega)
  refine ⟨τ6, WXExec.mono (WXExec.seq (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) e6)
    (by have := Nat.mul_le_mul_right (83 * Wb + 30) hsg1; unfold emitCost; omega), h6, ?_, fun j hj => ?_⟩
  · rw [hk6 P (by simp; omega)]; simp
  · rw [hk6 j hj]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hj
    by_cases hjP : j = P
    · subst hjP; simp [hp]
    · have hj5 : j ≠ 5 := fun e => hj.1 (by rw [e]; rfl)
      simp only [WState.setv_val, Function.update_of_ne (rX_ne hjP)]
      rw [hk4 j (by simp; omega) hjP]
      simp only [WState.setv_val, Function.update_of_ne (rX_ne hjP)]
      rw [hk2 j hj5, hk1 j (by simp; omega) hjP]

end TSgSteps

end NearCubicGates.Close.Expand.PolyTab
