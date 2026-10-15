import Proof.Gates.Expand.PolyTabStage8

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

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- `rX D := field rX P` of the request table. -/
def fetchR (P D : Fin 64) : WX :=
  .seq (getAt (sS 3) (U0 4) (rX 0) (rX 1) (rX P) (rX 9)) <|
  .seq (toReg (U0 4) (U0 8) (U0 9) (rX 5) (rX 3) (rX 4) (rX 6)) <|
  .seq (addR (rX 5) (rX D) (rX 7)) (.wm (WM.clear (rX 5)))

def fetchCost (Wb N x : ℕ) : ℕ :=
  gaCost Wb N + 1 + (x * (83 * Wb + 30) + 41 * Wb + 14 + 1 + (18 * x + 3 + 1 + (3 * x + 1)))

theorem fetchR_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (P D : Fin 64) (hP : P.val ∉ [0, 1, 9]) (hD : D.val ∉ [0, 1, 9, 3, 4, 6, 5, 29, 20, 7])
    (hDV : rX D ∈ (RVL : List (Fin NRk))) (hD52 : D.val < 52) (p x : ℕ) (hx : (preN r)[p]? = some x)
    (hxW : x < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ) (hp : τ.val (rX P) = p)
    (hD0 : τ.val (rX D) = 0)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 2 * (preN r).length + 2 * Wb + x + 4 ≤ cap) :
    Runs cap (fetchR P D) τ (fetchCost Wb (preN r).length x)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV ρ ∧
        ρ.val (rX D) = x ∧ ∀ j : Fin 64, j ≠ D → j ≠ 5 → ρ.val (rX j) = τ.val (rX j)) := by
  have hD' := hD
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hD'
  obtain ⟨d0, d1, d9, d3, d4, d6, d5, d29, d20, d7⟩ := hD'
  obtain ⟨τ1, e1, h1, hp1, hk1⟩ :=
    tsg_getAt cap Wb r hW inp hd σA outV 0 (fun _ => True) P hP p x hx hxW τ hI hp (by omega)
  obtain ⟨τ2, e2, h2, hk2⟩ := tsg_toReg cap hW x hxW τ1 h1 (by omega)
  have h25 : τ2.val (rX 5) = x := h2.z5
  have rD5 : rX 5 ≠ rX D := rX_ne (fun e => d5 (by rw [← e]; rfl))
  have rD7 : rX D ≠ rX 7 := rX_ne (fun e => d7 (by rw [e]; rfl))
  have hD2 : τ2.val (rX D) = 0 := by
    rw [hk2 D (fun e => d5 (by rw [e]; rfl))]
    by_cases hDP : D = P
    · subst hDP; rw [hp1]; rw [hD0] at hp; omega
    · rw [hk1 D (by simp; omega) hDP, hD0]
  have e3 := addR_spec cap (A := rX 5) (B := rX D) (T := rX 7) rD5 (by polyTabNe) rD7 τ2 h2.z7 (by rw [hD2, h25]; omega)
  rw [hD2, h25, zero_add] at e3
  have h3 := h2.setv D hD hDV hD52 x
  have e4 := wclear_spec (cap := cap) (rX 5) x (τ2.setv (rX D) x) (by simp [Function.update_of_ne rD5, h25])
    (by simp [Function.update_of_ne rD5, h25]; omega)
  have hfin : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV
      ((τ2.setv (rX D) x).setv (rX 5) 0) := by
    obtain ⟨⟨v, hv, hv8, hv9, hq⟩, hO, h0, h1', h9, h3', h4, h6, h5, h29, h7, htb, htbh, hfr⟩ := h3
    exact ⟨⟨v, evv_setv hv 5 (by decide) 0, hv8, hv9, trivial⟩, ⟨by simp [hO.1], by simp [hO.2.1],
      by simp [hO.2.2]⟩, by simp [h0], by simp [h1'], by simp [h9], by simp [h3'], by simp [h4], by simp [h6], by simp,
      by simp [h29], by simp [h7], by simp [htb], by simp [htbh],
      se_ext hfr (sameExcept_setv (S := []) _ (List.mem_singleton_self _) 0) (by simp)
        (fun q hq => by simp at hq; subst hq; unfold RVL; simp)⟩
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.wm e4)))) (by unfold fetchCost; omega),
    hfin, by simp [Function.update_of_ne rD5.symm], fun j hjD hj5 => ?_⟩
  simp only [WState.setv_val, Function.update_of_ne (rX_ne hjD), Function.update_of_ne (rX_ne hj5)]
  rw [hk2 j hj5]
  by_cases hjP : j = P
  · subst hjP; rw [hp1, hp]
  · by_cases hj20 : j = 20
    · subst hj20; rw [h1.out.2.2, hI.out.2.2]
    · rw [hk1 j (by simp; omega) hjP]

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms.SInt (encS)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- One coordinate: `rX 23` points at its index field, `rX 17` is the gate's block base. -/
def coordStep : WX :=
  .seq (fetchR 23 16) <| .seq (addR (rX 17) (rX 21) (rX 7)) <| .seq (WMX.inc (rX 21)) <|
  .seq (addR (rX 16) (rX 21) (rX 7)) <| .seq (addR (rX 16) (rX 21) (rX 7)) <| .seq (.wm (WM.clear (rX 16))) <|
  .seq (emitW 21) <| .seq (.wm (WM.clear (rX 21))) (WMX.inc (rX 23))

theorem encS_eq (z : ℤ) : encS z = 2 * z.natAbs + wSign z := by unfold encS wSign; rfl

def coordCost (Wb N : ℕ) : ℕ :=
  fetchCost Wb N N + 1 + (18 * N + 3 + 1 + (3 + 1 + (18 * N + 3 + 1 + (18 * N + 3 + 1 + (3 * N + 1 + 1 +
    (emitCost Wb N + 1 + (3 * N + 1 + 1 + 3)))))))

theorem fetchCost_mono (Wb N : ℕ) {x y : ℕ} (h : x ≤ y) : fetchCost Wb N x ≤ fetchCost Wb N y := by
  unfold fetchCost
  have := Nat.mul_le_mul_right (83 * Wb + 30) h
  omega

/-- A register step inside the table phase. -/
theorem ts_reg {Wb : ℕ} {inp : List Bool} {hd : ℕ} {TB : List Bool} {σA : WSt} {outV : List Bool} {τ : WSt}
    (h : TS Wb inp hd TB σA outV τ) (j : Fin 64) (hj : j.val ∈ [16, 17, 21, 22, 24, 25, 43, 23, 26]) (y : ℕ) :
    TS Wb inp hd TB σA outV (τ.setv (rX j) y) :=
  TSg.setv h j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        unfold RVL
        rcases hj with h | h | h | h | h | h | h | h | h <;>
          (have : j = ⟨j.val, j.isLt⟩ := rfl; rw [this]; simp only [h]; simp))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega) y

theorem coordStep_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (q : ℕ) (i : Fin r.n) (hq : (preN r)[q]? = some i.val)
    (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h44 : τ.val (rX 23) = q) (h17 : τ.val (rX 17) = 5 + g.val * (2 * r.n + 3)) (h16 : τ.val (rX 16) = 0)
    (h21 : τ.val (rX 21) = 0)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length + 4 * Wb + 40 ≤ cap) :
    Runs cap coordStep τ (coordCost Wb (preN r).length)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ frame (binary Wb (encS ((r.gates g).weight i)))) ρ ∧ ρ.val (rX 23) = q + 1 ∧
        ρ.val (rX 17) = 5 + g.val * (2 * r.n + 3) ∧ ρ.val (rX 16) = 0 ∧ ρ.val (rX 21) = 0 ∧
        ∀ j : Fin 64, j.val ∉ [5, 20, 16, 21, 23] → ρ.val (rX j) = τ.val (rX j)) := by
  set bg := 5 + g.val * (2 * r.n + 3) with hbg
  have hlenP := preN_length r
  have hs := preN_wsign r g i
  have hm := preN_wmag r g i
  have hqN : q < (preN r).length := by by_contra hc; rw [List.getElem?_eq_none (by omega)] at hq; exact absurd hq (by simp)
  have hpN : bg + (2 + 2 * i.val) < (preN r).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; exact absurd hm (by simp)
  have hnks : r.n = r.k + r.s := by
    have := Fintype.card_congr r.layout; simpa using this
  have hiN : i.val < (preN r).length := by
    have := i.isLt; have : pV r = 5 + r.G * (2 * r.n + 3) + r.k + 1 + r.s + 1 + 2 ^ r.k + 1 := rfl
    omega
  have hil := i.isLt
  have hmB := ((r.hB g).1 i)
  -- fetch the index
  obtain ⟨τ1, e1, h1, h116, hk1⟩ := fetchR_spec cap Wb r hW inp hd σA outV 23 16 (by decide) (by decide)
    (by unfold RVL; simp) (by decide) q i.val hq (by omega) τ hI h44 h16 (by omega)
  have e1' := WXExec.mono e1 (fetchCost_mono Wb (preN r).length (show i.val ≤ (preN r).length by omega))
  -- `rX 21 := bg + 1 + 2i`
  have v1_17 : τ1.val (rX 17) = bg := by rw [hk1 17 (by decide) (by decide), h17]
  have v1_21 : τ1.val (rX 21) = 0 := by rw [hk1 21 (by decide) (by decide), h21]
  have e2 := addR_spec cap (A := rX 17) (B := rX 21) (T := rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe) τ1 h1.z7
    (by rw [v1_17, v1_21]; omega)
  rw [v1_17, v1_21, zero_add] at e2
  have h2 := ts_reg h1 21 (by simp) bg
  have e3 := WXExec.inc cap (rX 21) (τ1.setv (rX 21) bg) (by simp; omega)
  have h3 := ts_reg h2 21 (by simp) (bg + 1)
  simp only [WState.setv_val, Function.update_self] at e3
  set τ3 := (τ1.setv (rX 21) bg).setv (rX 21) (bg + 1) with hτ3
  have v3_16 : τ3.val (rX 16) = i.val := by simp [hτ3, h116]
  have v3_21 : τ3.val (rX 21) = bg + 1 := by simp [hτ3]
  have e4 := addR_spec cap (A := rX 16) (B := rX 21) (T := rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe) τ3 h3.z7
    (by rw [v3_16, v3_21]; omega)
  rw [v3_16, v3_21] at e4
  have h4 := ts_reg h3 21 (by simp) (bg + 1 + i.val)
  set τ4 := τ3.setv (rX 21) (bg + 1 + i.val) with hτ4
  have v4_16 : τ4.val (rX 16) = i.val := by simp [hτ4, v3_16]
  have e5 := addR_spec cap (A := rX 16) (B := rX 21) (T := rX 7) (by polyTabNe) (by polyTabNe) (by polyTabNe) τ4 h4.z7
    (by rw [v4_16]; simp [hτ4]; omega)
  rw [v4_16, show τ4.val (rX 21) = bg + 1 + i.val by simp [hτ4]] at e5
  have h5 := ts_reg h4 21 (by simp) (bg + 1 + i.val + i.val)
  set τ5 := τ4.setv (rX 21) (bg + 1 + i.val + i.val) with hτ5
  have e6 := wclear_spec (cap := cap) (rX 16) i.val τ5 (by simp [hτ5, v4_16]) (by simp [hτ5, v4_16]; omega)
  have h6 := ts_reg h5 16 (by simp) 0
  set τ6 := τ5.setv (rX 16) 0 with hτ6
  have hp6 : τ6.val (rX 21) = bg + (1 + 2 * i.val) := by simp [hτ6, hτ5]; ring
  obtain ⟨τ7, e7, h7, hp7, hk7⟩ := emitW_spec cap Wb r hW inp hd σA outV 21 (by decide) (by unfold RVL; simp)
    (by decide) (bg + (1 + 2 * i.val)) _ _ hs (by rw [show bg + (1 + 2 * i.val) + 1 = bg + (2 + 2 * i.val) by ring]; exact hm)
    (by unfold wSign; split_ifs <;> omega) (by omega) τ6 h6 hp6 (by omega)
  have e8 := wclear_spec (cap := cap) (rX 21) _ τ7 hp7 (by omega)
  have h8 := ts_reg h7 21 (by simp) 0
  have v8_44 : (τ7.setv (rX 21) 0).val (rX 23) = q := by
    simp only [WState.setv_val, Function.update_of_ne (show rX 23 ≠ rX 21 by polyTabNe)]
    rw [hk7 23 (by decide)]; simp [hτ6, hτ5, hτ4, hτ3, hk1 23 (by decide) (by decide), h44]
  have e9 := WXExec.inc cap (rX 23) (τ7.setv (rX 21) 0) (by rw [v8_44]; omega)
  rw [v8_44] at e9
  have h9 := ts_reg h8 23 (by simp) (q + 1)
  refine ⟨_, WXExec.mono (WXExec.seq e1' <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <|
    WXExec.seq (WXExec.wm e6) <| WXExec.seq e7 <| WXExec.seq (WXExec.wm e8) e9) (by unfold coordCost; nlinarith), ?_,
    by simp, ?_, ?_, by simp, fun j hj => ?_⟩
  · rw [encS_eq]; exact h9
  · simp only [WState.setv_val, Function.update_of_ne (show rX 17 ≠ rX 23 by polyTabNe),
      Function.update_of_ne (show rX 17 ≠ rX 21 by polyTabNe)]
    rw [hk7 17 (by decide)]; simp [hτ6, hτ5, hτ4, hτ3, v1_17]
  · simp only [WState.setv_val, Function.update_of_ne (show rX 16 ≠ rX 23 by polyTabNe),
      Function.update_of_ne (show rX 16 ≠ rX 21 by polyTabNe)]
    rw [hk7 16 (by decide)]; simp [hτ6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    have n44 : rX j ≠ rX 23 := rX_ne (fun e => hj.2.2.2.2 (by rw [e]; rfl))
    have n21 : rX j ≠ rX 21 := rX_ne (fun e => hj.2.2.2.1 (by rw [e]; rfl))
    have n16 : rX j ≠ rX 16 := rX_ne (fun e => hj.2.2.1 (by rw [e]; rfl))
    simp only [WState.setv_val, Function.update_of_ne n44, Function.update_of_ne n21]
    rw [hk7 j (by simp; omega)]
    simp only [hτ6, hτ5, hτ4, hτ3, WState.setv_val, Function.update_of_ne n16, Function.update_of_ne n21]
    exact hk1 j (fun e => hj.2.2.1 (by rw [e]; rfl)) (fun e => hj.1 (by rw [e]; rfl))

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms.SInt (encS)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def coordLoop : WX := .whr (rX 24) (.seq (WMX.dec (rX 24)) coordStep)

/-- The records of the first `k` coordinates. -/
def crecs (Wb : ℕ) (r : TabReq) (g : Fin r.G) {m : ℕ} (ids : Fin m → Fin r.n) (k : ℕ) : List Bool :=
  ((List.ofFn ids).take k).flatMap fun i => frame (binary Wb (encS ((r.gates g).weight i)))

theorem coordLoop_spec (cap Wb : ℕ) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ) (σA : WSt)
    (outV : List Bool) (g : Fin r.G) (q0 m : ℕ) (ids : Fin m → Fin r.n)
    (hids : ∀ j : Fin m, (preN r)[q0 + j.val]? = some (ids j).val)
    (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h24 : τ.val (rX 24) = m) (h44 : τ.val (rX 23) = q0) (h17 : τ.val (rX 17) = 5 + g.val * (2 * r.n + 3))
    (h16 : τ.val (rX 16) = 0) (h21 : τ.val (rX 21) = 0)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length + m * (2 * Wb + 1) +
      4 * Wb + 40 ≤ cap) :
    Runs cap coordLoop τ (m * (coordCost Wb (preN r).length + 4) + 1)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ crecs Wb r g ids m) ρ ∧ ρ.val (rX 23) = q0 + m ∧
        ρ.val (rX 17) = 5 + g.val * (2 * r.n + 3) ∧ ρ.val (rX 16) = 0 ∧ ρ.val (rX 21) = 0 ∧ ρ.val (rX 24) = 0 ∧
        ∀ j : Fin 64, j.val ∉ [5, 20, 16, 21, 23, 24] → ρ.val (rX j) = τ.val (rX j)) := by
  have hcl : ∀ k ≤ m, (crecs Wb r g ids k).length ≤ k * (2 * Wb + 1) := by
    intro k _
    unfold crecs
    rw [List.length_flatMap]
    have : ∀ x ∈ (List.ofFn ids).take k, (frame (binary Wb (encS ((r.gates g).weight x)))).length = 2 * Wb + 1 :=
      fun x _ => by rw [frame_length, binary_length]
    rw [List.map_congr_left this]
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (List.length_take_le _ _)
  let Inv : ℕ → WSt → Prop := fun k ρ =>
    TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA (outV ++ crecs Wb r g ids k) ρ ∧
      ρ.val (rX 23) = q0 + k ∧ ρ.val (rX 17) = 5 + g.val * (2 * r.n + 3) ∧ ρ.val (rX 16) = 0 ∧
      ρ.val (rX 21) = 0 ∧ ∀ j : Fin 64, j.val ∉ [5, 20, 16, 21, 23, 24] → ρ.val (rX j) = τ.val (rX j)
  have hstep : ∀ k < m, ∀ ρ, Inv k ρ → ρ.val (rX 24) = m - k →
      Runs cap coordStep (ρ.setv (rX 24) (m - k - 1)) (coordCost Wb (preN r).length)
        (fun μ => Inv (k + 1) μ ∧ μ.val (rX 24) = m - k - 1) := by
    intro k hk ρ ⟨hρ, r44, r17, r16, r21, rk⟩ _
    have hck := hcl k hk.le
    refine (coordStep_spec cap Wb r hW inp hd σA _ g (q0 + k) (ids ⟨k, hk⟩) (hids ⟨k, hk⟩) hWb hBn _
      (ts_reg hρ 24 (by simp) _) (by simp [r44]) (by simp [r17]) (by simp [r16]) (by simp [r21])
      (by
        have : (crecs Wb r g ids k).length + (2 * Wb + 1) ≤ m * (2 * Wb + 1) := by
          have : (k + 1) * (2 * Wb + 1) ≤ m * (2 * Wb + 1) := Nat.mul_le_mul_right _ hk
          nlinarith
        simp only [List.length_append]; omega)).post fun μ ⟨hμ, m44, m17, m16, m21, mk⟩ => ⟨⟨?_, ?_, m17, m16, m21,
        fun j hj => ?_⟩, ?_⟩
    · have e : crecs Wb r g ids (k + 1) = crecs Wb r g ids k ++
          frame (binary Wb (encS ((r.gates g).weight (ids ⟨k, hk⟩)))) := by
        unfold crecs
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp; exact hk)]
        simp
      rw [e, ← List.append_assoc]; exact hμ
    · rw [m44]; ring
    · rw [mk j (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj ⊢; omega)]
      simp only [WState.setv_val]
      rw [Function.update_of_ne (rX_ne (fun e => hj (by rw [e]; simp)))]
      exact rk j hj
    · rw [mk 24 (by decide)]; simp
  have hmc : m ≤ cap := by
    have : m ≤ m * (2 * Wb + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨μ, eμ, ⟨hμ, m44, m17, m16, m21, mk⟩, m24⟩ := Runs.count (cap := cap) (K := rX 24) (body := coordStep)
    (coordCost Wb (preN r).length) m Inv hmc hstep τ ⟨by simpa [crecs] using hI, by simp [h44], h17, h16, h21,
      fun _ _ => rfl⟩ h24
  exact ⟨μ, eμ, hμ, m44, m17, m16, m21, m24, mk⟩

end NearCubicGates.Close.Expand.PolyTab
