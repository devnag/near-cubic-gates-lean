import Proof.Gates.Solve.Rows2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces.Formats (inClass)

def cellP : WMX NS NR :=
  .seq (WMX.inc rFL) (.seq (addR rPB rIXP rTa) (.seq (addR rSLN rLS rTa) (.seq (.whr rLS (.seq (WMX.dec rLS) testP))
  (.seq (BinW.zero wE2 wZ rF rR) (.seq (.ifr rFL (BinW.copy wE2 wTWO rF rR) WMX.skip)
  (.seq (appendRecX wE2 sMAT rCS rCM) (.seq (.ifr rFL (WMX.dec rFL) WMX.skip)
  (.seq (.wm (WM.clear rIXP)) (.seq (.wm (WM.clear rISG)) (addR rLL rPB rTa))))))))))

/-- The registers of a cell. -/
def cellRegs : List Reg := [rFL, rIXP, rISG, rLS, rSGN, rT4]

/-- The cost bound of one entry. -/
def cellCost (ℓ U : ℕ) : ℕ := (ℓ + 2) * (13 * U) + 12 * U

theorem cell_spec (cap : ℕ) {σ0 σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {pts : List (List ℤ)}
    {σl : List ℕ} {jS jP : List Bool} (hc : CellCtx σ0 W ℓ pts σl jS jP) {q : ℕ} {j : ℕ} (hj : j < pts.length)
    (hNZQ : σ0.val rNZQ = (decide (q ≠ 0)).toNat) (hvq : v wQ = q) (hvT : v wTWO = 2)
    (hσl : σl.length ≤ ℓ) (hσb : ∀ x ∈ σl, x < 2 ^ ℓ) (hub : ∀ z ∈ pts[j], z.natAbs < 2 ^ ℓ) (hq : q < 2 ^ ℓ)
    (hℓW : ℓ + 2 ≤ W) (hz : ∀ r ∈ cellRegs, σ0.val r = 0) (hPB : σ0.val rPB = j * ℓ) (hSLN : σ0.val rSLN = σl.length)
    (hLL : σ0.val rLL = ℓ) {out L0 : List Bool} (hout : OutOn σ0 sMAT rCM out L0)
    (hcap : capC (pts.length * ℓ + ℓ) W ≤ cap) (hcapO : out.length + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap cellP σ (cellCost ℓ (ucost W (pts.length * ℓ + ℓ))) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      OutOn σ1 sMAT rCM (out ++ frame (binary (W + 1) (encS (if inClass q σl pts[j] then 1 else 0)))) L0 ∧
      σ1.val rPB = (j + 1) * ℓ ∧ (∀ r ∈ cellRegs, σ1.val r = 0) ∧
      SameExcept σ0 σ1 [sMAT] (rCM :: rPB :: cellRegs) ∧ ∀ X ∈ keepW, v1 X = v X) := by
  set N := pts.length * ℓ + ℓ with hN
  set U := ucost W N with hU
  have hU16 := one_le_ucost W N
  have hUL := lin_le_ucost W N
  have hUN := ucost_geN W N
  unfold capC at hcap
  have hcW : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < N + 2 by omega); omega
  have hjl : j * ℓ + ℓ ≤ N := by
    have : (j + 1) * ℓ ≤ pts.length * ℓ := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, one_mul] at this; omega
  simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨hFL, hIXP, hISG, hLS, hSGN, hT4⟩ := hz
  have hcost : 3 + 1 + (18 * (j * ℓ) + 3 + 1 + (18 * σl.length + 3 + 1 + (σl.length * (12 * U + 4) + 1 + 1 +
      (U + 1 + (U + 1 + 1 + (U + 1 + (2 + 1 + (U + 1 + (U + 1 + (18 * ℓ + 3)))))))))) ≤ cellCost ℓ U := by
    unfold cellCost
    have h1 : σl.length * (12 * U + 4) ≤ (ℓ + 2) * (12 * U + 4) := Nat.mul_le_mul_right _ (by omega)
    have h2 : 18 * (j * ℓ) ≤ 18 * N := by omega
    nlinarith
  refine Runs.cost ?_ hcost
  -- 1. `FL := 1`
  refine Runs.seq (opIncR cap h (r := rFL) (by decide) (by rw [hFL]; omega)) (fun τ1 h1 => ?_)

  refine Runs.seq ((opAddR cap h1 (A := rPB) (B := rIXP) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hIXP, hPB]; omega)).cost (show 18 * (σ0.setv rFL (σ0.val rFL + 1)).val rPB + 3
      ≤ 18 * (j * ℓ) + 3 by simp (config := {decide := true}) [hPB])) (fun τ2 h2 => ?_)
  set σ2 := (σ0.setv rFL (σ0.val rFL + 1)).setv rIXP ((σ0.setv rFL (σ0.val rFL + 1)).val rIXP +
    (σ0.setv rFL (σ0.val rFL + 1)).val rPB) with hσ2
  refine Runs.seq ((opAddR cap h2 (A := rSLN) (B := rLS) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ2, hLS, hSLN]; omega)).cost
      (show 18 * σ2.val rSLN + 3 ≤ 18 * σl.length + 3 by simp (config := {decide := true}) [hσ2, hSLN])) (fun τ3 h3 => ?_)
  set σ3 := σ2.setv rLS (σ2.val rLS + σ2.val rSLN) with hσ3
  have hfr03 : SameExcept σ0 σ3 [] [rISG, rIXP, rFL, rLS] := by
    refine ⟨fun x _ => ⟨rfl, rfl⟩, fun r hr => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ3, hσ2, Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.2]
  have hc3 : CellCtx σ3 W ℓ pts σl jS jP := hc.same hfr03
  -- 4. the tests
  have hI0 : TInv σ3 W q σl pts[j] (j * ℓ) v 0 τ3 := by
    refine ⟨σ3, v, h3, by simp (config := {decide := true}) [hσ3, hσ2, hISG],
      by simp (config := {decide := true}) [hσ3, hσ2, hIXP, hPB], by simp (config := {decide := true}) [hσ3, hσ2, hFL],
      by simp (config := {decide := true}) [hσ3, hσ2, hSGN], by simp (config := {decide := true}) [hσ3, hσ2, hT4],
      SameExcept.refl _ _ _, fun X _ => rfl⟩
  have hloop := Runs.count (cap := cap) (K := rLS) (body := testP) (12 * U) σl.length
    (TInv σ3 W q σl pts[j] (j * ℓ) v) (by omega)
    (fun k hk τ hτ _ => test_step cap hc3 hj (by rw [hfr03.val (by decide), hNZQ]) v hvq hσl hσb hub hq hℓW
      (by unfold capC; omega) k hk τ hτ) τ3 hI0
    (by rw [h3.val (by decide)]; simp (config := {decide := true}) [hσ3, hσ2, hLS, hSLN])
  refine Runs.seq hloop (fun τ4 ⟨⟨σ4, v4, h4, hISG4, hIXP4, hFL4, hSGN4, hT44, hfr4, hkeep4⟩, hK4⟩ => ?_)
  have hFLc : σ4.val rFL = (if inClass q σl pts[j] then 1 else 0) := by
    rw [hFL4]
    by_cases hin : inClass q σl pts[j] = true
    · have := (inClass_iff q σl pts[j]).mp hin; rw [decide_eq_true this, if_pos hin]; rfl
    · have : ¬ ∀ i < σl.length, testOK q σl pts[j] i := fun h' => hin ((inClass_iff q σl pts[j]).mpr h')
      rw [decide_eq_false this, if_neg hin]; rfl
  -- 5. `wE2 := 0`, 6. `wE2 := 2·FL`
  refine Runs.seq ((opZero cap h4 (X := wE2) (by decide) (by decide) hcW).cost
    (show 41 * (W + 1) + 3 ≤ U by omega)) (fun τ5 h5 => ?_)
  set v5 := Function.update v4 wE2 0 with hv5
  have hstep6 : Runs cap (.ifr rFL (BinW.copy wE2 wTWO rF rR) WMX.skip) τ5 (U + 1)
      (fun ρ => ∃ v6, At σ4 ρ W v6 ∧ v6 wE2 = encS (if inClass q σl pts[j] then 1 else 0) ∧
        ∀ X ∈ keepW, v6 X = v X) := by
    have hkeep5 : ∀ X ∈ keepW, v5 X = v X := by
      intro X hX
      have : X ≠ wE2 := by
        simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX; rcases hX with rfl | rfl | rfl | rfl <;> decide
      rw [hv5, Function.update_of_ne this, hkeep4 X hX]
    by_cases hin : inClass q σl pts[j] = true
    · have hv : τ5.val rFL ≠ 0 := by rw [h5.val (by decide), hFLc]; simp [hin]
      refine (Runs.ifrT hv ((opCopy cap h5 (X := wE2) (Y := wTWO) (by decide) (by decide) (by decide) hcW).mono
        (show 41 * (W + 1) + 3 ≤ U by omega) (fun ρ hρ => ⟨_, hρ, ?_, fun X hX => ?_⟩)))
      · simp [hin, encS, hkeep5 wTWO (by decide), hvT]
      · have : X ≠ wE2 := by
          simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX; rcases hX with rfl | rfl | rfl | rfl <;> decide
        rw [Function.update_of_ne this, hkeep5 X hX]
    · have hv : τ5.val rFL = 0 := by rw [h5.val (by decide), hFLc]; simp [hin]
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ5) ⟨v5, h5, ?_, hkeep5⟩)).cost (by omega)
      simp [hv5, hin, encS]
  refine Runs.seq hstep6 (fun τ6 ⟨v6, h6, hv6E, hkeep6⟩ => ?_)
  -- 7. append
  have hout4 : OutOn σ4 sMAT rCM out L0 :=
    OutOn.same hout (SameExcept.trans hfr03 hfr4) (by simp) (by decide)
  refine Runs.seq ((opAppend cap h6 (X := wE2) (O := sMAT) (CO := rCM) (by decide) (by decide) (by decide) hout4
    hcapO).cost (show 40 * (W + 1) + 11 ≤ U by omega)) (fun τ7 h7 => ?_)
  rw [hv6E] at h7
  set σ7 := ((σ4.sets sMAT (overlay (out ++ frame (binary (W + 1) (encS (if inClass q σl pts[j] then 1 else 0)))) L0)).seth
    sMAT (out ++ frame (binary (W + 1) (encS (if inClass q σl pts[j] then 1 else 0)))).length).setv rCM
    (out ++ frame (binary (W + 1) (encS (if inClass q σl pts[j] then 1 else 0)))).length with hσ7
  -- 8. `FL := 0`
  have h7FL : σ7.val rFL = (if inClass q σl pts[j] then 1 else 0) := by
    simp (config := {decide := true}) [hσ7, hFLc]
  have hstep8' : Runs cap (.ifr rFL (WMX.dec rFL) WMX.skip) τ7 2 (fun ρ => At (σ7.setv rFL 0) ρ W v6) := by
    by_cases hin : inClass q σl pts[j] = true
    · have hv : τ7.val rFL ≠ 0 := by rw [h7.val (by decide), h7FL]; simp [hin]
      refine (Runs.ifrT hv ((opDecR cap h7 (r := rFL) (by decide) (by rw [h7FL]; split <;> omega)).post
        (fun ρ hρ => ?_))).cost (by omega)
      rw [h7FL] at hρ; simp [hin] at hρ; exact hρ
    · have hv : τ7.val rFL = 0 := by rw [h7.val (by decide), h7FL]; simp [hin]
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ7) ?_)).cost (by omega)
      have e : σ7.setv rFL 0 = σ7 := by
        have : σ7.val rFL = 0 := by rw [h7FL]; simp [hin]
        rw [← this, wsetv_same]
      rw [e]; exact h7
  refine Runs.seq hstep8' (fun τ8 h8 => ?_)

  have h8IXP : (σ7.setv rFL 0).val rIXP = j * ℓ + σl.length := by
    simp (config := {decide := true}) [hσ7, hIXP4]
  refine Runs.seq ((opClearR cap h8 (r := rIXP) (by decide) (by rw [h8IXP]; omega)).cost
    (show 3 * (σ7.setv rFL 0).val rIXP + 1 ≤ U by rw [h8IXP]; omega)) (fun τ9 h9 => ?_)
  have h9ISG : ((σ7.setv rFL 0).setv rIXP 0).val rISG = σl.length := by
    simp (config := {decide := true}) [hσ7, hISG4]
  refine Runs.seq ((opClearR cap h9 (r := rISG) (by decide) (by rw [h9ISG]; omega)).cost
    (show 3 * ((σ7.setv rFL 0).setv rIXP 0).val rISG + 1 ≤ U by rw [h9ISG]; omega)) (fun τ10 h10 => ?_)
  set σ10 := (((σ7.setv rFL 0).setv rIXP 0).setv rISG 0) with hσ10
  have h10PB : σ10.val rPB = j * ℓ := by
    simp (config := {decide := true}) [hσ10, hσ7]; rw [hfr4.val (by decide), hfr03.val (by decide), hPB]
  have h10LL : σ10.val rLL = ℓ := by
    simp (config := {decide := true}) [hσ10, hσ7]; rw [hfr4.val (by decide), hfr03.val (by decide), hLL]
  refine ((opAddR cap h10 (A := rLL) (B := rPB) (by decide) (by decide) (by decide)
    (by rw [h10PB, h10LL]; omega))).mono (by rw [h10LL]) (fun τ11 h11 => ⟨_, v6, h11, ?_, ?_, ?_, ?_, hkeep6⟩)
  · exact ⟨by simp (config := {decide := true}) [hσ10, hσ7], by simp (config := {decide := true}) [hσ10, hσ7],
      by simp (config := {decide := true}) [hσ10, hσ7]⟩
  · simp (config := {decide := true}) [h10PB, h10LL]; ring
  · intro r hr
    simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simp (config := {decide := true}) [hσ10]
    · simp (config := {decide := true}) [hσ10]
    · simp (config := {decide := true}) [hσ10]
    · simp (config := {decide := true}) [hσ10, hσ7]; rw [← h4.val (by decide)]; exact hK4
    · simp (config := {decide := true}) [hσ10, hσ7, hSGN4]
    · simp (config := {decide := true}) [hσ10, hσ7, hT44]
  · refine SameExcept.trans (hfr03.weaken (by simp) (by simp [cellRegs])) (SameExcept.trans
      (hfr4.weaken (by simp) (by simp [cellRegs])) ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩)
    · have : x ≠ sMAT := by simpa using hx
      simp [hσ10, hσ7, Function.update_of_ne this]
    · simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ10, hσ7, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
        Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.2.2.1]
    · simp [hσ10, hσ7]

end NearCubicGates.Close.Solve
