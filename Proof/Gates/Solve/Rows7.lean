import Proof.Gates.Solve.Rows6

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
open NearCubicWires.RepairRepresentation (natWord)

def rowB : WMX NS NR :=
  .seq (BinW.zero wB wZ rF rR) (.seq (CounterMachine.natRead sRAW sRUL wB rCA rR2 rCW) (.seq (BinW.shl wB wZ rF rR)
  (.seq (addR rNN rLP2 rTa) (.seq (.whr rLP2 (.seq (WMX.dec rLP2) cellP)) (.seq (appendRecX wB sMAT rCS rCM)
  (.seq (.wm (WM.clear rPB)) (.seq (.wm (WM.clear rSLN)) (.ifr rNZQ (WMX.dec rNZQ) WMX.skip))))))))

/-- The registers of a row. -/
def rowRegs : List Reg := rNZQ :: rSLN :: rPB :: rLP2 :: cellRegs

/-- The cost bound of `rowB`. -/
def rowBCost (n ℓ U : ℕ) : ℕ := (n + 2) * (cellCost ℓ U + 4) + 10 * U

theorem rowB_spec (cap : ℕ) {σ0 σ : MS} {W ℓ : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {word : List Bool}
    (hc : RawCtx σ0 W word) {pts : List (List ℤ)} {σl : List ℕ} {jS jP : List Bool}
    (hcc : CellCtx σ0 W ℓ pts σl jS jP) (q b : ℕ) (pre rest : List Bool) (hword : word = pre ++ natWord b ++ rest)
    (hsh : σ0.sh sRAW = pre.length) (hNZQ : σ0.val rNZQ = (decide (q ≠ 0)).toNat) (hvq : v wQ = q)
    (hvT : v wTWO = 2) (hvZ : v wZ = 0) (hSLN : σ0.val rSLN = σl.length) (hLL : σ0.val rLL = ℓ)
    (hNN : σ0.val rNN = pts.length) (hPB : σ0.val rPB = 0) (hLP2 : σ0.val rLP2 = 0)
    (hz : ∀ r ∈ cellRegs, σ0.val r = 0) (hσl : σl.length ≤ ℓ) (hσb : ∀ x ∈ σl, x < 2 ^ ℓ)
    (hub : ∀ u ∈ pts, ∀ z ∈ u, z.natAbs < 2 ^ ℓ) (hq : q < 2 ^ ℓ) (hb : b < 2 ^ ℓ) (hℓW : ℓ + 2 ≤ W) (hℓ1 : 1 ≤ ℓ)
    {out L0 : List Bool} (hout : OutOn σ0 sMAT rCM out L0) (hcap : capC (pts.length * ℓ + ℓ) W ≤ cap)
    (hcapO : out.length + (pts.length + 2) * (2 * (W + 1) + 1) + 2 ≤ cap) :
    Runs cap rowB σ (rowBCost pts.length ℓ (ucost W (pts.length * ℓ + ℓ))) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      σ1.st sRAW = σ0.st sRAW ∧ σ1.sh sRAW = pre.length + (natWord b).length ∧
      OutOn σ1 sMAT rCM (out ++ recBits W (entVals q σl pts pts.length ++ [encS (b : ℤ)])) L0 ∧
      (∀ r ∈ rowRegs, σ1.val r = 0) ∧ SameExcept σ0 σ1 [sRAW, sMAT] (rCM :: rowRegs) ∧ v1 wZ = 0 ∧ v1 wTWO = 2) := by
  set n := pts.length with hn
  set N := n * ℓ + ℓ with hN
  set U := ucost W N with hU
  have hU16 := one_le_ucost W N
  have hUL := lin_le_ucost W N
  have hUN := ucost_geN W N
  have hcapC := hcap
  unfold capC at hcapC
  have hcW : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < N + 2 by omega); omega
  have hc4 : 4 * (W + 1) + 4 ≤ cap := by
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show 2 ≤ N + 2 by omega); omega
  have hpow : 2 ^ ℓ * 4 ≤ 2 ^ W := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnN : n ≤ N := by rw [hN]; have := Nat.le_mul_of_pos_right n (show 0 < ℓ by omega); omega
  have hnl : n * ℓ ≤ N := by omega
  have hcost : U + 1 + (60 * (W + 2) + 1 + (U + 1 + (U + 1 + ((n * (cellCost ℓ U + 4) + 1) + 1 + (U + 1 +
      (U + 1 + (U + 1 + 2))))))) ≤ rowBCost n ℓ U := by
    unfold rowBCost
    have e : (n + 2) * (cellCost ℓ U + 4) = n * (cellCost ℓ U + 4) + 2 * (cellCost ℓ U + 4) := by ring
    omega
  refine Runs.cost ?_ hcost
  -- 1. `wB := encS b`
  refine Runs.seq ((opZero cap h (X := wB) (by decide) (by decide) hcW).cost (show 41 * (W + 1) + 3 ≤ U by omega))
    (fun τ1 h1 => ?_)
  refine Runs.seq (opNatRead cap h1 (X := wB) (by decide) (by simp) b pre rest (by rw [hc.raw, hword]) hsh hc.rul
    hc.rulh hc.R2 (by rw [pow_succ]; omega) hc4) (fun τ2 h2 => ?_)
  set σ2 := σ0.seth sRAW (pre.length + (natWord b).length) with hσ2
  refine Runs.seq ((opShl cap h2 (X := wB) (by decide) (by decide) hcW).cost (show 41 * (W + 1) + 8 ≤ U by omega))
    (fun τ3 h3 => ?_)
  set v3 := Function.update (Function.update (Function.update v wB 0) wB b) wB
    (2 * Function.update (Function.update v wB 0) wB b wB) with hv3
  have hv3B : v3 wB = encS (b : ℤ) := by simp [hv3, encS_nat]

  refine Runs.seq ((opAddR cap h3 (A := rNN) (B := rLP2) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ2, hLP2, hNN]; omega)).cost
    (show 18 * σ2.val rNN + 3 ≤ U by simp (config := {decide := true}) [hσ2, hNN]; omega)) (fun τ4 h4 => ?_)
  set σ4 := σ2.setv rLP2 (σ2.val rLP2 + σ2.val rNN) with hσ4
  have hfr04 : SameExcept σ0 σ4 [sRAW] [rLP2] :=
    SameExcept.trans (sameExcept_seth σ0 (by simp) _) (sameExcept_setv _ (by simp) _)
  have hcc4 : CellCtx σ4 W ℓ pts σl jS jP :=
    ⟨by rw [hfr04.st (by decide), hcc.sg], by rw [hfr04.sh (by decide), hcc.sgh], by rw [hfr04.st (by decide), hcc.pt],
      by rw [hfr04.sh (by decide), hcc.pth]⟩
  -- 3. the entries
  have hI0 : CellsInv σ4 W ℓ q σl pts out L0 v3 0 τ4 := by
    refine ⟨σ4, v3, h4, by simpa [entVals, recBits] using OutOn.same hout hfr04 (by decide) (by decide),
      by simp (config := {decide := true}) [hσ4, hσ2, hPB], fun r hr => ?_, SameExcept.refl _ _ _, fun _ _ => rfl⟩
    have : r ∉ [rLP2] := by
      simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hfr04.val this]; exact hz r hr
  have hloop := Runs.count (cap := cap) (K := rLP2) (body := cellP) (cellCost ℓ U) n
    (CellsInv σ4 W ℓ q σl pts out L0 v3) (by omega)
    (fun j hj τ hτ _ => cells_step cap hcc4 (by rw [hfr04.val (by decide), hNZQ]) v3
      (by simp (config := {decide := true}) [hv3, hvq]) (by simp (config := {decide := true}) [hv3, hvT]) hσl hσb hub hq
      hℓW (by rw [hfr04.val (by decide), hSLN]) (by rw [hfr04.val (by decide), hLL]) hcap
      (by rw [← hn]; have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show n + 1 ≤ n + 2 by omega); omega) j hj τ hτ)
      τ4 hI0
    (by rw [h4.val (by decide)]; simp (config := {decide := true}) [hσ4, hσ2, hLP2, hNN])
  refine Runs.seq hloop (fun τ5 ⟨⟨σ5, v5, h5, hout5, hPB5, hz5, hfr5, hkeep5⟩, hK5⟩ => ?_)
  -- 4. append `encS b`
  have hlen5 : (out ++ recBits W (entVals q σl pts n)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [List.length_append, recBits_length]; simp only [entVals, List.length_map, List.length_range]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show n + 1 ≤ n + 2 by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  refine Runs.seq ((opAppend cap h5 (X := wB) (O := sMAT) (CO := rCM) (by decide) (by decide) (by decide) hout5
    hlen5).cost (show 40 * (W + 1) + 11 ≤ U by omega)) (fun τ6 h6 => ?_)
  rw [hkeep5 wB (by decide), hv3B] at h6
  set σ6 := ((σ5.sets sMAT (overlay (out ++ recBits W (entVals q σl pts n) ++ frame (binary (W + 1) (encS (b : ℤ)))) L0)).seth
    sMAT (out ++ recBits W (entVals q σl pts n) ++ frame (binary (W + 1) (encS (b : ℤ)))).length).setv rCM
    (out ++ recBits W (entVals q σl pts n) ++ frame (binary (W + 1) (encS (b : ℤ)))).length with hσ6
  -- 5. clears
  have h6PB : σ6.val rPB = n * ℓ := by simp (config := {decide := true}) [hσ6, hPB5]
  refine Runs.seq ((opClearR cap h6 (r := rPB) (by decide) (by rw [h6PB]; omega)).cost
    (show 3 * σ6.val rPB + 1 ≤ U by rw [h6PB]; omega)) (fun τ7 h7 => ?_)
  have h7SLN : (σ6.setv rPB 0).val rSLN = σl.length := by
    simp (config := {decide := true}) [hσ6]; rw [hfr5.val (by decide), hfr04.val (by decide), hSLN]
  refine Runs.seq ((opClearR cap h7 (r := rSLN) (by decide) (by rw [h7SLN]; omega)).cost
    (show 3 * (σ6.setv rPB 0).val rSLN + 1 ≤ U by rw [h7SLN]; omega)) (fun τ8 h8 => ?_)
  set σ8 := (σ6.setv rPB 0).setv rSLN 0 with hσ8
  have h8NZQ : σ8.val rNZQ = (decide (q ≠ 0)).toNat := by
    simp (config := {decide := true}) [hσ8, hσ6]; rw [hfr5.val (by decide), hfr04.val (by decide), hNZQ]; simp
  have hstep : Runs cap (.ifr rNZQ (WMX.dec rNZQ) WMX.skip) τ8 2 (fun ρ => At (σ8.setv rNZQ 0) ρ W v5) := by
    by_cases hq0 : q = 0
    · have hv : τ8.val rNZQ = 0 := by rw [h8.val (by decide), h8NZQ]; simp [hq0]
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ8) ?_)).cost (by omega)
      have e : σ8.setv rNZQ 0 = σ8 := by
        have : σ8.val rNZQ = 0 := by rw [h8NZQ]; simp [hq0]
        rw [← this, wsetv_same]
      rw [e]; exact h8
    · have hv : τ8.val rNZQ ≠ 0 := by rw [h8.val (by decide), h8NZQ]; simp [hq0]
      refine (Runs.ifrT hv ((opDecR cap h8 (r := rNZQ) (by decide) (by rw [h8NZQ]; simp [hq0]; omega)).post
        (fun ρ hρ => ?_))).cost (by omega)
      rw [h8NZQ] at hρ; simp [hq0] at hρ; exact hρ
  refine hstep.post (fun τ9 h9 => ⟨_, v5, h9, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp (config := {decide := true}) [hσ8, hσ6]; rw [hfr5.st (by decide)]; simp [hσ4, hσ2]
  · simp (config := {decide := true}) [hσ8, hσ6]; rw [hfr5.sh (by decide)]; simp [hσ4, hσ2]
  · refine ⟨by simp (config := {decide := true}) [hσ8, hσ6, recBits_append, recBits, List.append_assoc],
      by simp (config := {decide := true}) [hσ8, hσ6, recBits_append, recBits],
      by simp (config := {decide := true}) [hσ8, hσ6, recBits_append, recBits]⟩
  · intro r hr
    simp only [rowRegs, List.mem_cons] at hr
    rcases hr with rfl | rfl | rfl | rfl | hr
    · simp
    · simp (config := {decide := true}) [hσ8]
    · simp (config := {decide := true}) [hσ8]
    · simp (config := {decide := true}) [hσ8, hσ6]; rw [← h5.val (by decide)]; exact hK5
    · have h1 : r ≠ rNZQ ∧ r ≠ rSLN ∧ r ≠ rPB ∧ r ≠ rCM := by
        simp only [cellRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp [hσ8, hσ6, Function.update_of_ne h1.1, Function.update_of_ne h1.2.1, Function.update_of_ne h1.2.2.1,
        Function.update_of_ne h1.2.2.2, hz5 r hr]
  · refine SameExcept.trans (hfr04.weaken (by simp) (by simp [rowRegs])) (SameExcept.trans (hfr5.weaken (by simp)
      (by simp [rowRegs, cellRegs])) ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩)
    · have : x ≠ sMAT := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx; exact hx.2
      simp [hσ8, hσ6, Function.update_of_ne this]
    · simp only [rowRegs, cellRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hσ8, hσ6, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
        Function.update_of_ne hr.2.2.2.1]
    · simp [hσ8, hσ6]
  · rw [hkeep5 wZ (by decide)]; simp (config := {decide := true}) [hv3, hvZ]
  · rw [hkeep5 wTWO (by decide)]; simp (config := {decide := true}) [hv3, hvT]

end NearCubicGates.Close.Solve
