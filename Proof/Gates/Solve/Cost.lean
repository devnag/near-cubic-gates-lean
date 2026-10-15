import Proof.Gates.Solve.Main2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces.Formats (SysReq sysWord solveWord)

/-- The total cost as a function of `m`, `n`, `ℓ` and the width `W`. -/
def mainCostF (m n ℓ W : ℕ) : ℕ :=
  setupCost ℓ + 1 + (buildCost m n ℓ W + 1 + (elimCost (m + n) (n + 1) n (ucost W ((m + n) * (n + 1))) + 1 +
    (outCost W ((m + n) * (n + 1)) (n + 1) m n + 1 + (rewOutCost W n + 1 +
      64 * (3 * (setupCap ℓ + capB ℓ ℓ ℓ W + capE (2 * ℓ * (ℓ + 1)) W + ℓ + 2 * (W + 1) + 2) + 2)))))

theorem mainCost_eq (s : SysReq) :
    mainCost s = mainCostF s.rows.length s.pts.length (sysWord s).length (wOf (sysWord s).length) := by
  unfold mainCost mainCostF capT; simp only [List.length_finRange]

theorem mainCostF_mono {m n ℓ W M : ℕ} (hm : m ≤ M) (hn : n ≤ M) (hℓ : ℓ ≤ M) (hW : W ≤ M) :
    mainCostF m n ℓ W ≤ mainCostF M M M M := by
  simp only [mainCostF, setupCost, buildCost, buildACost, buildBCost, ptsCost, ptCost, rowsCost, rowCost, rowACost,
    rowBCost, cellCost, identCost, idRowCost, elimCost, colCost, ucost, outCost, chkCost, okCost, wordNCost,
    printCost, entCost, entACost, entBCost, euclidCost, rewOutCost, rewBodyCost, setupCap, capB, capP, capC, capE,
    NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost]
  gcongr

theorem mainCostF_poly (M : ℕ) (hM : 1 ≤ M) : mainCostF M M M M ≤ 10 ^ 8 * M ^ 7 := by
  simp only [mainCostF, setupCost, buildCost, buildACost, buildBCost, ptsCost, ptCost, rowsCost, rowCost, rowACost,
    rowBCost, cellCost, identCost, idRowCost, elimCost, colCost, ucost, outCost, chkCost, okCost, wordNCost,
    printCost, entCost, entACost, entBCost, euclidCost, rewOutCost, rewBodyCost, setupCap, capB, capP, capC, capE,
    NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost]
  ring_nf
  have h0 : 1 ≤ M ^ 7 := Nat.one_le_pow _ _ hM
  have h1 : M ≤ M ^ 7 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  have h2 : M ^ 2 ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  have h3 : M ^ 3 ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  have h4 : M ^ 4 ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  have h5 : M ^ 5 ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  have h6 : M ^ 6 ≤ M ^ 7 := Nat.pow_le_pow_right hM (by norm_num)
  omega

/-- The class constant. -/
def costK : ℕ := 10 ^ 8 * 8 ^ 7

/-- **The cost class**: `mainCost s ≤ costK · (|sysWord s| + 1)^14`. -/
theorem mainCost_le (s : SysReq) : mainCost s ≤ costK * ((sysWord s).length + 1) ^ 14 := by
  rw [mainCost_eq]
  set ℓ := (sysWord s).length
  have hW : wOf ℓ = 8 * (ℓ + 1) ^ 2 := rfl
  have hℓW : ℓ ≤ wOf ℓ := by rw [hW]; nlinarith
  have h1 := mainCostF_mono (M := wOf ℓ) (le_trans (rows_len_le s) hℓW) (le_trans (pts_len_le s) hℓW) hℓW le_rfl
  have h2 := mainCostF_poly (wOf ℓ) (by rw [hW]; nlinarith)
  have h3 : 10 ^ 8 * wOf ℓ ^ 7 = costK * (ℓ + 1) ^ 14 := by rw [hW, costK]; ring
  omega

end NearCubicGates.Close.Solve
