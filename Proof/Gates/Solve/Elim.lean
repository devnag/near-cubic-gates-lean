import Proof.Gates.Solve.Col

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

/-- The copy-back work stream (not a word). -/
abbrev sWR : Str := 28

theorem lin2_le_ucost (W N : ℕ) : 100 * (N + 1) * (W + 2) ≤ ucost W N := by
  unfold ucost
  have h1 : (W + 2) ≤ (W + 2) ^ 2 := sq_ge W
  have h2 : 100 * (N + 1) ≤ 1000 * (N + 2) := by omega
  calc 100 * (N + 1) * (W + 2) ≤ 1000 * (N + 2) * (W + 2) := Nat.mul_le_mul_right _ h2
    _ ≤ 1000 * (N + 2) * (W + 2) ^ 2 := Nat.mul_le_mul_left _ h1

theorem closeOut_le (W N : ℕ) : 5 * (N * (2 * (W + 1) + 1)) + 3 ≤ ucost W N := by
  have := lin2_le_ucost W N
  have : 5 * (N * (2 * (W + 1) + 1)) + 3 ≤ 100 * (N + 1) * (W + 2) := by nlinarith
  omega

theorem copyAll_le (W N : ℕ) : N * (40 * (W + 1) + 11 + (50 * (W + 1) + 30)) + 3 ≤ ucost W N := by
  have := lin2_le_ucost W N
  have : N * (40 * (W + 1) + 11 + (50 * (W + 1) + 30)) + 3 ≤ 100 * (N + 1) * (W + 2) := by nlinarith
  omega

/-! ## The search -/

def searchP : WMX NS NR :=
  .seq (addR rV rSIX rTa) (.seq (addR rMM rSL rTa) (.seq (.whr rSL (.seq (WMX.dec rSL) searchBody))
    (.seq (.wm (WM.clear rSIX)) (.wm (WM.clear rSB)))))

theorem firstNZ_zero (a : ℕ → ℕ → ℤ) (vv : ℕ) : firstNZ a vv 0 = none := rfl

/-- The cost of the steps of `searchP`. -/
def searchSteps (U m k : ℕ) : ℕ := (2 - k) * (U + 1) + (m * (7 * U + 4) + 1) + 1 + (U + 1 + U)

theorem searchSteps_le (U m : ℕ) (hU : 16 ≤ U) : searchSteps U m 0 ≤ (m + 2) * (8 * U) := by
  unfold searchSteps; nlinarith

theorem search_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C : ℕ} {a : ℕ → ℕ → ℤ}
    {vv Bd : ℕ} {junk : List Bool} (hc : SCtx σ0 W R C a vv Bd junk) (hcap : capE (R * C) W ≤ cap) {m : ℕ}
    (hR1 : 0 < R) (hm : m ≤ R) (hMM : σ0.val rMM = m) (hSIX : σ0.val rSIX = 0) (hSB : σ0.val rSB = 0) (hNZ : σ0.val rNZ = 0)
    (hFD : σ0.val rFD = 0) (hRB : σ0.val rRB = 0) (hSL : σ0.val rSL = 0) {D : ℤ} (hD : v wDD = encS D) :
    Runs cap searchP σ ((m + 2) * (8 * ucost W (R * C))) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      FState σ1 v1 a vv C (piv m a vv) ∧ σ1.val rSIX = 0 ∧ σ1.val rSB = 0 ∧ σ1.val rNZ = 0 ∧ σ1.val rSL = 0 ∧
      SameExcept σ0 σ1 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] ∧ v1 wDD = encS D) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  obtain ⟨N, hN⟩ : ∃ N, N = R * C := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = ucost W N := ⟨_, rfl⟩
  rw [← hN] at cap1 hcap ⊢
  rw [← hUd]
  have hU : 16 ≤ U := hUd ▸ one_le_ucost W N
  have hUN : 4000 * (N + 2) ≤ U := hUd ▸ ucost_geN W N
  have hvC := hc.hv
  have hmC : m * C + C ≤ N + C := by
    rw [hN]; have := Nat.mul_le_mul_right C hm; omega
  have hRN : R ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hCN : C ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hR1
  refine Runs.cost ?_ (searchSteps_le U m hU)
  -- 1. `SIX := vv`
  refine Runs.seq' ((opAddR cap h (A := rV) (B := rSIX) (by decide) (by decide) (by decide)
    (by rw [hSIX, hc.V]; omega)).cost (show 18 * σ0.val rV + 3 ≤ U by rw [hc.V]; omega)) (fun τ1 h1 => ?_)
    (c2 := searchSteps U m 1) (by unfold searchSteps; omega)
  set σ1 := σ0.setv rSIX (σ0.val rSIX + σ0.val rV) with hσ1
  -- 2. `SL := m`
  refine Runs.seq' ((opAddR cap h1 (A := rMM) (B := rSL) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hSL, hMM]; omega)).cost
      (show 18 * σ1.val rMM + 3 ≤ U by simp (config := {decide := true}) [hσ1, hMM]; omega))
    (fun τ2 h2 => ?_) (c2 := searchSteps U m 2) (by unfold searchSteps; omega)
  set σ2 := σ1.setv rSL (σ1.val rSL + σ1.val rMM) with hσ2
  have hfr2 : SameExcept σ0 σ2 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] := by
    refine SameExcept.trans (sameExcept_setv σ0 (by simp) _) (sameExcept_setv σ1 (by simp) _)
  have hc2 : SCtx σ2 W R C a vv Bd junk := hc.same hfr2 (by simp) (by decide)
  have hI0 : SInv σ2 W C a D vv 0 τ2 := by
    refine ⟨σ2, v, h2, by simp (config := {decide := true}) [hσ2, hσ1, hSIX, hc.V],
      by simp (config := {decide := true}) [hσ2, hσ1, hSB], by simp (config := {decide := true}) [hσ2, hσ1, hNZ], ?_,
      SameExcept.refl _ _ _, hD⟩
    rw [firstNZ_zero]
    exact ⟨by simp (config := {decide := true}) [hσ2, hσ1, hFD], by simp (config := {decide := true}) [hσ2, hσ1, hRB]⟩
  have hloop := Runs.count (cap := cap) (K := rSL) (body := searchBody) (7 * U) m (SInv σ2 W C a D vv)
    (by omega) (fun k hk τ hτ _ => by
      have := search_step cap hc2 (by rw [← hN]; exact hcap) hm k hk τ hτ
      rw [← hN, ← hUd] at this; exact this) τ2 hI0
    (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hSL, hMM])
  refine Runs.seq' hloop (fun τ3 ⟨⟨σ3, v3, h3, h3SIX, h3SB, h3NZ, h3F, hfr3, h3D⟩, hK⟩ => ?_)
    (c2 := U + 1 + U) (by unfold searchSteps; omega)
  -- 4. clears
  refine Runs.seq' ((opClearR cap h3 (r := rSIX) (by decide) (by rw [h3SIX]; omega)).cost
    (show 3 * σ3.val rSIX + 1 ≤ U by rw [h3SIX]; omega)) (fun τ4 h4 => ?_) (c2 := U) (by omega)
  refine ((opClearR cap h4 (r := rSB) (by decide) (by simp (config := {decide := true}) [h3SB]; omega)).cost
    (show 3 * (σ3.setv rSIX 0).val rSB + 1 ≤ U by simp (config := {decide := true}) [h3SB]; omega)).post
    (fun τ5 h5 => ⟨_, v3, h5, ?_, by simp (config := {decide := true}), by simp (config := {decide := true}),
      by simp (config := {decide := true}) [h3NZ], ?_, ?_, h3D⟩)
  · have e : piv m a vv = firstNZ a vv m := rfl
    rw [e]
    rcases hf : firstNZ a vv m with _ | r <;> rw [hf] at h3F
    · exact ⟨by simp (config := {decide := true}) [h3F.1], by simp (config := {decide := true}) [h3F.2]⟩
    · exact ⟨by simp (config := {decide := true}) [h3F.1], by simp (config := {decide := true}) [h3F.2.1], h3F.2.2⟩
  · simp (config := {decide := true}); rw [← h3.val (by decide)]; exact hK
  · exact SameExcept.trans hfr2 (SameExcept.trans hfr3 (SameExcept.trans (sameExcept_setv σ3 (by simp) _)
      (sameExcept_setv _ (by simp) _)))

/-! ## The copy back -/

theorem opCopyAll (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (xs : List ℕ) (junk Lm : List Bool)
    (hI : σ0.st sNEW = recStream (xs.map (binary (W + 1))) ++ junk) (hIh : σ0.sh sNEW = 0) (hWh : σ0.sh sWR = 0)
    (hWl : (σ0.st sWR).length ≤ 2 * (W + 1) + 1) (hO : OutOn σ0 sMAT rCM [] Lm)
    (hcap : xs.length * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap (copyAll sNEW sWR sMAT rCA rCW rCS rCM) σ (xs.length * (40 * (W + 1) + 11 + (50 * (W + 1) + 30)) + 3)
      (fun τ => ∃ σ1, At σ1 τ W v ∧ OutOn σ1 sMAT rCM (recBits W xs) Lm ∧ σ1.sh sWR = 0 ∧
        (σ1.st sWR).length ≤ 2 * (W + 1) + 1 ∧ SameExcept σ0 σ1 [sWR, sMAT] [rCM]) := by
  have hO' : OutOn σ sMAT rCM [] Lm := ⟨by rw [h.st (by decide), hO.1], by rw [h.sh (by decide), hO.2.1],
    by rw [h.val (by decide), hO.2.2]⟩
  refine (copyAll_spec cap (I := sNEW) (Wk := sWR) (O := sMAT) (CI := rCA) (CW := rCW) (CS := rCS) (CO := rCM)
    (by decide) (by decide) (W + 1) (by omega) xs σ junk [] Lm (by rw [h.st (by decide), hI])
    (by rw [h.sh (by decide), hIh]) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide))
    (by rw [h.sh (by decide), hWh]) (by rw [h.st (by decide)]; exact hWl) hO' (by omega) (by simp; omega)).post ?_
  rintro τ ⟨hOτ, hWτ, hWlτ, hfr⟩
  obtain ⟨hM1, hM2, hM3, hM4⟩ := h.merge hfr (by decide) (by decide)
  refine ⟨_, hM1, ⟨?_, ?_, ?_⟩, by rw [(hM3 sWR (by decide)).2]; exact hWτ, by rw [(hM3 sWR (by decide)).1]; exact hWlτ,
    hM2⟩
  · rw [(hM3 sMAT (by decide)).1, hOτ.1]; simp [recBits]
  · rw [(hM3 sMAT (by decide)).2, hOτ.2.1]; simp [recBits]
  · rw [hM4 rCM (by decide), hOτ.2.2]; simp [recBits]

/-! ## One column -/

/-- The registers of the elimination that are `0` between columns. -/
def colRegs : List Reg := [rSIX, rSB, rNZ, rFD, rRB, rSL, rIJ, rIV, rRJ, rLJ, rLI, rCN, rCM]

/-- The Bareiss update of column `vv` with the pivot found: pass, close, copy back, `D := P`, clears. -/
def updP : WMX NS NR :=
  .seq passP (.seq (closeOutX sNEW rCN) (.seq (copyAll sNEW sWR sMAT rCA rCW rCS rCM) (.seq (closeOutX sMAT rCM)
    (.seq (BinW.copy wDD wPW rF rR) (.seq (.wm (WM.clear rIJ)) (.seq (WMX.dec rFD) (.wm (WM.clear rRB))))))))

/-- One column: search, then the update if a pivot was found. -/
def colP : WMX NS NR := .seq searchP (.ifr rFD updP WMX.skip)

/-- The state of the elimination before a column. -/
structure ColCtx (σ0 : MS) (W R C m : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (vv Bd : ℕ) (junk : List Bool) : Prop where
  mat : σ0.st sMAT = recStream ((matV R C a).map (binary (W + 1))) ++ junk
  math : σ0.sh sMAT = 0
  newh : σ0.sh sNEW = 0
  wrh : σ0.sh sWR = 0
  wrl : (σ0.st sWR).length ≤ 2 * (W + 1) + 1
  hR1 : 0 < R
  hm : m ≤ R
  hv : vv < C
  RR : σ0.val rRR = R
  CC : σ0.val rCC = C
  MM : σ0.val rMM = m
  V : σ0.val rV = vv
  z : ∀ r ∈ colRegs, σ0.val r = 0
  bd : ∀ i j, i < R → j < C → (a i j).natAbs ≤ Bd
  bD : D.natAbs ≤ Bd
  hW : 2 * Bd * Bd + 1 < 2 ^ W
  D0 : D ≠ 0

/-- The cost bound of one column. -/
def colCost (R C U : ℕ) : ℕ := (R + 2) * (C + 2) * (30 * U)

theorem updCost_le (R C U : ℕ) (hU : 16 ≤ U) (m : ℕ) (hm : m ≤ R) :
    (m + 2) * (8 * U) + 1 + (passCost R C U + 1 + (U + 1 + (U + 1 + (U + 1 + (U + 1 + (U + 1 + (1 + 1 + U)))))) + 1)
      ≤ colCost R C U := by
  unfold passCost colCost
  have h1 : m * U ≤ R * U := Nat.mul_le_mul_right _ hm
  have h2 : 0 ≤ R * C * U := Nat.zero_le _
  have h3 : 0 ≤ C * U := Nat.zero_le _
  have h4 : R ≤ R * U := Nat.le_mul_of_pos_right _ (by omega)
  ring_nf
  ring_nf at h1 h4
  omega

/-- The update registers. -/
def updRegs : List Reg := [rIJ, rIV, rRJ, rLJ, rLI, rCN, rCM, rFD, rRB]

theorem upd_spec (cap : ℕ) {σ1 τ : MS} {W : ℕ} {v1 : Str → ℕ} (h : At σ1 τ W v1) {R C : ℕ} {a : ℕ → ℕ → ℤ}
    {D : ℤ} {r vv Bd : ℕ} {junk : List Bool} (hc : PassCtx σ1 W R C a D r vv Bd junk) (hRR : σ1.val rRR = R)
    (hz : ∀ q ∈ [rIJ, rIV, rRJ, rLJ, rLI, rCN, rCM], σ1.val q = 0) (hFD : σ1.val rFD = 1)
    (hP : v1 wPW = encS (a r vv)) (hD : v1 wDD = encS D) (hnewh : σ1.sh sNEW = 0) (hwrh : σ1.sh sWR = 0)
    (hwrl : (σ1.st sWR).length ≤ 2 * (W + 1) + 1) (hcap : capE (R * C) W ≤ cap) :
    Runs cap updP τ (passCost R C (ucost W (R * C)) + 1 + (ucost W (R * C) + 1 + (ucost W (R * C) + 1 +
      (ucost W (R * C) + 1 + (ucost W (R * C) + 1 + (ucost W (R * C) + 1 + (1 + 1 + ucost W (R * C))))))))
      (fun τ' => ∃ σ2 v2 junk', At σ2 τ' W v2 ∧
        σ2.st sMAT = recStream ((matV R C (upd a D r vv)).map (binary (W + 1))) ++ junk' ∧ σ2.sh sMAT = 0 ∧
        σ2.sh sNEW = 0 ∧ σ2.sh sWR = 0 ∧ (σ2.st sWR).length ≤ 2 * (W + 1) + 1 ∧ (∀ q ∈ updRegs, σ2.val q = 0) ∧
        SameExcept σ1 σ2 [sMAT, sNEW, sWR] updRegs ∧ v2 wDD = encS (a r vv)) := by
  obtain ⟨cap1, cap2, cap3⟩ := cap_facts hcap
  have hU := one_le_ucost W (R * C)
  have hUN := ucost_geN W (R * C)
  have hz' : ∀ q ∈ [rIJ, rIV, rRJ, rLJ, rLI, rCN, rCM], σ1.val q = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz'
  obtain ⟨hIJ, hIV, hRJ, hLJ, hLI, hCN, hCM⟩ := hz'
  -- 1. the pass
  refine Runs.seq (pass_spec cap h hc hRR hIJ hIV hRJ hLJ hLI hP hD (outOn_start σ1 sNEW rCN hnewh hCN) hcap)
    (fun τ2 ⟨σ2, v2, h2, hout2, hIJ2, hIV2, hRJ2, hLJ2, hLI2, hfr2, hP2, hD2⟩ => ?_)
  have hlen : (recBits W (matV R C (upd a D r vv))).length = R * C * (2 * (W + 1) + 1) := by
    rw [recBits_length, matV_length]
  -- 2. close `NEW`
  refine Runs.seq ((opCloseOut cap h2 (O := sNEW) (CO := rCN) (by decide) (by decide) hout2
    (by rw [hlen]; omega)).cost (by rw [hlen]; exact closeOut_le W (R * C))) (fun τ3 h3 => ?_)
  set σ3 := ((σ2.sets sNEW (overlay (recBits W (matV R C (upd a D r vv)) ++ [false]) (σ1.st sNEW))).seth sNEW 0).setv
    rCN 0 with hσ3
  have hfr2' := hfr2
  have h3new : σ3.st sNEW = recStream ((matV R C (upd a D r vv)).map (binary (W + 1))) ++
      (σ1.st sNEW).drop (recBits W (matV R C (upd a D r vv)) ++ [false]).length := by
    simp [hσ3, overlay, recStream_eq]
  have hfr13 : SameExcept σ1 σ3 [sNEW] [rCN, rIJ, rIV, rRJ, rLJ, rLI] := by
    refine SameExcept.trans hfr2 ?_
    refine SameExcept.trans (sameExcept_sets σ2 (by simp) _) (SameExcept.trans (sameExcept_seth _ (by simp) _)
      (sameExcept_setv _ (by simp) _))
  -- 3. copy back
  have hMAT0 : OutOn σ3 sMAT rCM [] (σ3.st sMAT) := outOn_start σ3 sMAT rCM
    (by rw [hfr13.sh (by decide), hc.math]) (by rw [hfr13.val (by decide), hCM])
  refine Runs.seq ((opCopyAll cap h3 (matV R C (upd a D r vv)) _ (σ3.st sMAT) h3new (by simp [hσ3])
    (by rw [hfr13.sh (by decide), hwrh]) (by rw [hfr13.st (by decide)]; exact hwrl) hMAT0
    (by rw [matV_length]; omega)).cost (by rw [matV_length]; exact copyAll_le W (R * C)))
    (fun τ4 ⟨σ4, h4, hout4, hwh4, hwl4, hfr4⟩ => ?_)
  -- 4. close `MAT`
  have hlen4 : (recBits W (matV R C (upd a D r vv))).length ≤ cap := by rw [hlen]; omega
  refine Runs.seq ((opCloseOut cap h4 (O := sMAT) (CO := rCM) (by decide) (by decide) hout4 hlen4).cost
    (by rw [hlen]; exact closeOut_le W (R * C))) (fun τ5 h5 => ?_)
  set σ5 := ((σ4.sets sMAT (overlay (recBits W (matV R C (upd a D r vv)) ++ [false]) (σ3.st sMAT))).seth sMAT 0).setv
    rCM 0 with hσ5
  -- 5. `DD := PW`
  refine Runs.seq ((opCopy cap h5 (X := wDD) (Y := wPW) (by decide) (by decide) (by decide) cap2).cost
    (show 41 * (W + 1) + 3 ≤ ucost W (R * C) by have := lin_le_ucost W (R * C); omega)) (fun τ6 h6 => ?_)
  -- 6. clears
  have h5IJ : σ5.val rIJ = R * C := by
    rw [show σ5.val rIJ = σ4.val rIJ by simp (config := {decide := true}) [hσ5], hfr4.val (by decide)]
    simp (config := {decide := true}) [hσ3, hIJ2]
  refine Runs.seq ((opClearR cap h6 (r := rIJ) (by decide) (by rw [h5IJ]; omega)).cost
    (show 3 * σ5.val rIJ + 1 ≤ ucost W (R * C) by rw [h5IJ]; omega)) (fun τ7 h7 => ?_)
  have h5FD : σ5.val rFD = 1 := by
    rw [show σ5.val rFD = σ4.val rFD by simp (config := {decide := true}) [hσ5], hfr4.val (by decide)]
    simp (config := {decide := true}) [hσ3]; rw [hfr2.val (by decide), hFD]
  refine Runs.seq (opDecR cap h7 (r := rFD) (by decide) (by simp (config := {decide := true}) [h5FD]; omega))
    (fun τ8 h8 => ?_)
  have h5RB : σ5.val rRB = r * C := by
    rw [show σ5.val rRB = σ4.val rRB by simp (config := {decide := true}) [hσ5], hfr4.val (by decide)]
    simp (config := {decide := true}) [hσ3]; rw [hfr2.val (by decide), hc.RB]
  have hrC : r * C ≤ R * C := Nat.mul_le_mul_right _ hc.hr.le
  refine ((opClearR cap h8 (r := rRB) (by decide) (by simp (config := {decide := true}) [h5RB]; omega)).cost
    (show 3 * ((σ5.setv rIJ 0).setv rFD ((σ5.setv rIJ 0).val rFD - 1)).val rRB + 1 ≤ ucost W (R * C) by
      simp (config := {decide := true}) [h5RB]; omega)).post (fun τ9 h9 => ?_)
  refine ⟨_, _, (σ3.st sMAT).drop ((recBits W (matV R C (upd a D r vv)) ++ [false]).length), h9, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, by simp [hP2, hP]⟩
  · simp (config := {decide := true}) [hσ5, overlay, recStream_eq]
  · simp (config := {decide := true}) [hσ5]
  · simp (config := {decide := true}) [hσ5]
    rw [hfr4.sh (by decide)]; simp [hσ3]
  · simp (config := {decide := true}) [hσ5]; exact hwh4
  · simp (config := {decide := true}) [hσ5]; exact hwl4
  · intro q hq
    simp only [updRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp (config := {decide := true})
    · simp (config := {decide := true}) [hσ5]; rw [hfr4.val (by decide)]; simp (config := {decide := true}) [hσ3, hIV2]
    · simp (config := {decide := true}) [hσ5]; rw [hfr4.val (by decide)]; simp (config := {decide := true}) [hσ3, hRJ2]
    · simp (config := {decide := true}) [hσ5]; rw [hfr4.val (by decide)]; simp (config := {decide := true}) [hσ3, hLJ2]
    · simp (config := {decide := true}) [hσ5]; rw [hfr4.val (by decide)]; simp (config := {decide := true}) [hσ3, hLI2]
    · simp (config := {decide := true}) [hσ5]; rw [hfr4.val (by decide)]; simp (config := {decide := true}) [hσ3]
    · simp (config := {decide := true}) [hσ5]
    · simp (config := {decide := true}) [h5FD]
    · simp (config := {decide := true})
  · refine SameExcept.trans (hfr13.weaken (by simp) (by simp [updRegs])) ?_
    refine SameExcept.trans (hfr4.weaken (by simp) (by simp [updRegs])) ?_
    refine SameExcept.trans (sameExcept_sets σ4 (by simp) _) (SameExcept.trans (sameExcept_seth _ (by simp) _)
      (SameExcept.trans (sameExcept_setv _ (by simp [updRegs]) _) (SameExcept.trans (sameExcept_setv _ (by simp [updRegs]) _)
        (SameExcept.trans (sameExcept_setv _ (by simp [updRegs]) _) (sameExcept_setv _ (by simp [updRegs]) _)))))

end NearCubicGates.Close.Solve
