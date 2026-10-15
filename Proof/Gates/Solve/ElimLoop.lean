import Proof.Gates.Solve.Elim

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

def ColPost (σ0 σ1 : MS) (W R C : ℕ) (b : ℕ → ℕ → ℤ) : Prop :=
  (∃ junk', σ1.st sMAT = recStream ((matV R C b).map (binary (W + 1))) ++ junk') ∧ σ1.sh sMAT = 0 ∧
    σ1.sh sNEW = 0 ∧ σ1.sh sWR = 0 ∧ (σ1.st sWR).length ≤ 2 * (W + 1) + 1 ∧ (∀ q ∈ colRegs, σ1.val q = 0) ∧
    SameExcept σ0 σ1 [sMAT, sNEW, sWR] colRegs

theorem col_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C m : ℕ} {a : ℕ → ℕ → ℤ}
    {D : ℤ} {vv Bd : ℕ} {junk : List Bool} (hc : ColCtx σ0 W R C m a D vv Bd junk) (hD : v wDD = encS D)
    (hcap : capE (R * C) W ≤ cap) :
    Runs cap colP σ (colCost R C (ucost W (R * C))) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      ColPost σ0 σ1 W R C (step m ⟨a, D⟩ vv).a ∧ v1 wDD = encS (step m ⟨a, D⟩ vv).D) := by
  have hU := one_le_ucost W (R * C)
  have hz := hc.z
  simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨hSIX, hSB, hNZ, hFD, hRB, hSL, hIJ, hIV, hRJ, hLJ, hLI, hCN, hCM⟩ := hz
  have hsc : SCtx σ0 W R C a vv Bd junk := ⟨hc.mat, hc.math, hc.hv, hc.V, hc.CC, hc.bd, hc.hW⟩
  refine Runs.cost ?_ (updCost_le R C (ucost W (R * C)) hU m hc.hm)
  refine Runs.seq (search_spec cap h hsc hcap hc.hR1 hc.hm hc.MM hSIX hSB hNZ hFD hRB hSL hD)
    (fun τ1 ⟨σ1, v1, h1, hF1, h1SIX, h1SB, h1NZ, h1SL, hfr1, hD1⟩ => ?_)
  have e1 : ∀ q, q ∉ [rSIX, rSB, rNZ, rFD, rRB, rSL] → σ1.val q = σ0.val q := fun q hq => hfr1.val hq
  rcases hp : piv m a vv with _ | r
  · -- no pivot
    rw [hp] at hF1
    have hv : τ1.val rFD = 0 := by rw [h1.val (by decide)]; exact hF1.1
    refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ1) ⟨σ1, v1, h1, ?_, ?_⟩)).cost (by omega)
    · have hst : step m ⟨a, D⟩ vv = ⟨a, D⟩ := by unfold step; rw [hp]
      rw [hst]
      refine ⟨⟨junk, by rw [hfr1.st (by decide), hc.mat]⟩, by rw [hfr1.sh (by decide), hc.math],
        by rw [hfr1.sh (by decide), hc.newh], by rw [hfr1.sh (by decide), hc.wrh],
        by rw [hfr1.st (by decide)]; exact hc.wrl, ?_, hfr1.weaken (by simp) (by simp [colRegs])⟩
      intro q hq
      simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1SIX
      · exact h1SB
      · exact h1NZ
      · exact hF1.1
      · exact hF1.2
      · exact h1SL
      · rw [e1 _ (by decide)]; exact hIJ
      · rw [e1 _ (by decide)]; exact hIV
      · rw [e1 _ (by decide)]; exact hRJ
      · rw [e1 _ (by decide)]; exact hLJ
      · rw [e1 _ (by decide)]; exact hLI
      · rw [e1 _ (by decide)]; exact hCN
      · rw [e1 _ (by decide)]; exact hCM
    · have hst : step m ⟨a, D⟩ vv = ⟨a, D⟩ := by unfold step; rw [hp]
      rw [hst]; exact hD1
  · -- the pivot `r`
    rw [hp] at hF1
    obtain ⟨hrm, hr0⟩ := piv_some m hp
    have hv : τ1.val rFD ≠ 0 := by rw [h1.val (by decide), hF1.1]; omega
    have hpc : PassCtx σ1 W R C a D r vv Bd junk :=
      ⟨by rw [hfr1.st (by decide), hc.mat], by rw [hfr1.sh (by decide), hc.math], lt_of_lt_of_le hrm hc.hm, hc.hv,
        hF1.2.1, by rw [e1 _ (by decide), hc.V], by rw [e1 _ (by decide), hc.CC], hc.bd, hc.bD, hc.hW, hc.D0⟩
    have hu := upd_spec cap h1 hpc (by rw [e1 _ (by decide), hc.RR])
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [e1 _ (by decide)]; exact hIJ
        · rw [e1 _ (by decide)]; exact hIV
        · rw [e1 _ (by decide)]; exact hRJ
        · rw [e1 _ (by decide)]; exact hLJ
        · rw [e1 _ (by decide)]; exact hLI
        · rw [e1 _ (by decide)]; exact hCN
        · rw [e1 _ (by decide)]; exact hCM)
      hF1.1 hF1.2.2 hD1 (by rw [hfr1.sh (by decide), hc.newh]) (by rw [hfr1.sh (by decide), hc.wrh])
      (by rw [hfr1.st (by decide)]; exact hc.wrl) hcap
    refine Runs.ifrT hv (hu.post (fun τ2 ⟨σ2, v2, junk', h2, h2mat, h2math, h2newh, h2wrh, h2wrl, h2z, hfr2, hD2⟩ =>
      ⟨σ2, v2, h2, ?_, ?_⟩))
    · have hst : step m ⟨a, D⟩ vv = ⟨upd a D r vv, a r vv⟩ := by unfold step; rw [hp]
      rw [hst]
      refine ⟨⟨junk', h2mat⟩, h2math, h2newh, h2wrh, h2wrl, ?_, ?_⟩
      · intro q hq
        by_cases hu : q ∈ updRegs
        · exact h2z q hu
        · rw [hfr2.val hu]
          simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
          simp only [updRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first | exact h1SIX | exact h1SB | exact h1NZ | exact h1SL | (simp at hu)
      · exact SameExcept.trans (hfr1.weaken (by simp) (by simp [colRegs]))
          (hfr2.weaken (by simp) (by simp [updRegs, colRegs]))
    · have hst : step m ⟨a, D⟩ vv = ⟨upd a D r vv, a r vv⟩ := by unfold step; rw [hp]
      rw [hst]; exact hD2

/-! ## The elimination loop -/

/-- All `n` columns. -/
def elimP : WMX NS NR :=
  .seq (addR rNN rLV rTa) (.seq (.whr rLV (.seq (WMX.dec rLV) (.seq colP (WMX.inc rV)))) (.wm (WM.clear rV)))

/-- The registers of the elimination loop. -/
def elimRegs : List Reg := rV :: rLV :: colRegs

/-- The parameters of the elimination (registers outside `elimRegs`, bounds). -/
structure ElimPar (σ0 : MS) (W R C m n : ℕ) (M : ℕ → ℕ → ℤ) (Bd : ℕ) : Prop where
  hm : m ≤ R
  hn : n < C
  hnR : n ≤ R
  RR : σ0.val rRR = R
  CC : σ0.val rCC = C
  MM : σ0.val rMM = m
  bd : ∀ k ≤ n, ∀ i j, i < R → j < C → ((run m ⟨M, 1⟩ k).a i j).natAbs ≤ Bd
  bD : ∀ k ≤ n, ((run m ⟨M, 1⟩ k).D).natAbs ≤ Bd
  D0 : ∀ k ≤ n, (run m ⟨M, 1⟩ k).D ≠ 0
  hW : 2 * Bd * Bd + 1 < 2 ^ W

/-- The data of the elimination (on the reference state). -/
structure ElimCtx (σ0 : MS) (W R C m n : ℕ) (M : ℕ → ℕ → ℤ) (Bd : ℕ) (junk : List Bool) : Prop where
  par : ElimPar σ0 W R C m n M Bd
  mat : σ0.st sMAT = recStream ((matV R C M).map (binary (W + 1))) ++ junk
  math : σ0.sh sMAT = 0
  newh : σ0.sh sNEW = 0
  wrh : σ0.sh sWR = 0
  wrl : (σ0.st sWR).length ≤ 2 * (W + 1) + 1
  NN : σ0.val rNN = n
  z : ∀ r ∈ elimRegs, σ0.val r = 0

/-- The cost bound of the elimination. -/
def elimCost (R C n U : ℕ) : ℕ := (n + 2) * (colCost R C U + 10)

/-- The column-loop invariant after `k` columns. -/
def EInv (σA : MS) (W R C m : ℕ) (M : ℕ → ℕ → ℤ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ (∃ junk', σ1.st sMAT = recStream ((matV R C (run m ⟨M, 1⟩ k).a).map (binary (W + 1))) ++
    junk') ∧ σ1.sh sMAT = 0 ∧ σ1.sh sNEW = 0 ∧ σ1.sh sWR = 0 ∧ (σ1.st sWR).length ≤ 2 * (W + 1) + 1 ∧
    (∀ q ∈ colRegs, σ1.val q = 0) ∧ σ1.val rV = k ∧ SameExcept σA σ1 [sMAT, sNEW, sWR] elimRegs ∧
    v1 wDD = encS (run m ⟨M, 1⟩ k).D

theorem colRegs_ne {q : Reg} (hq : q ∈ colRegs) : q ≠ rV ∧ q ≠ rLV := by
  simp only [colRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem elim_step (cap : ℕ) {σA : MS} {W R C m n : ℕ} {M : ℕ → ℕ → ℤ} {Bd : ℕ}
    (hc : ElimPar σA W R C m n M Bd) (hcap : capE (R * C) W ≤ cap) (k : ℕ) (hk : k < n) (τ : MS)
    (hI : EInv σA W R C m M k τ) :
    Runs cap (.seq colP (WMX.inc rV)) (τ.setv rLV (n - k - 1)) (colCost R C (ucost W (R * C)) + 1 + 3)
      (fun ρ => EInv σA W R C m M (k + 1) ρ ∧ ρ.val rLV = n - k - 1) := by
  obtain ⟨σ1, v1, h1, ⟨junk1, hmat1⟩, hmath1, hnewh1, hwrh1, hwrl1, hz1, hV1, hfr1, hD1⟩ := hI
  have h1' := h1.setv (r := rLV) (by decide) (n - k - 1)
  set σ2 := σ1.setv rLV (n - k - 1) with hσ2
  have hfr2 : SameExcept σA σ2 [sMAT, sNEW, sWR] elimRegs :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by decide) _)
  have hcc : ColCtx σ2 W R C m (run m ⟨M, 1⟩ k).a (run m ⟨M, 1⟩ k).D k Bd junk1 :=
    ⟨by simp [hσ2, hmat1], by simp [hσ2, hmath1], by simp [hσ2, hnewh1], by simp [hσ2, hwrh1],
      by simp [hσ2, hwrl1], by have := hc.hnR; omega, hc.hm, by have := hc.hn; omega,
      by rw [hfr2.val (by decide), hc.RR], by rw [hfr2.val (by decide), hc.CC], by rw [hfr2.val (by decide), hc.MM],
      by simp (config := {decide := true}) [hσ2, hV1],
      fun q hq => by
        have := (colRegs_ne hq).2
        simp [hσ2, Function.update_of_ne this, hz1 q hq],
      hc.bd k hk.le, hc.bD k hk.le, hc.hW, hc.D0 k hk.le⟩
  refine Runs.seq (col_spec cap h1' hcc hD1 hcap) (fun τ3 ⟨σ3, v3, h3, ⟨⟨junk3, hmat3⟩, hmath3, hnewh3, hwrh3, hwrl3,
    hz3, hfr3⟩, hD3⟩ => ?_)
  have hV3 : σ3.val rV = k := by rw [hfr3.val (by decide)]; simp (config := {decide := true}) [hσ2, hV1]
  have hRC : R ≤ R * C := Nat.le_mul_of_pos_right _ (by have := hc.hn; omega)
  have hk1 : k + 1 < cap := by
    have h1 := hc.hnR
    have h2 : 2 * (R * C) + 10 ≤ cap := by unfold capE at hcap; omega
    omega
  refine (opIncR cap h3 (r := rV) (by decide) (by rw [hV3]; omega)).post
    (fun τ4 h4 => ⟨⟨_, v3, h4, ⟨junk3, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hD3⟩, ?_⟩)
  · simp only [WState.setv_st]; exact hmat3
  · simpa using hmath3
  · simpa using hnewh3
  · simpa using hwrh3
  · simpa using hwrl3
  · intro q hq
    have := (colRegs_ne hq).1
    simp [Function.update_of_ne this, hz3 q hq]
  · simp [hV3]
  · exact SameExcept.trans hfr2 (SameExcept.trans (hfr3.weaken (by simp)
      (fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
      (sameExcept_setv σ3 (by simp [elimRegs]) _))
  · rw [h4.val (by decide)]; simp (config := {decide := true}); rw [hfr3.val (by decide)]; simp [hσ2]

theorem elim_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C m n : ℕ} {M : ℕ → ℕ → ℤ}
    {Bd : ℕ} {junk : List Bool} (hc : ElimCtx σ0 W R C m n M Bd junk) (hD : v wDD = encS 1)
    (hcap : capE (R * C) W ≤ cap) :
    Runs cap elimP σ (elimCost R C n (ucost W (R * C))) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      (∃ junk', σ1.st sMAT = recStream ((matV R C (run m ⟨M, 1⟩ n).a).map (binary (W + 1))) ++ junk') ∧
      σ1.sh sMAT = 0 ∧ σ1.sh sNEW = 0 ∧ σ1.sh sWR = 0 ∧ (σ1.st sWR).length ≤ 2 * (W + 1) + 1 ∧
      (∀ q ∈ elimRegs, σ1.val q = 0) ∧ SameExcept σ0 σ1 [sMAT, sNEW, sWR] elimRegs ∧
      v1 wDD = encS (run m ⟨M, 1⟩ n).D) := by
  have hU := one_le_ucost W (R * C)
  have hUN := ucost_geN W (R * C)
  have hRC : R ≤ R * C := Nat.le_mul_of_pos_right _ (by have := hc.par.hn; omega)
  have hnR := hc.par.hnR
  have hz := hc.z
  have hV0 : σ0.val rV = 0 := hz rV (by decide)
  have hLV0 : σ0.val rLV = 0 := hz rLV (by decide)
  have hcolC : ucost W (R * C) ≤ colCost R C (ucost W (R * C)) := by
    unfold colCost; nlinarith
  have hcapN : n ≤ cap := by unfold capE at hcap; omega
  refine Runs.seq' ((opAddR cap h (A := rNN) (B := rLV) (by decide) (by decide) (by decide)
    (by rw [hLV0, hc.NN]; omega)).cost (show 18 * σ0.val rNN + 3 ≤ ucost W (R * C) by rw [hc.NN]; omega))
    (fun τ1 h1 => ?_)
    (c2 := n * (colCost R C (ucost W (R * C)) + 1 + 3 + 4) + 1 + 1 + ucost W (R * C))
    (by unfold elimCost; nlinarith)
  set σ1 := σ0.setv rLV (σ0.val rLV + σ0.val rNN) with hσ1
  have hfr01 : SameExcept σ0 σ1 [sMAT, sNEW, sWR] elimRegs := sameExcept_setv σ0 (by decide) _
  have hpar : ElimPar σ1 W R C m n M Bd :=
    ⟨hc.par.hm, hc.par.hn, hc.par.hnR, by rw [hfr01.val (by decide), hc.par.RR],
      by rw [hfr01.val (by decide), hc.par.CC], by rw [hfr01.val (by decide), hc.par.MM], hc.par.bd, hc.par.bD,
      hc.par.D0, hc.par.hW⟩
  have hI0 : EInv σ1 W R C m M 0 τ1 := by
    refine ⟨σ1, v, h1, ⟨junk, by simp [hσ1, hc.mat]; rfl⟩, by simp [hσ1, hc.math], by simp [hσ1, hc.newh],
      by simp [hσ1, hc.wrh], by simp [hσ1, hc.wrl], fun q hq => ?_, by simp (config := {decide := true}) [hσ1, hV0],
      SameExcept.refl _ _ _, by rw [hD]; rfl⟩
    have := (colRegs_ne hq).2
    simp [hσ1, Function.update_of_ne this, hz q (by simp [elimRegs, hq])]
  have hloop := Runs.count (cap := cap) (K := rLV) (body := .seq colP (WMX.inc rV))
    (colCost R C (ucost W (R * C)) + 1 + 3) n (EInv σ1 W R C m M) hcapN
    (fun k hk τ hτ _ => elim_step cap hpar hcap k hk τ hτ) τ1 hI0
    (by rw [h1.val (by decide)]; simp (config := {decide := true}) [hσ1, hLV0, hc.NN])
  refine Runs.seq' hloop (fun τ2 ⟨⟨σ2, v2, h2, hmat2, hmath2, hnewh2, hwrh2, hwrl2, hz2, hV2, hfr2, hD2⟩, hK⟩ => ?_)
    (c2 := ucost W (R * C)) (by omega)
  refine ((opClearR cap h2 (r := rV) (by decide) (by rw [hV2]; exact hcapN)).cost
    (show 3 * σ2.val rV + 1 ≤ ucost W (R * C) by rw [hV2]; omega)).post
    (fun τ3 h3 => ⟨_, v2, h3, by simpa using hmat2, by simpa using hmath2, by simpa using hnewh2,
      by simpa using hwrh2, by simpa using hwrl2, ?_, ?_, hD2⟩)
  · intro q hq
    simp only [elimRegs, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · simp
    · simp (config := {decide := true}); rw [← h2.val (by decide)]; exact hK
    · have := (colRegs_ne hq).1
      simp [Function.update_of_ne this, hz2 q hq]
  · exact SameExcept.trans hfr01 (SameExcept.trans hfr2 (sameExcept_setv σ2 (by decide) _))

end NearCubicGates.Close.Solve
