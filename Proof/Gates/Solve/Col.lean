import Proof.Gates.Solve.Pass

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

/-- The data of a search, stated on a reference state. -/
structure SCtx (σ0 : MS) (W R C : ℕ) (a : ℕ → ℕ → ℤ) (vv Bd : ℕ) (junk : List Bool) : Prop where
  mat : σ0.st sMAT = recStream ((matV R C a).map (binary (W + 1))) ++ junk
  math : σ0.sh sMAT = 0
  hv : vv < C
  V : σ0.val rV = vv
  CC : σ0.val rCC = C
  bd : ∀ i j, i < R → j < C → (a i j).natAbs ≤ Bd
  hW : 2 * Bd * Bd + 1 < 2 ^ W

theorem SCtx.same {σ0 σ1 : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {vv Bd : ℕ} {junk : List Bool}
    (h : SCtx σ0 W R C a vv Bd junk) {S : List Str} {Rg : List Reg} (hfr : SameExcept σ0 σ1 S Rg)
    (hS : sMAT ∉ S) (hRg : rV ∉ Rg ∧ rCC ∉ Rg) : SCtx σ1 W R C a vv Bd junk :=
  ⟨by rw [hfr.st hS, h.mat], by rw [hfr.sh hS, h.math], h.hv, by rw [hfr.val hRg.1, h.V],
    by rw [hfr.val hRg.2, h.CC], h.bd, h.hW⟩

/-- The first nonzero row among the first `k`. -/
def firstNZ (a : ℕ → ℕ → ℤ) (vv k : ℕ) : Option ℕ := (List.range k).find? fun i => a i vv != 0

theorem firstNZ_succ (a : ℕ → ℕ → ℤ) (vv k : ℕ) : firstNZ a vv (k + 1) =
    match firstNZ a vv k with
    | some r => some r
    | none => if a k vv ≠ 0 then some k else none := by
  unfold firstNZ
  rw [List.range_succ, List.find?_append]
  rcases h : (List.find? (fun i => a i vv != 0) (List.range k)) with _ | r
  · by_cases hk : a k vv = 0 <;> simp [hk]
  · simp

theorem firstNZ_lt {a : ℕ → ℕ → ℤ} {vv k r : ℕ} (h : firstNZ a vv k = some r) : r < k :=
  List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- The flag state for a search result. -/
def FState (σ1 : MS) (v1 : Str → ℕ) (a : ℕ → ℕ → ℤ) (vv C : ℕ) : Option ℕ → Prop
  | none => σ1.val rFD = 0 ∧ σ1.val rRB = 0
  | some r => σ1.val rFD = 1 ∧ σ1.val rRB = r * C ∧ v1 wPW = encS (a r vv)

/-- The search body: test row `k`, keep the first hit, step the indices. -/
def searchBody : WMX NS NR :=
  .seq (getAt sMAT wK rCA rCW rSIX rK2) (.seq (nzP wK wZ rNZ rF rR)
    (.seq (.ifr rNZ (.seq (WMX.dec rNZ) (.ifr rFD WMX.skip (.seq (WMX.inc rFD)
      (.seq (addR rSB rRB rTa) (BinW.copy wPW wK rF rR))))) WMX.skip)
    (.seq (addR rCC rSIX rTa) (addR rCC rSB rTa))))

/-- The search invariant after `k` rows. -/
def SInv (σA : MS) (W C : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (vv : ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rSIX = k * C + vv ∧ σ1.val rSB = k * C ∧ σ1.val rNZ = 0 ∧
    FState σ1 v1 a vv C (firstNZ a vv k) ∧ SameExcept σA σ1 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] ∧ v1 wDD = encS D

theorem search_step (cap : ℕ) {σA : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ} {vv Bd : ℕ} {junk : List Bool}
    (hcA : SCtx σA W R C a vv Bd junk) (hcap : capE (R * C) W ≤ cap) {m : ℕ} (hm : m ≤ R) (k : ℕ)
    (hk : k < m) (τ : MS) (hI : SInv σA W C a D vv k τ) :
    Runs cap searchBody (τ.setv rSL (m - k - 1)) (7 * ucost W (R * C))
      (fun ρ => SInv σA W C a D vv (k + 1) ρ ∧ ρ.val rSL = m - k - 1) := by
  obtain ⟨σ1, v1, h1, hSIX, hSB, hNZ, hF, hfr1, hD1⟩ := hI
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  obtain ⟨N, hN⟩ : ∃ N, N = R * C := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = ucost W N := ⟨_, rfl⟩
  rw [← hN] at cap1 ⊢
  rw [← hUd]
  have hU : 16 ≤ U := hUd ▸ one_le_ucost W N
  have hUN : 4000 * (N + 2) ≤ U := hUd ▸ ucost_geN W N
  have hUL : 500 * W + 700 ≤ U := hUd ▸ lin_le_ucost W N
  have hkR : k < R := lt_of_lt_of_le hk hm
  have hkC : k * C + C ≤ N := by
    rw [hN]; have := Nat.mul_le_mul_right C (show k + 1 ≤ R from hkR); rw [Nat.add_mul, one_mul] at this; exact this
  have hvC := hcA.hv
  have h1' := h1.setv (r := rSL) (by decide) (m - k - 1)
  set σ2 := σ1.setv rSL (m - k - 1) with hσ2
  have hfr2 : SameExcept σA σ2 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : SCtx σ2 W R C a vv Bd junk := hcA.same hfr2 (by simp) (by decide)
  have h2SIX : σ2.val rSIX = k * C + vv := by simp (config := {decide := true}) [hσ2, hSIX]
  -- 1. `wK := a k vv`
  have hidx : σ2.val rSIX < (matV R C a).length := by rw [h2SIX, matV_length]; exact idx_lt hkR hvC
  have hgl := getAt_le W N (σ2.val rSIX) (by rw [h2SIX]; omega)
  rw [← hUd] at hgl
  refine Runs.seq' ((opGetAt cap h1' (A := sMAT) (IX := rSIX) (by decide) (by decide) (matV R C a) junk hc2.mat
    hc2.math hidx (by rw [matV_length, ← hN, h2SIX]; omega)).cost hgl)
    (fun τ3 h3 => ?_) (c2 := 6 * U - 1) (by omega)
  have hxk : (matV R C a)[σ2.val rSIX] = encS (a k vv) := by simp only [h2SIX]; exact matV_get R C a hkR hvC
  rw [hxk] at h3
  set v3 := Function.update v1 wK (encS (a k vv)) with hv3
  -- 2. `NZ := [a k vv ≠ 0]`
  have hlt : v3 wK < 2 ^ (W + 1) := by
    simp only [hv3, Function.update_self]
    exact encS_lt (hcA.bd k vv hkR hvC |>.trans_lt (by have := hcA.hW; have := le_sq2 Bd; omega))
  refine Runs.seq' ((opNz cap h3 (X := wK) (NZ := rNZ) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ2, hNZ]) hlt cap2).cost (show 41 * (W + 1) + 12 ≤ U by omega))
    (fun τ4 h4 => ?_) (c2 := 5 * U - 2) (by omega)
  have hnz : (decide (v3 wK ≠ 0)).toNat = (decide (a k vv ≠ 0)).toNat := by
    simp only [hv3, Function.update_self]
    congr 2
    apply propext; constructor
    · intro h e; apply h; rw [e]; rfl
    · intro h e; apply h; exact encS_inj (by rw [e]; rfl)
  rw [hnz] at h4
  set σ4 := σ2.setv rNZ (decide (a k vv ≠ 0)).toNat with hσ4
  -- 3. the branch
  have hbr : Runs cap (.ifr rNZ (.seq (WMX.dec rNZ) (.ifr rFD WMX.skip (.seq (WMX.inc rFD)
      (.seq (addR rSB rRB rTa) (BinW.copy wPW wK rF rR))))) WMX.skip) τ4 (2 * U)
      (fun ρ => ∃ σ5 v5, At σ5 ρ W v5 ∧ σ5.val rSIX = k * C + vv ∧ σ5.val rSB = k * C ∧ σ5.val rNZ = 0 ∧
        FState σ5 v5 a vv C (firstNZ a vv (k + 1)) ∧ SameExcept σA σ5 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] ∧
        v5 wDD = encS D ∧ σ5.val rSL = m - k - 1 ∧ σ5.val rCC = C) := by
    have h4NZ : τ4.val rNZ = (decide (a k vv ≠ 0)).toNat := by rw [h4.val (by decide)]; simp [hσ4]
    have hfr4 : SameExcept σA σ4 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] :=
      SameExcept.trans hfr2 (sameExcept_setv σ2 (by simp) _)
    have h4CC : σ4.val rCC = C := by rw [hfr4.val (by decide), hcA.CC]
    by_cases hak : a k vv = 0
    · -- no hit: skip
      have hv : τ4.val rNZ = 0 := by rw [h4NZ]; simp [hak]
      refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ4) ⟨σ4, v3, h4, ?_⟩)).cost (by omega)
      refine ⟨by simp (config := {decide := true}) [hσ4, hσ2, hSIX], by simp (config := {decide := true}) [hσ4, hσ2, hSB],
        by simp [hσ4, hak], ?_, hfr4, by simp (config := {decide := true}) [hv3, hD1],
        by simp (config := {decide := true}) [hσ4, hσ2], h4CC⟩
      rw [firstNZ_succ]
      rcases hfk : firstNZ a vv k with _ | r
      · simp only [hak, ne_eq, not_true_eq_false, if_false]
        rw [hfk] at hF
        exact ⟨by simp (config := {decide := true}) [hσ4, hσ2, hF.1], by simp (config := {decide := true}) [hσ4, hσ2, hF.2]⟩
      · rw [hfk] at hF
        exact ⟨by simp (config := {decide := true}) [hσ4, hσ2, hF.1],
          by simp (config := {decide := true}) [hσ4, hσ2, hF.2.1], by simp (config := {decide := true}) [hv3, hF.2.2]⟩
    · have hv : τ4.val rNZ ≠ 0 := by rw [h4NZ]; simp [hak]
      refine (Runs.ifrT hv ?_).cost (show 2 * U - 1 + 1 ≤ 2 * U by omega)
      · -- dec NZ
        refine Runs.seq' (opDecR cap h4 (r := rNZ) (by decide) (by simp [hσ4, hak]; omega)) (fun τ5 h5 => ?_)
          (c2 := 2 * U - 4) (by omega)
        set σ5 := σ4.setv rNZ (σ4.val rNZ - 1) with hσ5
        have h5NZ : σ5.val rNZ = 0 := by simp [hσ5, hσ4, hak]
        have hfr5 : SameExcept σA σ5 [] [rSIX, rSB, rNZ, rFD, rRB, rSL] :=
          SameExcept.trans hfr4 (sameExcept_setv σ4 (by simp) _)
        rcases hfk : firstNZ a vv k with _ | r
        · -- first hit
          rw [hfk] at hF
          have hFD : τ5.val rFD = 0 := by rw [h5.val (by decide)]; simp (config := {decide := true}) [hσ5, hσ4, hσ2, hF.1]
          refine (Runs.ifrF hFD ?_).cost (show 2 * U - 4 - 1 + 1 ≤ 2 * U - 4 by omega)
          refine Runs.seq' (opIncR cap h5 (r := rFD) (by decide) (by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hF.1]; omega))
            (fun τ6 h6 => ?_) (c2 := 2 * U - 10) (by omega)
          set σ6 := σ5.setv rFD (σ5.val rFD + 1) with hσ6
          refine Runs.seq' ((opAddR cap h6 (A := rSB) (B := rRB) (by decide) (by decide) (by decide)
            (by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hF.2, hSB]; omega)).cost
            (show 18 * σ6.val rSB + 3 ≤ U by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hSB]; omega))
            (fun τ7 h7 => ?_) (c2 := U - 20) (by omega)
          refine ((opCopy cap h7 (X := wPW) (Y := wK) (by decide) (by decide) (by decide) cap2).cost
            (show 41 * (W + 1) + 3 ≤ U - 20 by omega)).post (fun τ8 h8 => ?_)
          refine ⟨_, _, h8, by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hSIX],
            by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hSB], by simp (config := {decide := true}) [hσ6, h5NZ], ?_,
            ?_, by simp (config := {decide := true}) [hv3, hD1], by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2],
            by simp (config := {decide := true}) [hσ6, hσ5, h4CC]⟩
          · rw [firstNZ_succ, hfk]
            simp only [hak, ne_eq, not_false_eq_true, if_true]
            refine ⟨by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hF.1], ?_, by simp [hv3]⟩
            simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ2, hF.2, hSB]
          · refine SameExcept.trans hfr5 (SameExcept.trans (sameExcept_setv σ5 (by simp) _) (sameExcept_setv _ (by simp) _))
        · -- already found
          rw [hfk] at hF
          have hFD : τ5.val rFD ≠ 0 := by rw [h5.val (by decide)]; simp (config := {decide := true}) [hσ5, hσ4, hσ2, hF.1]
          refine (Runs.ifrT hFD (Runs.of (WXExec.skip cap τ5) ?_)).cost (by omega)
          refine ⟨σ5, v3, h5, by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hSIX],
            by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hSB], h5NZ, ?_, hfr5,
            by simp (config := {decide := true}) [hv3, hD1], by simp (config := {decide := true}) [hσ5, hσ4, hσ2],
            by simp (config := {decide := true}) [hσ5, h4CC]⟩
          rw [firstNZ_succ, hfk]
          exact ⟨by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hF.1],
            by simp (config := {decide := true}) [hσ5, hσ4, hσ2, hF.2.1], by simp (config := {decide := true}) [hv3, hF.2.2]⟩
  refine Runs.seq' hbr (fun τ5 ⟨σ5, v5, h5, h5SIX, h5SB, h5NZ, h5F, hfr5, h5D, h5SL, h5CC⟩ => ?_) (c2 := 3 * U - 3)
    (by omega)
  -- 4. `SIX += C`, `SB += C`
  refine Runs.seq' ((opAddR cap h5 (A := rCC) (B := rSIX) (by decide) (by decide) (by decide)
    (by rw [h5SIX, h5CC]; omega)).cost (show 18 * σ5.val rCC + 3 ≤ U by rw [h5CC]; omega))
    (fun τ6 h6 => ?_) (c2 := U) (by omega)
  refine ((opAddR cap h6 (A := rCC) (B := rSB) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [h5SB, h5CC]; omega)).cost
    (show 18 * (σ5.setv rSIX (σ5.val rSIX + σ5.val rCC)).val rCC + 3 ≤ U by
      simp (config := {decide := true}) [h5CC]; omega)).post (fun τ7 h7 => ⟨⟨_, v5, h7, ?_, ?_, ?_, ?_, ?_, h5D⟩, ?_⟩)
  · simp (config := {decide := true}) [h5SIX, h5CC]; ring
  · simp (config := {decide := true}) [h5SB, h5CC]; ring
  · simp (config := {decide := true}) [h5NZ]
  · rcases hf : firstNZ a vv (k + 1) with _ | r <;> rw [hf] at h5F
    · exact ⟨by simp (config := {decide := true}) [h5F.1], by simp (config := {decide := true}) [h5F.2]⟩
    · exact ⟨by simp (config := {decide := true}) [h5F.1], by simp (config := {decide := true}) [h5F.2.1], h5F.2.2⟩
  · exact SameExcept.trans hfr5 (SameExcept.trans (sameExcept_setv σ5 (by simp) _) (sameExcept_setv _ (by simp) _))
  · rw [h7.val (by decide)]; simp (config := {decide := true}) [h5SL]

end NearCubicGates.Close.Solve
