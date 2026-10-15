import Proof.Gates.Solve.Entry
import Proof.Gates.Solve.Value

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

/-- The matrix entries as signed words, row-major. -/
def matV (R C : ℕ) (a : ℕ → ℕ → ℤ) : List ℕ := flat R C fun i j => encS (a i j)

theorem matV_length (R C : ℕ) (a : ℕ → ℕ → ℤ) : (matV R C a).length = R * C := flat_length _ _ _

theorem matV_get (R C : ℕ) (a : ℕ → ℕ → ℤ) {i j : ℕ} (hi : i < R) (hj : j < C) :
    (matV R C a)[i * C + j]'(by rw [matV_length]; exact idx_lt hi hj) = encS (a i j) := flat_get _ _ _ hi hj

/-- The cap needed by the pass on `N` records of width `W + 1`. -/
def capE (N W : ℕ) : ℕ := 4 * (N + 2) * (2 * (W + 1) + 1) + 2 * N + 10

/-- The data of one pass, stated on a reference state. -/
structure PassCtx (σ0 : MS) (W R C : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (r vv Bd : ℕ) (junk : List Bool) : Prop where
  mat : σ0.st sMAT = recStream ((matV R C a).map (binary (W + 1))) ++ junk
  math : σ0.sh sMAT = 0
  hr : r < R
  hv : vv < C
  RB : σ0.val rRB = r * C
  V : σ0.val rV = vv
  CC : σ0.val rCC = C
  bd : ∀ i j, i < R → j < C → (a i j).natAbs ≤ Bd
  bD : D.natAbs ≤ Bd
  hW : 2 * Bd * Bd + 1 < 2 ^ W
  D0 : D ≠ 0

theorem PassCtx.same {σ0 σ1 : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ} {r vv Bd : ℕ} {junk : List Bool}
    (h : PassCtx σ0 W R C a D r vv Bd junk) {S : List Str} {Rg : List Reg} (hfr : SameExcept σ0 σ1 S Rg)
    (hS : sMAT ∉ S) (hRg : rRB ∉ Rg ∧ rV ∉ Rg ∧ rCC ∉ Rg) : PassCtx σ1 W R C a D r vv Bd junk :=
  ⟨by rw [hfr.st hS, h.mat], by rw [hfr.sh hS, h.math], h.hr, h.hv, by rw [hfr.val hRg.1, h.RB],
    by rw [hfr.val hRg.2.1, h.V], by rw [hfr.val hRg.2.2, h.CC], h.bd, h.bD, h.hW, h.D0⟩

theorem OutOn.same {σ0 σ1 : MS} {O : Str} {CO : Reg} {out L0 : List Bool} (h : OutOn σ0 O CO out L0)
    {S : List Str} {Rg : List Reg} (hfr : SameExcept σ0 σ1 S Rg) (hO : O ∉ S) (hC : CO ∉ Rg) :
    OutOn σ1 O CO out L0 := ⟨by rw [hfr.st hO, h.1], by rw [hfr.sh hO, h.2.1], by rw [hfr.val hC, h.2.2]⟩

/-! ## One row -/

/-- Row `i`: `AV := a_iv`, `RJ := r·C`, then `C` entries. -/
def rowP : WMX NS NR :=
  .seq (addR rIJ rIV rTa) (.seq (addR rV rIV rTa) (.seq (getAt sMAT wK rCA rCW rIV rK2)
    (.seq (BinW.copy wAV wK rF rR) (.seq (.wm (WM.clear rIV)) (.seq (addR rRB rRJ rTa) (.seq (addR rCC rLJ rTa)
      (.seq (.whr rLJ (.seq (WMX.dec rLJ) entryP)) (.wm (WM.clear rRJ)))))))))

/-- The record values of row `i` of the next matrix. -/
def rowVals (a : ℕ → ℕ → ℤ) (D : ℤ) (r vv i C : ℕ) : List ℕ := (List.range C).map fun j => encS (upd a D r vv i j)

/-- The cost of the steps of `rowP`, in the unit `U`. -/
def rowSteps (U C k : ℕ) : ℕ := (7 - k) * (U + 1) + (C * (12 * U + 4) + 1) + 1 + U

theorem rowCost_le (U C : ℕ) (hU : 16 ≤ U) : rowSteps U C 0 ≤ (C + 1) * (13 * U) := by
  unfold rowSteps; nlinarith

/-- The invariant of the entry loop of row `i` after `k` entries. -/
def RowInv (σ7 : MS) (W : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (r vv i C : ℕ) (out L0 : List Bool) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ8 v8, At σ8 τ W v8 ∧ OutOn σ8 sNEW rCN (out ++ recBits W (rowVals a D r vv i k)) L0 ∧
    σ8.val rIJ = i * C + k ∧ σ8.val rRJ = r * C + k ∧ SameExcept σ7 σ8 [sNEW] [rCN, rIJ, rRJ, rLJ] ∧
    v8 wPW = encS (a r vv) ∧ v8 wAV = encS (a i vv) ∧ v8 wDD = encS D

theorem cap_facts {N W cap : ℕ} (hcap : capE N W ≤ cap) :
    (N + 1) * (2 * (W + 1) + 1) + 2 * N ≤ cap ∧ 2 * (W + 1) + 1 ≤ cap ∧
    (N + 1) * (2 * (W + 1) + 1) + 2 * N + N * (2 * (W + 1) + 1) + N * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap := by
  unfold capE at hcap
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- One entry of the row loop. -/
theorem row_step (cap : ℕ) {σ7 : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ} {r vv Bd : ℕ} {junk : List Bool}
    (hc7 : PassCtx σ7 W R C a D r vv Bd junk) {i : ℕ} (hi : i < R) {out L0 : List Bool}
    (hol : out.length ≤ R * C * (2 * (W + 1) + 1)) (hcap : capE (R * C) W ≤ cap) (k : ℕ) (hk : k < C) (τ : MS)
    (hI : RowInv σ7 W a D r vv i C out L0 k τ) :
    Runs cap entryP (τ.setv rLJ (C - k - 1)) (12 * ucost W (R * C))
      (fun ρ => RowInv σ7 W a D r vv i C out L0 (k + 1) ρ ∧ ρ.val rLJ = C - k - 1) := by
  obtain ⟨σ8, v8, h8, hout8, hIJ8, hRJ8, hfr8, hP8, hA8, hD8⟩ := hI
  obtain ⟨cap1, -, cap3⟩ := cap_facts hcap
  have hCN : C ≤ R * C := Nat.le_mul_of_pos_left _ (by omega)
  have h8' := h8.setv (r := rLJ) (by decide) (C - k - 1)
  have hc8 : PassCtx (σ8.setv rLJ (C - k - 1)) W R C a D r vv Bd junk :=
    (hc7.same hfr8 (by decide) (by decide)).same (S := []) (Rg := [rLJ])
      (sameExcept_setv σ8 (by simp) _) (by simp) (by decide)
  have hIJ8' : (σ8.setv rLJ (C - k - 1)).val rIJ = i * C + k := by simp (config := {decide := true}) [hIJ8]
  have hRJ8' : (σ8.setv rLJ (C - k - 1)).val rRJ = r * C + k := by simp (config := {decide := true}) [hRJ8]
  have hidx1 : (σ8.setv rLJ (C - k - 1)).val rIJ < (matV R C a).length := by
    rw [hIJ8', matV_length]; exact idx_lt hi hk
  have hidx2 : (σ8.setv rLJ (C - k - 1)).val rRJ < (matV R C a).length := by
    rw [hRJ8', matV_length]; exact idx_lt hc7.hr hk
  have hxij : (matV R C a)[(σ8.setv rLJ (C - k - 1)).val rIJ] = encS (a i k) := by
    simp only [hIJ8']; exact matV_get R C a hi hk
  have hxrj : (matV R C a)[(σ8.setv rLJ (C - k - 1)).val rRJ] = encS (a r k) := by
    simp only [hRJ8']; exact matV_get R C a hc7.hr hk
  have hout8' : OutOn (σ8.setv rLJ (C - k - 1)) sNEW rCN (out ++ recBits W (rowVals a D r vv i k)) L0 :=
    OutOn.same hout8 (sameExcept_setv σ8 (S := []) (Rg := [rLJ]) (by simp) _) (by simp) (by decide)
  have hlen : (out ++ recBits W (rowVals a D r vv i k)).length ≤
      R * C * (2 * (W + 1) + 1) + R * C * (2 * (W + 1) + 1) := by
    rw [List.length_append, recBits_length]; simp only [rowVals, List.length_map, List.length_range]
    have := Nat.mul_le_mul_right (2 * (W + 1) + 1) (show k ≤ R * C by omega)
    omega
  have hcapE : ((matV R C a).length + 1) * (2 * (W + 1) + 1) + 2 * (matV R C a).length +
      (out ++ recBits W (rowVals a D r vv i k)).length + 2 * (W + 1) + 2 ≤ cap := by
    rw [matV_length]; omega
  have hiC : i * C + k < R * C := idx_lt hi hk
  have hrC : r * C + k < R * C := idx_lt hc7.hr hk
  have he := entry_spec cap h8' (matV R C a) junk hc8.mat hc8.math hidx1 hidx2 hxij hxrj (P := a r vv)
    (A := a i vv) (D := D) hP8 hA8 hD8 hc7.D0 (Bd := Bd)
    ⟨hc7.bd i k hi hk, hc7.bd r k hc7.hr hk, hc7.bd r vv hc7.hr hc7.hv, hc7.bd i vv hi hc7.hv, hc7.bD, hc7.hW⟩
    hout8' hcapE (by rw [hIJ8', hRJ8']; constructor <;> nlinarith)
  rw [matV_length] at he
  refine he.post (fun ρ ⟨σ9, v9, h9, hout9, hIJ9, hRJ9, hfr9, hP9, hA9, hD9⟩ => ⟨⟨σ9, v9, h9, ?_, ?_, ?_, ?_,
    by rw [hP9, hP8], by rw [hA9, hA8], by rw [hD9, hD8]⟩, ?_⟩)
  · have e : out ++ recBits W (rowVals a D r vv i (k + 1)) = out ++ recBits W (rowVals a D r vv i k) ++
        frame (binary (W + 1) (encS (Int.tdiv (a i k * a r vv - a r k * a i vv) D))) := by
      rw [rowVals, List.range_succ, List.map_append, recBits_append, ← List.append_assoc]
      congr 2
      simp only [List.map_cons, List.map_nil, recBits, List.flatMap_cons, List.flatMap_nil, List.append_nil, upd]
      congr 4; ring
    rw [e]; exact hout9
  · rw [hIJ9, hIJ8']; ring
  · rw [hRJ9, hRJ8']; ring
  · refine SameExcept.trans hfr8 ?_
    have h1 := (sameExcept_setv σ8 (S := [sNEW]) (Rg := [rCN, rIJ, rRJ, rLJ]) (r := rLJ) (by simp) (C - k - 1))
    exact SameExcept.trans h1 (hfr9.weaken (by simp) (by simp))
  · rw [h9.val (by decide), hfr9.val (by decide)]; simp

theorem row_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ}
    {r vv Bd : ℕ} {junk : List Bool} (hc : PassCtx σ0 W R C a D r vv Bd junk) {i : ℕ} (hi : i < R)
    (hIJ : σ0.val rIJ = i * C) (hIV : σ0.val rIV = 0) (hRJ : σ0.val rRJ = 0) (hLJ : σ0.val rLJ = 0)
    (hP : v wPW = encS (a r vv)) (hD : v wDD = encS D) {out L0 : List Bool} (hout : OutOn σ0 sNEW rCN out L0)
    (hol : out.length ≤ R * C * (2 * (W + 1) + 1)) (hcap : capE (R * C) W ≤ cap) :
    Runs cap rowP σ ((C + 1) * (13 * ucost W (R * C))) (fun τ => ∃ σ1 v', At σ1 τ W v' ∧
      OutOn σ1 sNEW rCN (out ++ recBits W (rowVals a D r vv i C)) L0 ∧ σ1.val rIJ = (i + 1) * C ∧
      σ1.val rIV = 0 ∧ σ1.val rRJ = 0 ∧ σ1.val rLJ = 0 ∧
      SameExcept σ0 σ1 [sNEW] [rCN, rIJ, rIV, rRJ, rLJ] ∧ v' wPW = v wPW ∧ v' wDD = v wDD) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  obtain ⟨N, hN⟩ : ∃ N, N = R * C := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ U, U = ucost W N := ⟨_, rfl⟩
  rw [← hN] at hol hcap cap1 ⊢
  rw [← hUd]
  have hU : 16 ≤ U := hUd ▸ one_le_ucost W N
  have hUN : 4000 * (N + 2) ≤ U := hUd ▸ ucost_geN W N
  have hUL : 500 * W + 700 ≤ U := hUd ▸ lin_le_ucost W N
  have hCN : C ≤ N := by
    have : 1 ≤ R := by omega
    rw [hN]; exact Nat.le_mul_of_pos_left _ this
  have hiC : i * C + C ≤ N := by
    rw [hN]; have := Nat.mul_le_mul_right C (show i + 1 ≤ R from hi); rw [Nat.add_mul, one_mul] at this; exact this
  have hrC : r * C + C ≤ N := by
    rw [hN]; have := Nat.mul_le_mul_right C (show r + 1 ≤ R from hc.hr); rw [Nat.add_mul, one_mul] at this; exact this
  have hvC := hc.hv
  refine Runs.cost ?_ (rowCost_le U C hU)
  -- 1–2. `IV := i·C + vv`
  refine Runs.seq' ((opAddR cap h (A := rIJ) (B := rIV) (by decide) (by decide) (by decide)
    (by rw [hIV, hIJ]; omega)).cost (show 18 * σ0.val rIJ + 3 ≤ U by rw [hIJ]; omega)) (fun τ1 h1 => ?_)
    (c2 := rowSteps U C 1) (by unfold rowSteps; omega)
  set σ1 := σ0.setv rIV (σ0.val rIV + σ0.val rIJ) with hσ1
  refine Runs.seq' ((opAddR cap h1 (A := rV) (B := rIV) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hIV, hIJ, hc.V]; omega)).cost
      (show 18 * σ1.val rV + 3 ≤ U by simp (config := {decide := true}) [hσ1, hc.V]; omega))
    (fun τ2 h2 => ?_) (c2 := rowSteps U C 2) (by unfold rowSteps; omega)
  set σ2 := σ1.setv rIV (σ1.val rIV + σ1.val rV) with hσ2
  have h2IV : σ2.val rIV = i * C + vv := by simp (config := {decide := true}) [hσ2, hσ1, hIV, hIJ, hc.V]
  have hc2 : PassCtx σ2 W R C a D r vv Bd junk := hc.same (S := []) (Rg := [rIV])
    (by refine ⟨fun x _ => ⟨rfl, rfl⟩, fun q hq => ?_, rfl⟩
        have : q ≠ rIV := by simpa using hq
        simp [hσ2, hσ1, Function.update_of_ne this]) (by simp) (by decide)
  -- 3. `wK := a i vv`
  have hidx : σ2.val rIV < (matV R C a).length := by rw [h2IV, matV_length]; exact idx_lt hi hc.hv
  have hgl := getAt_le W N (σ2.val rIV) (by rw [h2IV]; omega)
  rw [← hUd] at hgl
  refine Runs.seq' ((opGetAt cap h2 (A := sMAT) (IX := rIV) (by decide) (by decide) (matV R C a) junk hc2.mat
    hc2.math hidx (by rw [matV_length, ← hN, h2IV]; omega)).cost hgl)
    (fun τ3 h3 => ?_) (c2 := rowSteps U C 3) (by unfold rowSteps; omega)
  have hxiv : (matV R C a)[σ2.val rIV] = encS (a i vv) := by simp only [h2IV]; exact matV_get R C a hi hc.hv
  rw [hxiv] at h3
  -- 4. `AV := a i vv`
  refine Runs.seq' ((opCopy cap h3 (X := wAV) (Y := wK) (by decide) (by decide) (by decide) cap2).cost
    (show 41 * (W + 1) + 3 ≤ U by omega)) (fun τ4 h4 => ?_)
    (c2 := rowSteps U C 4) (by unfold rowSteps; omega)
  -- 5. `IV := 0`
  refine Runs.seq' ((opClearR cap h4 (r := rIV) (by decide) (by rw [h2IV]; omega)).cost
    (show 3 * σ2.val rIV + 1 ≤ U by rw [h2IV]; omega)) (fun τ5 h5 => ?_)
    (c2 := rowSteps U C 5) (by unfold rowSteps; omega)
  set σ5 := σ2.setv rIV 0 with hσ5
  -- 6. `RJ := r·C`
  refine Runs.seq' ((opAddR cap h5 (A := rRB) (B := rRJ) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ5, hσ2, hσ1, hRJ, hc.RB]; omega)).cost
      (show 18 * σ5.val rRB + 3 ≤ U by simp (config := {decide := true}) [hσ5, hσ2, hσ1, hc.RB]; omega))
    (fun τ6 h6 => ?_) (c2 := rowSteps U C 6) (by unfold rowSteps; omega)
  set σ6 := σ5.setv rRJ (σ5.val rRJ + σ5.val rRB) with hσ6
  -- 7. `LJ := C`
  refine Runs.seq' ((opAddR cap h6 (A := rCC) (B := rLJ) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ6, hσ5, hσ2, hσ1, hLJ, hc.CC]; omega)).cost
      (show 18 * σ6.val rCC + 3 ≤ U by simp (config := {decide := true}) [hσ6, hσ5, hσ2, hσ1, hc.CC]; omega))
    (fun τ7 h7 => ?_) (c2 := rowSteps U C 7) (by unfold rowSteps; omega)
  set σ7 := σ6.setv rLJ (σ6.val rLJ + σ6.val rCC) with hσ7
  have h7IJ : σ7.val rIJ = i * C := by simp (config := {decide := true}) [hσ7, hσ6, hσ5, hσ2, hσ1, hIJ]
  have h7RJ : σ7.val rRJ = r * C := by simp (config := {decide := true}) [hσ7, hσ6, hσ5, hσ2, hσ1, hRJ, hc.RB]
  have h7LJ : σ7.val rLJ = C := by simp (config := {decide := true}) [hσ7, hσ6, hσ5, hσ2, hσ1, hLJ, hc.CC]
  have h7IV : σ7.val rIV = 0 := by simp (config := {decide := true}) [hσ7, hσ6, hσ5]
  have h7fr : SameExcept σ0 σ7 [] [rIJ, rRJ, rLJ, rIV] := by
    refine ⟨fun x _ => ⟨rfl, rfl⟩, fun q hq => ?_, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hq.1, Function.update_of_ne hq.2.1,
      Function.update_of_ne hq.2.2.1, Function.update_of_ne hq.2.2.2]
  have hc7 : PassCtx σ7 W R C a D r vv Bd junk := hc.same h7fr (by simp) (by decide)
  -- 8. the entry loop
  have hI0 : RowInv σ7 W a D r vv i C out L0 0 τ7 := by
    refine ⟨σ7, _, h7, ?_, by rw [h7IJ]; ring, by rw [h7RJ]; ring, SameExcept.refl _ _ _, ?_, ?_, ?_⟩
    · simpa [rowVals, recBits] using OutOn.same hout h7fr (by simp) (by decide)
    · simp (config := {decide := true}) [hP]
    · simp
    · simp (config := {decide := true}) [hD]
  have hloop := Runs.count (cap := cap) (K := rLJ) (body := entryP) (12 * U) C
    (RowInv σ7 W a D r vv i C out L0) (by omega)
    (fun k hk τ hτ _ => by
      have := row_step cap hc7 hi (by rw [← hN]; exact hol) (by rw [← hN]; exact hcap) k hk τ hτ
      rw [← hN, ← hUd] at this; exact this) τ7 hI0 (by rw [h7.val (by decide), h7LJ])
  refine Runs.seq' hloop (fun τ8 ⟨⟨σ8, v8, h8, hout8, hIJ8, hRJ8, hfr8, hP8, hA8, hD8⟩, hK8⟩ => ?_)
    (c2 := U) (by unfold rowSteps; omega)
  -- 9. `RJ := 0`
  refine ((opClearR cap h8 (r := rRJ) (by decide) (by rw [hRJ8]; omega)).cost
    (show 3 * σ8.val rRJ + 1 ≤ U by rw [hRJ8]; omega)).post (fun τ9 h9 => ?_)
  have hLJ8 : σ8.val rLJ = 0 := by rw [← h8.val (by decide)]; exact hK8
  have hIV8 : σ8.val rIV = 0 := by rw [hfr8.val (by decide)]; exact h7IV
  refine ⟨_, v8, h9, ⟨by simpa using hout8.1, by simpa using hout8.2.1,
    by simp (config := {decide := true}) [hout8.2.2]⟩, ?_, ?_, ?_, ?_, ?_, by rw [hP8, hP], by rw [hD8, hD]⟩
  · simp (config := {decide := true}) [hIJ8]; ring
  · simp (config := {decide := true}) [hIV8]
  · simp (config := {decide := true})
  · simp (config := {decide := true}) [hLJ8]
  · refine SameExcept.trans (h7fr.weaken (by simp) (by simp)) (SameExcept.trans (hfr8.weaken (by simp) (by simp)) ?_)
    exact sameExcept_setv σ8 (by simp) _

/-! ## One pass -/

/-- All `R` rows (`LI := R`, then the row loop). -/
def passP : WMX NS NR := .seq (addR rRR rLI rTa) (.whr rLI (.seq (WMX.dec rLI) rowP))

theorem matV_succ (k C : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (r vv : ℕ) :
    matV (k + 1) C (upd a D r vv) = matV k C (upd a D r vv) ++ rowVals a D r vv k C := by
  simp [matV, flat_succ, rowVals]

/-- The invariant of the row loop after `k` rows. -/
def PassInv (σA : MS) (W C : ℕ) (a : ℕ → ℕ → ℤ) (D : ℤ) (r vv : ℕ) (L0 : List Bool) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ OutOn σ1 sNEW rCN (recBits W (matV k C (upd a D r vv))) L0 ∧ σ1.val rIJ = k * C ∧
    σ1.val rIV = 0 ∧ σ1.val rRJ = 0 ∧ σ1.val rLJ = 0 ∧ SameExcept σA σ1 [sNEW] [rCN, rIJ, rIV, rRJ, rLJ, rLI] ∧
    v1 wPW = encS (a r vv) ∧ v1 wDD = encS D

/-- The cost bound of the pass. -/
def passCost (R C U : ℕ) : ℕ := (R + 2) * ((C + 1) * (13 * U) + 4)

theorem pass_step (cap : ℕ) {σA : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ} {r vv Bd : ℕ} {junk L0 : List Bool}
    (hcA : PassCtx σA W R C a D r vv Bd junk) (hcap : capE (R * C) W ≤ cap) (k : ℕ) (hk : k < R) (τ : MS)
    (hI : PassInv σA W C a D r vv L0 k τ) :
    Runs cap rowP (τ.setv rLI (R - k - 1)) ((C + 1) * (13 * ucost W (R * C)))
      (fun ρ => PassInv σA W C a D r vv L0 (k + 1) ρ ∧ ρ.val rLI = R - k - 1) := by
  obtain ⟨σ1, v1, h1, hout1, hIJ1, hIV1, hRJ1, hLJ1, hfr1, hP1, hD1⟩ := hI
  have h1' := h1.setv (r := rLI) (by decide) (R - k - 1)
  have hfr1' : SameExcept σA (σ1.setv rLI (R - k - 1)) [sNEW] [rCN, rIJ, rIV, rRJ, rLJ, rLI] :=
    SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc1 : PassCtx (σ1.setv rLI (R - k - 1)) W R C a D r vv Bd junk := hcA.same hfr1' (by decide) (by decide)
  have hlen : (recBits W (matV k C (upd a D r vv))).length ≤ R * C * (2 * (W + 1) + 1) := by
    rw [recBits_length, matV_length]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk.le)
  have hr := row_spec cap h1' hc1 hk (by simp (config := {decide := true}) [hIJ1])
    (by simp (config := {decide := true}) [hIV1]) (by simp (config := {decide := true}) [hRJ1])
    (by simp (config := {decide := true}) [hLJ1]) hP1 hD1
    (OutOn.same hout1 (sameExcept_setv σ1 (S := []) (Rg := [rLI]) (by simp) _) (by simp) (by decide)) hlen hcap
  refine hr.post (fun ρ ⟨σ2, v2, h2, hout2, hIJ2, hIV2, hRJ2, hLJ2, hfr2, hP2, hD2⟩ =>
    ⟨⟨σ2, v2, h2, by rw [matV_succ, recBits_append]; exact hout2, hIJ2, hIV2, hRJ2, hLJ2,
      SameExcept.trans hfr1' (hfr2.weaken (by simp) (by simp)), by rw [hP2, hP1], by rw [hD2, hD1]⟩, ?_⟩)
  rw [h2.val (by decide), hfr2.val (by decide)]; simp

theorem pass_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C : ℕ} {a : ℕ → ℕ → ℤ} {D : ℤ}
    {r vv Bd : ℕ} {junk L0 : List Bool} (hc : PassCtx σ0 W R C a D r vv Bd junk) (hRR : σ0.val rRR = R)
    (hIJ : σ0.val rIJ = 0) (hIV : σ0.val rIV = 0) (hRJ : σ0.val rRJ = 0) (hLJ : σ0.val rLJ = 0)
    (hLI : σ0.val rLI = 0) (hP : v wPW = encS (a r vv)) (hD : v wDD = encS D) (hout : OutOn σ0 sNEW rCN [] L0)
    (hcap : capE (R * C) W ≤ cap) :
    Runs cap passP σ (passCost R C (ucost W (R * C))) (fun τ => ∃ σ1 v', At σ1 τ W v' ∧
      OutOn σ1 sNEW rCN (recBits W (matV R C (upd a D r vv))) L0 ∧ σ1.val rIJ = R * C ∧
      σ1.val rIV = 0 ∧ σ1.val rRJ = 0 ∧ σ1.val rLJ = 0 ∧ σ1.val rLI = 0 ∧
      SameExcept σ0 σ1 [sNEW] [rCN, rIJ, rIV, rRJ, rLJ, rLI] ∧ v' wPW = v wPW ∧ v' wDD = v wDD) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  have hU := one_le_ucost W (R * C)
  have hUN := ucost_geN W (R * C)
  have hRN : R ≤ R * C + 2 := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · have := hc.hv; omega
    · have := Nat.le_mul_of_pos_right R h0; omega
  refine Runs.seq' (opAddR cap h (A := rRR) (B := rLI) (by decide) (by decide) (by decide)
    (by rw [hLI, hRR]; omega)) (fun τ1 h1 => ?_) (c2 := R * ((C + 1) * (13 * ucost W (R * C)) + 4) + 1)
    (by unfold passCost; rw [hRR]; nlinarith)
  set σ1 := σ0.setv rLI (σ0.val rLI + σ0.val rRR) with hσ1
  have hc1 : PassCtx σ1 W R C a D r vv Bd junk := hc.same (S := []) (Rg := [rLI]) (sameExcept_setv σ0 (by simp) _)
    (by simp) (by decide)
  have hI0 : PassInv σ1 W C a D r vv L0 0 τ1 := by
    refine ⟨σ1, v, h1, ?_, by simp (config := {decide := true}) [hσ1, hIJ], by simp (config := {decide := true}) [hσ1, hIV],
      by simp (config := {decide := true}) [hσ1, hRJ], by simp (config := {decide := true}) [hσ1, hLJ],
      SameExcept.refl _ _ _, hP, hD⟩
    simpa [matV, flat, recBits] using OutOn.same hout (sameExcept_setv σ0 (S := []) (Rg := [rLI]) (by simp) _)
      (by simp) (by decide)
  have hloop := Runs.count (cap := cap) (K := rLI) (body := rowP) ((C + 1) * (13 * ucost W (R * C))) R
    (PassInv σ1 W C a D r vv L0) (by omega) (fun k hk τ hτ _ => pass_step cap hc1 hcap k hk τ hτ) τ1 hI0
    (by rw [h1.val (by decide)]; simp (config := {decide := true}) [hσ1, hLI, hRR])
  refine hloop.post (fun τ ⟨⟨σ2, v2, h2, hout2, hIJ2, hIV2, hRJ2, hLJ2, hfr2, hP2, hD2⟩, hK⟩ =>
    ⟨σ2, v2, h2, hout2, hIJ2, hIV2, hRJ2, hLJ2, by rw [← h2.val (by decide)]; exact hK, ?_, by rw [hP2, hP],
      by rw [hD2, hD]⟩)
  exact SameExcept.trans (sameExcept_setv σ0 (S := [sNEW]) (Rg := [rCN, rIJ, rIV, rRJ, rLJ, rLI]) (by simp) _) hfr2

end NearCubicGates.Close.Solve
