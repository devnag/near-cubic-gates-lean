import Proof.Gates.Solve.Points3

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

abbrev rLR : Reg := 43
abbrev rSLN : Reg := 44
abbrev rLS : Reg := 45
abbrev rCSG : Reg := 46
abbrev rPB : Reg := 47
abbrev rNZQ : Reg := 48
abbrev rFL : Reg := 49
abbrev rT4 : Reg := 50
abbrev rISG : Reg := 51
abbrev rIXP : Reg := 52
abbrev rLP2 : Reg := 53
abbrev wQ : Str := 19
abbrev wB : Str := 23
abbrev wSG : Str := 24
abbrev wE2 : Str := 25

/-! ## The residue test, value level -/

/-- The test of coordinate `i`: `|u_i − σ_i| mod q = 0` (for `q = 0`: `u_i = σ_i`). -/
abbrev testOK (q : ℕ) (σ : List ℕ) (u : List ℤ) (i : ℕ) : Prop := (u.getD i 0 - (σ.getD i 0 : ℤ)).natAbs % q = 0

theorem inClass_iff (q : ℕ) (σ : List ℕ) (u : List ℤ) :
    inClass q σ u = true ↔ ∀ i < σ.length, testOK q σ u i := by
  unfold inClass testOK
  rw [List.all_eq_true]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have := h i (List.mem_range.mpr hi)
    rw [decide_eq_true_iff, Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero,
      Int.ofNat_dvd_left] at this
    exact Nat.mod_eq_zero_of_dvd this
  · have := h i (List.mem_range.mp hi)
    rw [decide_eq_true_iff, Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero, Int.ofNat_dvd_left]
    exact Nat.dvd_of_mod_eq_zero this

/-- The point records: point `j`, coordinate `i` at index `j·ℓ + i`. -/
theorem ptVals_get (ℓ : ℕ) : ∀ (pts : List (List ℤ)) (j i : ℕ) (hj : j < pts.length) (hi : i < ℓ),
    (pts.flatMap (ptVals ℓ))[j * ℓ + i]'(by
      rw [List.length_flatMap]; simp only [ptVals, List.length_map, List.length_range, List.map_const',
        List.sum_replicate, smul_eq_mul]
      have : (j + 1) * ℓ ≤ pts.length * ℓ := Nat.mul_le_mul_right _ hj
      nlinarith) = encS ((pts[j]).getD i 0)
  | [], j, _, hj, _ => absurd hj (by simp)
  | u :: us, 0, i, _, hi => by
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add]
    rw [List.getElem_append_left (by simp [ptVals]; exact hi)]
    simp [ptVals]
  | u :: us, j + 1, i, hj, hi => by
    simp only [List.flatMap_cons]
    rw [List.getElem_append_right (by simp [ptVals]; nlinarith)]
    have e : (j + 1) * ℓ + i - (ptVals ℓ u).length = j * ℓ + i := by simp [ptVals]; ring_nf; omega
    simp only [e]
    exact ptVals_get ℓ us j i (by simpa using hj) hi

/-- The `σ` records: `encS σ_i = 2·σ_i`. -/
def sgVals (σ : List ℕ) : List ℕ := σ.map fun x : ℕ => encS ((x : ℕ) : ℤ)

theorem encS_nat (x : ℕ) : encS (x : ℤ) = 2 * x := by simp [encS]

end NearCubicGates.Close.Solve

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)

/-! ## The test program -/

/-- Coordinate `i`: clear `rFL` unless `q ∣ u_i − σ_i`; step the two indices. -/
def testP : WMX NS NR :=
  .seq (getAt sSG wK rCA rCW rISG rK2) (.seq (BinW.copy wSG wK rF rR)
  (.seq (getAt sPT wK rCA rCW rIXP rK2) (.seq (BinW.copy wX1 wK rF rR)
  (.seq (ssub wX1 wSG wM wN rS rT rF rR) (.seq (SInt.split wX1 wM rSGN rF rR)
  (.seq (.ifr rNZQ (.seq (BinW.divmod wM wQ wC wD wE rF rR rK rT2) (nzP wD wZ rT4 rF rR)) (nzP wM wZ rT4 rF rR))
  (.seq (.ifr rT4 (.seq (WMX.dec rT4) (.ifr rFL (WMX.dec rFL) WMX.skip)) WMX.skip)
  (.seq (.ifr rSGN (WMX.dec rSGN) WMX.skip)
  (.seq (WMX.inc rISG) (WMX.inc rIXP))))))))))

/-- The record streams a cell reads. -/
structure CellCtx (σ0 : MS) (W ℓ : ℕ) (pts : List (List ℤ)) (σl : List ℕ) (junkSG junkPT : List Bool) : Prop where
  sg : σ0.st sSG = recStream ((sgVals σl).map (binary (W + 1))) ++ junkSG
  sgh : σ0.sh sSG = 0
  pt : σ0.st sPT = recStream ((pts.flatMap (ptVals ℓ)).map (binary (W + 1))) ++ junkPT
  pth : σ0.sh sPT = 0

theorem CellCtx.same {σ0 σ1 : MS} {W ℓ : ℕ} {pts : List (List ℤ)} {σl : List ℕ} {jS jP : List Bool}
    (h : CellCtx σ0 W ℓ pts σl jS jP) {Rg : List Reg} (hfr : SameExcept σ0 σ1 [] Rg) : CellCtx σ1 W ℓ pts σl jS jP :=
  ⟨by rw [hfr.st (by simp), h.sg], by rw [hfr.sh (by simp), h.sgh], by rw [hfr.st (by simp), h.pt],
    by rw [hfr.sh (by simp), h.pth]⟩

/-- The words a cell keeps. -/
def keepW : List Str := [wZ, wQ, wB, wTWO]

/-- The test-loop invariant after `k` coordinates. -/
def TInv (σB : MS) (W : ℕ) (q : ℕ) (σl : List ℕ) (u : List ℤ) (PB : ℕ) (keep : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rISG = k ∧ σ1.val rIXP = PB + k ∧
    σ1.val rFL = (decide (∀ i < k, testOK q σl u i)).toNat ∧ σ1.val rSGN = 0 ∧ σ1.val rT4 = 0 ∧
    SameExcept σB σ1 [] [rISG, rIXP, rFL, rLS] ∧ ∀ X ∈ keepW, v1 X = keep X

end NearCubicGates.Close.Solve
