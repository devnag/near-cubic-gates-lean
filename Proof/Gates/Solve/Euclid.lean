import Proof.Gates.Solve.Gcd

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

abbrev wG1 : Str := 26
abbrev wG2 : Str := 13
abbrev rLE : Reg := 58

/-- One guarded Euclid step on `(wG1, wG2)`. -/
def euclidBody : WMX NS NR :=
  .seq (nzP wG2 wZ rNZ rF rR) (.ifr rNZ (.seq (WMX.dec rNZ) (.seq (BinW.divmod wG1 wG2 wC wD wE rF rR rK rT2)
    (.seq (BinW.copy wG1 wG2 rF rR) (BinW.copy wG2 wD rF rR)))) WMX.skip)

/-- `2(W+1)+1` guarded steps (`rLE := rR2`). -/
def euclidP : WMX NS NR := .seq (addR rR2 rLE rTa) (.whr rLE (.seq (WMX.dec rLE) euclidBody))

/-- The Euclid loop invariant after `k` steps. -/
def GInv (σA : MS) (W a b : ℕ) (v : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rNZ = 0 ∧ SameExcept σA σ1 [] [rNZ, rLE] ∧
    v1 wG1 = (ePow k (a, b)).1 ∧ v1 wG2 = (ePow k (a, b)).2 ∧ ∀ X, X ∉ [wG1, wG2, wC, wD, wE] → v1 X = v X

theorem ePow_succ' (k : ℕ) (p : ℕ × ℕ) : ePow (k + 1) p = eStep (ePow k p) := by
  rw [ePow_add k 1]; rfl

theorem euclid_step (cap : ℕ) {σA : MS} {W a b : ℕ} {v : Str → ℕ} (ha : a < 2 ^ W) (hb : b < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) (n k : ℕ) (τ : MS) (hI : GInv σA W a b v k τ) :
    Runs cap euclidBody (τ.setv rLE (n - k - 1)) (3 * ucost W 0)
      (fun ρ => GInv σA W a b v (k + 1) ρ ∧ ρ.val rLE = n - k - 1) := by
  obtain ⟨σ1, v1, h1, hNZ, hfr, hG1, hG2, ho⟩ := hI
  have h1' := h1.setv (r := rLE) (by decide) (n - k - 1)
  set σ2 := σ1.setv rLE (n - k - 1) with hσ2
  have hfr2 : SameExcept σA σ2 [] [rNZ, rLE] := hfr.trans (sameExcept_setv σ1 (by simp) _)
  have hNZ2 : σ2.val rNZ = 0 := by simp (config := {decide := true}) [hσ2, hNZ]
  have hbd : (ePow k (a, b)).1 ≤ max a b ∧ (ePow k (a, b)).2 ≤ max a b := ePow_le k (a, b)
  have hmx : max a b < 2 ^ W := max_lt ha hb
  have hp1 : (ePow k (a, b)).1 < 2 ^ W := lt_of_le_of_lt hbd.1 hmx
  have hp2 : (ePow k (a, b)).2 < 2 ^ W := lt_of_le_of_lt hbd.2 hmx
  have hpw : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
  have hU := one_le_ucost W 0
  have hUL := lin_le_ucost W 0
  have hd := div_le W 0
  have hstep := ePow_succ' k (a, b)
  refine Runs.seq' (opNz cap h1' (X := wG2) (NZ := rNZ) (by decide) (by decide) (by decide) hNZ2
    (by rw [hG2]; omega) hcap) (fun τ2 h2 => ?_) (c2 := 2 * ucost W 0) (by omega)
  by_cases hz : (ePow k (a, b)).2 = 0
  · have e0 : (decide (v1 wG2 ≠ 0)).toNat = 0 := by rw [hG2, hz]; rfl
    rw [e0] at h2
    refine (Runs.ifrF (c := 0) (by rw [h2.val (by decide)]; simp)
      (Runs.of (WXExec.skip cap τ2) ⟨⟨σ2.setv rNZ 0, v1, h2, by simp, ?_, ?_, ?_, ho⟩, ?_⟩)).cost (by omega)
    · exact hfr2.trans (sameExcept_setv σ2 (by simp) _)
    · rw [hG1, hstep]; simp [eStep, hz]
    · rw [hG2, hstep]; simp [eStep, hz]
    · rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2]
  · have e1 : (decide (v1 wG2 ≠ 0)).toNat = 1 := by rw [hG2]; simp [hz]
    rw [e1] at h2
    refine (Runs.ifrT (c := 2 * ucost W 0 - 1) (by rw [h2.val (by decide)]; simp) ?_).cost (by omega)
    refine Runs.seq' (opDecR cap h2 (r := rNZ) (by decide) (by simp (config := {decide := true}); omega))
      (fun τ3 h3 => ?_) (c2 := 2 * ucost W 0 - 3) (by omega)
    set σ3 := (σ2.setv rNZ 1).setv rNZ ((σ2.setv rNZ 1).val rNZ - 1) with hσ3
    have hfr3 : SameExcept σA σ3 [] [rNZ, rLE] :=
      (hfr2.trans (sameExcept_setv σ2 (by simp) _)).trans (sameExcept_setv _ (by simp) _)
    have hNZ3 : σ3.val rNZ = 0 := by simp [hσ3]
    have hLE3 : σ3.val rLE = n - k - 1 := by simp (config := {decide := true}) [hσ3, hσ2]
    refine Runs.seq' ((opDivmod cap h3 (A := wG1) (B := wG2) (Q := wC) (M := wD) (E := wE) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [hG1]; omega) (by rw [hG2]; omega)
      (by rw [hG2]; omega) hcap).cost hd) (fun τ4 h4 => ?_) (c2 := ucost W 0 - 4) (by omega)
    refine Runs.seq' (opCopy cap h4 (X := wG1) (Y := wG2) (by decide) (by decide) (by decide) hcap) (fun τ5 h5 => ?_)
      (c2 := 41 * (W + 1) + 3) (by omega)
    refine (opCopy cap h5 (X := wG2) (Y := wD) (by decide) (by decide) (by decide) hcap).post (fun ρ hρ =>
      ⟨⟨σ3, _, hρ, hNZ3, hfr3, ?_, ?_, ?_⟩, by rw [hρ.val (by decide)]; exact hLE3⟩)
    · rw [hstep]; simp (config := {decide := true}) [eStep, hz, hG2]
    · rw [hstep]; simp (config := {decide := true}) [eStep, hz, hG1, hG2]
    · intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hX
      obtain ⟨n1, n2, n3, n4, n5⟩ := hX
      rw [Function.update_of_ne n2, Function.update_of_ne n1, Function.update_of_ne n5, Function.update_of_ne n4,
        Function.update_of_ne n3]
      exact ho X (by simp [n1, n2, n3, n4, n5])

/-- The cost of `euclidP`. -/
def euclidCost (W : ℕ) : ℕ := 18 * (2 * (W + 1) + 1) + 3 + 1 + ((2 * (W + 1) + 1) * (3 * ucost W 0 + 4) + 1)

theorem euclid_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (hNZ : σ0.val rNZ = 0)
    (hLE : σ0.val rLE = 0) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1) (ha : v wG1 < 2 ^ W) (hb : v wG2 < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap euclidP σ (euclidCost W) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rNZ = 0 ∧ σ1.val rLE = 0 ∧
      SameExcept σ0 σ1 [] [rNZ, rLE] ∧ v1 wG1 = Nat.gcd (v wG1) (v wG2) ∧
      ∀ X, X ∉ [wG1, wG2, wC, wD, wE] → v1 X = v X) := by
  set N := 2 * (W + 1) + 1 with hN
  refine Runs.seq' (opAddR cap h (A := rR2) (B := rLE) (by decide) (by decide) (by decide) (by rw [hLE, hR2]; omega))
    (fun τ1 h1 => ?_) (c2 := N * (3 * ucost W 0 + 4) + 1) (by unfold euclidCost; rw [hR2])
  set σ1 := σ0.setv rLE (σ0.val rLE + σ0.val rR2) with hσ1
  have hfr1 : SameExcept σ0 σ1 [] [rNZ, rLE] := sameExcept_setv σ0 (by simp) _
  have hloop := Runs.count (cap := cap) (K := rLE) (body := euclidBody) (3 * ucost W 0) N
    (GInv σ1 W (v wG1) (v wG2) v) (by omega)
    (fun k _ τ hτ _ => euclid_step cap ha hb hcap N k τ hτ) τ1
    ⟨σ1, v, h1, by simp (config := {decide := true}) [hσ1, hNZ], SameExcept.refl _ _ _, rfl, rfl, fun _ _ => rfl⟩
    (by rw [h1.val (by decide)]; simp (config := {decide := true}) [hσ1, hLE, hR2])
  refine hloop.post (fun τ ⟨⟨σ2, v2, h2, hNZ2, hfr2, hG1, _, ho⟩, hK⟩ => ⟨σ2, v2, h2, hNZ2, ?_, hfr1.trans hfr2, ?_, ho⟩)
  · rw [← h2.val (by decide)]; exact hK
  · have e : ePow N (v wG1, v wG2) = (Nat.gcd (v wG1) (v wG2), 0) := by
      rw [hN, show 2 * (W + 1) + 1 = 2 * (W + 1) + 1 by rfl, ePow_add, ePow_result _ _ (W + 1)
        (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))), ePow_zero_fix]
    rw [hG1, e]

end NearCubicGates.Close.Solve
