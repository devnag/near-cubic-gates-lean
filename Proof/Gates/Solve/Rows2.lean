import Proof.Gates.Solve.Rows

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

/-- The remainder test: `rT4 := [|d| mod q ≠ 0]` (`q ≠ 0` by `divmod`, `q = 0` directly). -/
theorem test_branch (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (q dd : ℕ)
    (hNZQ : σ0.val rNZQ = (decide (q ≠ 0)).toNat) (hT4 : σ0.val rT4 = 0) (hvq : v wQ = q) (hvm : v wM = dd)
    (hdd : dd < 2 ^ W) (hq : 2 * q ≤ 2 ^ (W + 1)) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (.ifr rNZQ (.seq (BinW.divmod wM wQ wC wD wE rF rR rK rT2) (nzP wD wZ rT4 rF rR)) (nzP wM wZ rT4 rF rR))
      σ (2 * ucost W 0 + 2) (fun τ => ∃ v', At (σ0.setv rT4 (decide (dd % q ≠ 0)).toNat) τ W v' ∧
        ∀ X, X ∉ [wC, wD, wE] → v' X = v X) := by
  have hU := one_le_ucost W 0
  have hL := lin_le_ucost W 0
  have hd := div_le W 0
  have hdW : dd < 2 ^ (W + 1) := by rw [pow_succ]; omega
  by_cases hq0 : q = 0
  · subst hq0
    have hv : σ.val rNZQ = 0 := by rw [h.val (by decide), hNZQ]; simp
    refine (Runs.ifrF hv ((opNz cap h (X := wM) (NZ := rT4) (by decide) (by decide) (by decide) hT4
      (by rw [hvm]; exact hdW) hcap).mono (show 41 * (W + 1) + 12 ≤ 2 * ucost W 0 + 1 by omega)
      (fun τ hτ => ⟨v, ?_, fun _ _ => rfl⟩))).cost (by omega)
    rw [Nat.mod_zero]; rw [hvm] at hτ; exact hτ
  · have hv : σ.val rNZQ ≠ 0 := by rw [h.val (by decide), hNZQ]; simp [hq0]
    refine (Runs.ifrT hv (Runs.seq' ((opDivmod cap h (A := wM) (B := wQ) (Q := wC) (M := wD) (E := wE) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hvm]; exact hdW) (by rw [hvq]; omega)
      (by rw [hvq]; exact hq) hcap).cost hd) (fun τ1 h1 => ?_) (c := 2 * ucost W 0 + 1) (c2 := ucost W 0)
      (by omega))).cost (by omega)
    set v1 := Function.update (Function.update (Function.update v wC (v wM / v wQ)) wD (v wM % v wQ)) wE 0 with hv1
    have hv1D : v1 wD = dd % q := by simp (config := {decide := true}) [hv1, hvm, hvq]
    refine ((opNz cap h1 (X := wD) (NZ := rT4) (by decide) (by decide) (by decide) hT4
      (by rw [hv1D]; exact lt_of_le_of_lt (Nat.mod_le _ _) hdW) hcap).cost (by omega)).post
      (fun τ hτ => ⟨v1, by rw [hv1D] at hτ; exact hτ, fun X hX => ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hX
    simp [hv1, Function.update_of_ne hX.1, Function.update_of_ne hX.2.1, Function.update_of_ne hX.2.2]

theorem ucost_mono (W : ℕ) {N N' : ℕ} (h : N ≤ N') : ucost W N ≤ ucost W N' := by
  unfold ucost; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

theorem forall_lt_succ_iff (P : ℕ → Prop) (k : ℕ) : (∀ i < k + 1, P i) ↔ (∀ i < k, P i) ∧ P k :=
  ⟨fun h => ⟨fun i hi => h i (by omega), h k (by omega)⟩, fun h i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h.1 i hi
    · exact h.2⟩

/-- The cap a cell needs. -/
def capC (N W : ℕ) : ℕ := (N + 2) * (2 * (W + 1) + 1) + 2 * N + 10

/-- Clear the flag `rFL` when the test flag `rT4` is set; `rT4 := 0`. -/
theorem flag_step (cap : ℕ) {σ0 τ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 τ W v) (fl : ℕ) (hFL : σ0.val rFL = fl)
    (hfl : fl ≤ 1) (t : Bool) (hT4 : σ0.val rT4 = t.toNat) (hcap : 2 ≤ cap) :
    Runs cap (.ifr rT4 (.seq (WMX.dec rT4) (.ifr rFL (WMX.dec rFL) WMX.skip)) WMX.skip) τ 5
      (fun ρ => At ((σ0.setv rT4 0).setv rFL (if t then 0 else fl)) ρ W v) := by
  cases t
  · have hv : τ.val rT4 = 0 := by rw [h.val (by decide), hT4]; rfl
    refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ) ?_)).cost (by omega)
    have e : (σ0.setv rT4 0).setv rFL (if false = true then 0 else fl) = σ0 := by
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs with h1 h2 <;> (try subst h1) <;> (try subst h2) <;> simp_all
    rw [e]; exact h
  · have hv : τ.val rT4 ≠ 0 := by rw [h.val (by decide), hT4]; simp
    refine (Runs.ifrT hv (Runs.seq' (opDecR cap h (r := rT4) (by decide) (by rw [hT4]; simp; omega))
      (fun τ1 h1 => ?_) (c := 4) (c2 := 2) (by omega))).cost (by omega)
    have h0 : σ0.val rT4 - 1 = 0 := by rw [hT4]; rfl
    rw [h0] at h1
    rcases Nat.eq_zero_or_pos fl with hf | hf
    · have hv' : τ1.val rFL = 0 := by rw [h1.val (by decide)]; simp (config := {decide := true}) [hFL, hf]
      refine (Runs.ifrF hv' (Runs.of (WXExec.skip cap τ1) ?_)).cost (by omega)
      have e : (σ0.setv rT4 0).setv rFL (if true = true then 0 else fl) = σ0.setv rT4 0 := by
        apply WState.eq <;> try rfl
        funext r; simp only [WState.setv_val, Function.update_apply]
        split_ifs with h1 h2 <;> (try subst h1) <;> (try subst h2) <;> simp_all
      rw [e]; exact h1
    · have hv' : τ1.val rFL ≠ 0 := by rw [h1.val (by decide)]; simp (config := {decide := true}) [hFL]; omega
      refine (Runs.ifrT hv' ((opDecR cap h1 (r := rFL) (by decide) (by
        simp (config := {decide := true}) [hFL]; omega)).post (fun ρ hρ => ?_))).cost (by omega)
      have e : (σ0.setv rT4 0).val rFL - 1 = 0 := by simp (config := {decide := true}) [hFL]; omega
      rw [e] at hρ
      rw [if_pos rfl]; exact hρ

/-- Clear the sign flag `rSGN`. -/
theorem sign_step (cap : ℕ) {σ0 τ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 τ W v) (s : Bool)
    (hS : σ0.val rSGN = s.toNat) (hcap : 2 ≤ cap) :
    Runs cap (.ifr rSGN (WMX.dec rSGN) WMX.skip) τ 2 (fun ρ => At (σ0.setv rSGN 0) ρ W v) := by
  cases s
  · have hv : τ.val rSGN = 0 := by rw [h.val (by decide), hS]; rfl
    refine (Runs.ifrF hv (Runs.of (WXExec.skip cap τ) ?_)).cost (by omega)
    have e : σ0.setv rSGN 0 = σ0 := by rw [show (0 : ℕ) = σ0.val rSGN by rw [hS]; rfl, wsetv_same]
    rw [e]; exact h
  · have hv : τ.val rSGN ≠ 0 := by rw [h.val (by decide), hS]; simp
    refine (Runs.ifrT hv ((opDecR cap h (r := rSGN) (by decide) (by rw [hS]; simp; omega)).post
      (fun ρ hρ => ?_))).cost (by omega)
    have e : σ0.val rSGN - 1 = 0 := by rw [hS]; rfl
    rw [e] at hρ; exact hρ

theorem flag_value (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    (if (decide (¬ P k)) = true then 0 else (decide (∀ i < k, P i)).toNat) = (decide (∀ i < k + 1, P i)).toNat := by
  simp only [forall_lt_succ_iff]
  by_cases hk : P k <;> simp [hk]

theorem test_step (cap : ℕ) {σB : MS} {W ℓ : ℕ} {pts : List (List ℤ)} {σl : List ℕ} {jS jP : List Bool}
    (hc : CellCtx σB W ℓ pts σl jS jP) {q : ℕ} {j : ℕ} (hj : j < pts.length)
    (hNZQ : σB.val rNZQ = (decide (q ≠ 0)).toNat) (keep : Str → ℕ) (hkq : keep wQ = q) (hσl : σl.length ≤ ℓ)
    (hσb : ∀ x ∈ σl, x < 2 ^ ℓ) (hub : ∀ z ∈ pts[j], z.natAbs < 2 ^ ℓ) (hq : q < 2 ^ ℓ) (hℓW : ℓ + 2 ≤ W)
    (hcap : capC (pts.length * ℓ + ℓ) W ≤ cap) (k : ℕ) (hk : k < σl.length) (τ : MS)
    (hI : TInv σB W q σl pts[j] (j * ℓ) keep k τ) :
    Runs cap testP (τ.setv rLS (σl.length - k - 1)) (12 * ucost W (pts.length * ℓ + ℓ))
      (fun ρ => TInv σB W q σl pts[j] (j * ℓ) keep (k + 1) ρ ∧ ρ.val rLS = σl.length - k - 1) := by
  obtain ⟨σ1, v1, h1, hISG1, hIXP1, hFL1, hSGN1, hT41, hfr1, hkeep1⟩ := hI
  set N := pts.length * ℓ + ℓ with hN
  set u := pts[j] with hu
  have hU := one_le_ucost W N
  have hL := lin_le_ucost W N
  unfold capC at hcap
  have hW1 : 1 ≤ W := by omega
  have h1' := h1.setv (r := rLS) (by decide) (σl.length - k - 1)
  set σ2 := σ1.setv rLS (σl.length - k - 1) with hσ2
  have hfr2 : SameExcept σB σ2 [] [rISG, rIXP, rFL, rLS] := SameExcept.trans hfr1 (sameExcept_setv σ1 (by simp) _)
  have hc2 : CellCtx σ2 W ℓ pts σl jS jP := hc.same hfr2
  have hkN : k < N := by omega
  have hjk : j * ℓ + k < pts.length * ℓ := by
    have : (j + 1) * ℓ ≤ pts.length * ℓ := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, one_mul] at this; omega
  have hpow : 2 ^ ℓ * 2 ≤ 2 ^ W := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hσk : σl[k] < 2 ^ ℓ := hσb _ (List.getElem_mem hk)
  have huk : (u.getD k 0).natAbs < 2 ^ ℓ := by
    rcases Nat.lt_or_ge k u.length with h' | h'
    · rw [List.getD_eq_getElem _ _ h']; exact hub _ (List.getElem_mem h')
    · rw [List.getD_eq_default _ _ h']; simp
  -- 1. `wK := encS σ_k`
  have hlS : (sgVals σl).length = σl.length := by simp [sgVals]
  have hi1 : σ2.val rISG = k := by simp (config := {decide := true}) [hσ2, hISG1]
  have hi2 : σ2.val rIXP = j * ℓ + k := by simp (config := {decide := true}) [hσ2, hIXP1]
  have hidx1 : σ2.val rISG < (sgVals σl).length := by rw [hi1, hlS]; exact hk
  have hg1 := getAt_le W N (σ2.val rISG) (by rw [hi1]; omega)
  have hQ1 : (σl.length + 1) * (2 * (W + 1) + 1) ≤ (N + 2) * (2 * (W + 1) + 1) := Nat.mul_le_mul_right _ (by omega)
  have hQ2 : (pts.length * ℓ + 1) * (2 * (W + 1) + 1) ≤ (N + 2) * (2 * (W + 1) + 1) := Nat.mul_le_mul_right _ (by omega)
  have hcW : 2 * (W + 1) + 1 ≤ cap := by
    have := Nat.le_mul_of_pos_left (2 * (W + 1) + 1) (show 0 < N + 2 by omega); omega
  have hxW : (u.getD k 0).natAbs < 2 ^ W := by omega
  have hyW : ((σl[k] : ℕ) : ℤ).natAbs < 2 ^ W := by simp; omega
  have hcG1 : ((sgVals σl).length + 1) * (2 * (W + 1) + 1) + 2 * σ2.val rISG ≤ cap := by rw [hlS, hi1]; omega
  refine Runs.seq' ((opGetAt cap h1' (A := sSG) (IX := rISG) (by decide) (by decide) (sgVals σl) jS hc2.sg hc2.sgh
    hidx1 hcG1).cost hg1) (fun τ3 h3 => ?_)
    (c2 := 12 * ucost W N - (ucost W N + 1)) (by omega)
  have hx1 : (sgVals σl)[σ2.val rISG] = encS ((σl[k] : ℕ) : ℤ) := by
    unfold sgVals; simp only [hi1]; rw [List.getElem_map]
  rw [hx1] at h3
  -- 2. `wSG := wK`
  refine Runs.seq' ((opCopy cap h3 (X := wSG) (Y := wK) (by decide) (by decide) (by decide) hcW).cost
    (show 41 * (W + 1) + 3 ≤ ucost W N by omega)) (fun τ4 h4 => ?_)
    (c2 := 12 * ucost W N - 2 * (ucost W N + 1)) (by omega)
  -- 3. `wK := encS u_k`
  have hlP : (pts.flatMap (ptVals ℓ)).length = pts.length * ℓ := by
    rw [List.length_flatMap]; simp [ptVals]
  have hidx2 : σ2.val rIXP < (pts.flatMap (ptVals ℓ)).length := by rw [hlP, hi2]; exact hjk
  have hg2 := getAt_le W N (σ2.val rIXP) (by rw [hi2]; omega)
  have hcG2 : ((pts.flatMap (ptVals ℓ)).length + 1) * (2 * (W + 1) + 1) + 2 * σ2.val rIXP ≤ cap := by
    rw [hlP, hi2]; omega
  refine Runs.seq' ((opGetAt cap h4 (A := sPT) (IX := rIXP) (by decide) (by decide) (pts.flatMap (ptVals ℓ)) jP hc2.pt
    hc2.pth hidx2 hcG2).cost hg2) (fun τ5 h5 => ?_)
    (c2 := 12 * ucost W N - 3 * (ucost W N + 1)) (by omega)
  have hx2 : (pts.flatMap (ptVals ℓ))[σ2.val rIXP] = encS (u.getD k 0) := by
    simp only [hi2]
    exact ptVals_get ℓ pts j k hj (by omega)
  rw [hx2] at h5
  -- 4. `wX1 := wK`
  refine Runs.seq' ((opCopy cap h5 (X := wX1) (Y := wK) (by decide) (by decide) (by decide) hcW).cost
    (show 41 * (W + 1) + 3 ≤ ucost W N by omega)) (fun τ6 h6 => ?_)
    (c2 := 12 * ucost W N - 4 * (ucost W N + 1)) (by omega)
  -- 5. `wX1 := u_k − σ_k`
  refine Runs.seq' ((opSsub cap h6 (X := wX1) (Y := wSG) (M := wM) (N := wN) (by decide) (by decide) (by decide)
    (by decide) (by decide) (x := u.getD k 0) (y := ((σl[k] : ℕ) : ℤ))
    (by simp (config := {decide := true})) (by simp (config := {decide := true}))
    hxW hyW (by
      have := Int.natAbs_sub_le (u.getD k 0) ((σl[k] : ℕ) : ℤ)
      simp only [Int.natAbs_natCast] at this ⊢; omega) hcW).cost (show 420 * W + 610 ≤ ucost W N by omega))
    (fun τ7 ⟨v7, h7, hv7X, hv7o⟩ => ?_) (c2 := 12 * ucost W N - 5 * (ucost W N + 1)) (by omega)
  set d := u.getD k 0 - ((σl[k] : ℕ) : ℤ) with hd
  have hdW : d.natAbs < 2 ^ W := by
    have := Int.natAbs_sub_le (u.getD k 0) ((σl[k] : ℕ) : ℤ)
    simp at this; rw [hd]; omega
  -- 6. split
  have h2SGN : σ2.val rSGN = 0 := by simp (config := {decide := true}) [hσ2, hSGN1]
  refine Runs.seq' ((opSplit cap h7 (X := wX1) (M := wM) (by decide) (by decide) (by decide) (S := rSGN) (by decide)
    h2SGN hv7X hdW hcW).cost (show 76 * W + 125 ≤ ucost W N by omega)) (fun τ8 h8 => ?_)
    (c2 := 12 * ucost W N - 6 * (ucost W N + 1)) (by omega)
  -- 7. the remainder test
  have hkeep7 : ∀ X ∈ keepW, v7 X = keep X := by
    intro X hX
    have hX' : X ∉ [wX1, wM, wN] := by
      simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> decide
    have hX2 : X ≠ wX1 ∧ X ≠ wSG ∧ X ≠ wK := by
      simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> decide
    rw [hv7o X hX']
    simp (config := {decide := true}) [Function.update_of_ne hX2.1, Function.update_of_ne hX2.2.1,
      Function.update_of_ne hX2.2.2, hkeep1 X hX]
  have hb := test_branch cap h8 q d.natAbs (by rw [show (σ2.setv rSGN (decide (d < 0)).toNat).val rNZQ = σ2.val rNZQ
      by simp (config := {decide := true}), hfr2.val (by decide), hNZQ]) (by simp (config := {decide := true}) [hσ2, hT41])
    (by simp (config := {decide := true}); rw [hkeep7 wQ (by decide), hkq]) (by simp) hdW
    (by rw [pow_succ]; omega) hcW
  refine Runs.seq' (hb.cost (show 2 * ucost W 0 + 2 ≤ 3 * ucost W N by have := ucost_mono W (Nat.zero_le N); omega))
    (fun τ9 ⟨v9, h9, hv9⟩ => ?_) (c2 := 12 * ucost W N - 6 * (ucost W N + 1) - (3 * ucost W N + 1)) (by omega)
  set σ9 := (σ2.setv rSGN (decide (d < 0)).toNat).setv rT4 (decide (d.natAbs % q ≠ 0)).toNat with hσ9
  have hTest : testOK q σl u k ↔ d.natAbs % q = 0 := by
    unfold testOK; rw [List.getD_eq_getElem _ _ hk]
  -- 8. the flag
  have hfl9 : σ9.val rFL = (decide (∀ i < k, testOK q σl u i)).toNat := by
    simp (config := {decide := true}) [hσ9, hσ2, hFL1]
  have hT9 : σ9.val rT4 = (decide (¬ testOK q σl u k)).toNat := by
    have : σ9.val rT4 = (decide (d.natAbs % q ≠ 0)).toNat := by simp (config := {decide := true}) [hσ9]
    rw [this]; simp only [ne_eq, hTest]
  have hstep8 := flag_step cap h9 _ hfl9 (by cases decide (∀ i < k, testOK q σl u i) <;> simp) _ hT9 (by omega)
  rw [flag_value (fun i => testOK q σl u i) k] at hstep8
  refine Runs.seq' hstep8 (fun τ11 h11 => ?_) (c2 := 12 * ucost W N - 6 * (ucost W N + 1) - (3 * ucost W N + 1) - 6)
    (by omega)
  -- 9. the sign flag
  set σ11 := (σ9.setv rT4 0).setv rFL (decide (∀ i < k + 1, testOK q σl u i)).toNat with hσ11
  have hstep9 := sign_step cap h11 (decide (d < 0)) (by simp (config := {decide := true}) [hσ11, hσ9]) (by omega)
  refine Runs.seq' hstep9 (fun τ12 h12 => ?_) (c2 := 7) (by omega)
  -- 10. step the indices
  refine Runs.seq' (opIncR cap h12 (r := rISG) (by decide) (by
    simp (config := {decide := true}) [hσ11, hσ9, hσ2, hISG1]; omega)) (fun τ13 h13 => ?_) (c2 := 3) (by omega)
  refine (opIncR cap h13 (r := rIXP) (by decide) (by
    simp (config := {decide := true}) [hσ11, hσ9, hσ2, hIXP1]; omega)).post (fun ρ hρ => ⟨⟨_, v9, hρ, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ?_⟩)
  · simp (config := {decide := true}) [hσ11, hσ9, hσ2, hISG1]
  · simp (config := {decide := true}) [hσ11, hσ9, hσ2, hIXP1]; ring
  · simp (config := {decide := true}) [hσ11]
  · simp (config := {decide := true})
  · simp (config := {decide := true}) [hσ11]
  · refine SameExcept.trans hfr2 ⟨fun x _ => ?_, fun r hr => ?_, ?_⟩
    · simp [hσ11, hσ9]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      by_cases h1 : r = rSGN
      · subst h1; simp (config := {decide := true}) [hσ11, hσ9, hσ2, hSGN1]
      · by_cases h2 : r = rT4
        · subst h2; simp (config := {decide := true}) [hσ11, hσ9, hσ2, hT41]
        · simp [hσ11, hσ9, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne hr.1,
            Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1]
    · simp [hσ11, hσ9]
  · intro X hX
    have hXk : X ∉ [wC, wD, wE] ∧ X ≠ wM := by
      simp only [keepW, List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl <;> decide
    rw [hv9 X hXk.1]
    simp only [Function.update_apply]
    have hXM : X ≠ wM := hXk.2
    simp [hXM, hkeep7 X hX]
  · rw [hρ.val (by decide)]; simp (config := {decide := true}) [hσ11, hσ9, hσ2]

end NearCubicGates.Close.Solve
