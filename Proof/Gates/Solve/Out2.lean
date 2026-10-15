import Proof.Gates.Solve.Out1

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

theorem encS_eq_zero_iff (z : ℤ) : encS z = 0 ↔ z = 0 :=
  ⟨fun h => encS_inj (h.trans encS_zero.symm), fun h => by rw [h]; rfl⟩

def chkBody : WMX NS NR :=
  .seq (getAt sMAT wK rCA rCW rIX rK2) (.seq (nzP wK wZ rNZ rF rR)
    (.seq (.ifr rNZ (.seq (WMX.dec rNZ) (.ifr rBAD WMX.skip (WMX.inc rBAD))) WMX.skip) (addR rCC rIX rTa)))

def chkP : WMX NS NR := .seq (addR rNN rIX rTa) (.seq (addR rMM rLC rTa) (.whr rLC (.seq (WMX.dec rLC) chkBody)))

/-- The check-loop invariant after `k` rows. -/
def KInv (σA : MS) (W C n : ℕ) (a : ℕ → ℕ → ℤ) (v : Str → ℕ) (k : ℕ) (τ : MS) : Prop :=
  ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rIX = k * C + n ∧ σ1.val rBAD = (decide (∃ i < k, a i n ≠ 0)).toNat ∧
    σ1.val rNZ = 0 ∧ SameExcept σA σ1 [] [rIX, rBAD, rNZ, rLC] ∧ ∀ X, X ≠ wK → v1 X = v X

theorem MatCtx.same {σ0 σ1 : MS} {W R C : ℕ} {a : ℕ → ℕ → ℤ} {junk : List Bool} (h : MatCtx σ0 W R C a junk)
    {S : List Str} {Rg : List Reg} (hfr : SameExcept σ0 σ1 S Rg) (hS : sMAT ∉ S) : MatCtx σ1 W R C a junk :=
  ⟨by rw [hfr.st hS, h.mat], by rw [hfr.sh hS, h.math]⟩

theorem chk_step (cap : ℕ) {σA : MS} {W R C m n : ℕ} {a : ℕ → ℕ → ℤ} {junk : List Bool} {v : Str → ℕ}
    (hc : MatCtx σA W R C a junk) (hcap : capE (R * C) W ≤ cap) (hmR : m ≤ R) (hn : n < C) (hCN : C ≤ R * C + 2)
    (hCC : σA.val rCC = C) (hbd : ∀ i < R, (a i n).natAbs < 2 ^ W) (k : ℕ) (hk : k < m) (τ : MS)
    (hI : KInv σA W C n a v k τ) :
    Runs cap chkBody (τ.setv rLC (m - k - 1)) (4 * ucost W (R * C))
      (fun ρ => KInv σA W C n a v (k + 1) ρ ∧ ρ.val rLC = m - k - 1) := by
  obtain ⟨σ1, v1, h1, hIX, hBAD, hNZ, hfr, ho⟩ := hI
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  set N := R * C with hN
  set U := ucost W N with hUd
  have hUL : 500 * W + 700 ≤ U := lin_le_ucost W N
  have hUN : 4000 * (N + 2) ≤ U := ucost_geN W N
  have h1' := h1.setv (r := rLC) (by decide) (m - k - 1)
  set σ2 := σ1.setv rLC (m - k - 1) with hσ2
  have hfr2 : SameExcept σA σ2 [] [rIX, rBAD, rNZ, rLC] := hfr.trans (sameExcept_setv σ1 (by simp) _)
  have hc2 : MatCtx σ2 W R C a junk := hc.same hfr2 (by simp)
  have hIX2 : σ2.val rIX = k * C + n := by simp (config := {decide := true}) [hσ2, hIX]
  have hidx : k * C + n < N := idx_lt (by omega) hn
  have hkR : k < R := by omega
  refine Runs.seq' ((opGetAt cap h1' (A := sMAT) (IX := rIX) (by decide) (by decide) (matV R C a) junk hc2.mat
    hc2.math (by rw [matV_length, hIX2]; exact hidx) (by rw [matV_length, hIX2, ← hN]; omega)).cost
    (show _ ≤ U by rw [hIX2]; exact getAt_le W N _ hidx)) (fun τ3 h3 => ?_) (c2 := 3 * U - 1) (by omega)
  have hx : (matV R C a)[σ2.val rIX]'(by rw [matV_length, hIX2]; exact hidx) = encS (a k n) := by
    simp only [hIX2]; exact matV_get R C a hkR hn
  rw [hx] at h3
  refine Runs.seq' ((opNz cap h3 (X := wK) (NZ := rNZ) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ2, hNZ]) (by simp; exact encS_lt (hbd k hkR)) cap2).cost
    (show 41 * (W + 1) + 12 ≤ U by omega)) (fun τ4 h4 => ?_) (c2 := 2 * U - 2) (by omega)
  set v3 := Function.update v1 wK (encS (a k n)) with hv3
  have hz : (decide (v3 wK ≠ 0)).toNat = (decide (a k n ≠ 0)).toNat := by
    simp only [hv3, Function.update_self]
    by_cases h0 : a k n = 0 <;> simp [h0, encS_eq_zero_iff]
  rw [hz] at h4
  set σ4 := σ2.setv rNZ (decide (a k n ≠ 0)).toNat with hσ4
  have hBAD4 : σ4.val rBAD = (decide (∃ i < k, a i n ≠ 0)).toNat := by
    simp (config := {decide := true}) [hσ4, hσ2, hBAD]
  -- the flag
  have hflag : Runs cap (.ifr rNZ (.seq (WMX.dec rNZ) (.ifr rBAD WMX.skip (WMX.inc rBAD))) WMX.skip) τ4 8
      (fun τ5 => ∃ σ5, At σ5 τ5 W v3 ∧ σ5.val rNZ = 0 ∧
        σ5.val rBAD = (decide (∃ i < k + 1, a i n ≠ 0)).toNat ∧ SameExcept σ4 σ5 [] [rNZ, rBAD]) := by
    by_cases h0 : a k n = 0
    · have e : (decide (a k n ≠ 0)).toNat = 0 := by simp [h0]
      refine (Runs.ifrF (by rw [h4.val (by decide)]; simp [hσ4, h0]) (Runs.of (WXExec.skip cap τ4)
        ⟨σ4, h4, by simp [hσ4, h0], ?_, SameExcept.refl _ _ _⟩)).cost (by omega)
      rw [hBAD4]; congr 2
      apply propext; constructor
      · rintro ⟨i, hi, hne⟩; exact ⟨i, by omega, hne⟩
      · rintro ⟨i, hi, hne⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact ⟨i, hi, hne⟩
        · subst hi; exact absurd h0 hne
    · have e : (decide (a k n ≠ 0)).toNat = 1 := by simp [h0]
      have hex : (decide (∃ i < k + 1, a i n ≠ 0)).toNat = 1 := by
        simp only [Bool.toNat_eq_one, decide_eq_true_eq]; exact ⟨k, by omega, h0⟩
      refine (Runs.ifrT (c := 7) (by rw [h4.val (by decide)]; simp [hσ4, h0]) ?_)
      refine Runs.seq' (opDecR cap h4 (r := rNZ) (by decide) (by simp [hσ4, h0]; omega)) (fun τ5 h5 => ?_)
        (c2 := 5) (by omega)
      set σ5 := σ4.setv rNZ (σ4.val rNZ - 1) with hσ5
      have hNZ5 : σ5.val rNZ = 0 := by simp [hσ5, hσ4, h0]
      have hfr5 : SameExcept σ4 σ5 [] [rNZ, rBAD] := sameExcept_setv σ4 (by simp) _
      by_cases hb : ∃ i < k, a i n ≠ 0
      · have hb1 : σ5.val rBAD = 1 := by
          simp (config := {decide := true}) [hσ5, hσ4, hσ2, hBAD, hb]
        refine (Runs.ifrT (by rw [h5.val (by decide), hb1]; omega) (Runs.of (WXExec.skip cap τ5)
          ⟨σ5, h5, hNZ5, by rw [hb1, hex], hfr5⟩)).cost (by omega)
      · have hb0 : σ5.val rBAD = 0 := by
          simp (config := {decide := true}) [hσ5, hσ4, hσ2, hBAD, hb]
        refine (Runs.ifrF (by rw [h5.val (by decide), hb0]) ((opIncR cap h5 (r := rBAD) (by decide)
          (by rw [hb0]; omega)).post (fun τ6 h6 => ⟨_, h6, ?_, ?_, hfr5.trans (sameExcept_setv σ5 (by simp) _)⟩))).cost
          (by omega)
        · simp (config := {decide := true}) [hNZ5]
        · rw [WState.setv_val, Function.update_self, hb0, hex]
  refine Runs.seq' (hflag.cost (show 8 ≤ 8 by omega)) (fun τ5 ⟨σ5, h5, hNZ5, hBAD5, hfr5⟩ => ?_) (c2 := U)
    (by omega)
  have hcapA : k * C + n + C ≤ cap := by nlinarith
  have hv5 : ∀ r, r ≠ rNZ → r ≠ rBAD → σ5.val r = σ2.val r := fun r h1 h2 => by
    rw [hfr5.val (by simp [h1, h2])]; simp [hσ4, Function.update_of_ne h1]
  refine ((opAddR cap h5 (A := rCC) (B := rIX) (by decide) (by decide) (by decide)
    (by rw [hv5 _ (by decide) (by decide), hv5 _ (by decide) (by decide), hIX2, hfr2.val (by decide), hCC]; omega)).cost
    (by rw [hv5 _ (by decide) (by decide), hfr2.val (by decide), hCC]; omega)).post
    (fun τ6 h6 => ⟨⟨_, v3, h6, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  · simp only [WState.setv_val, Function.update_self]
    rw [hv5 _ (by decide) (by decide), hv5 _ (by decide) (by decide), hIX2, hfr2.val (by decide), hCC]; ring
  · simp (config := {decide := true}) [hBAD5]
  · simp (config := {decide := true}) [hNZ5]
  · refine SameExcept.trans hfr2 (SameExcept.trans ?_ (SameExcept.trans (hfr5.weaken (by simp) (by simp))
      (sameExcept_setv σ5 (by simp) _)))
    exact sameExcept_setv σ2 (by simp) _
  · intro X hX; simp [hv3, Function.update_of_ne hX, ho X hX]
  · rw [h6.val (by decide)]
    simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), hv5 _ (by decide) (by decide)]
    simp [hσ2]

def chkCost (W N m : ℕ) : ℕ := 18 * (N + 2) + 3 + 1 + (18 * (N + 2) + 3 + 1 + (m * (4 * ucost W N + 4) + 1))

theorem chk_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C m n : ℕ} {a : ℕ → ℕ → ℤ}
    {junk : List Bool} (hc : MatCtx σ0 W R C a junk) (hcap : capE (R * C) W ≤ cap) (hmR : m ≤ R) (hn : n < C)
    (hCN : C ≤ R * C + 2) (hCC : σ0.val rCC = C) (hNN : σ0.val rNN = n) (hMM : σ0.val rMM = m)
    (hIX : σ0.val rIX = 0) (hBAD : σ0.val rBAD = 0) (hNZ : σ0.val rNZ = 0) (hLC : σ0.val rLC = 0)
    (hbd : ∀ i < R, (a i n).natAbs < 2 ^ W) :
    Runs cap chkP σ (chkCost W (R * C) m) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧ σ1.val rIX = m * C + n ∧
      σ1.val rBAD = (decide (∃ i < m, a i n ≠ 0)).toNat ∧ σ1.val rNZ = 0 ∧ σ1.val rLC = 0 ∧
      SameExcept σ0 σ1 [] [rIX, rBAD, rNZ, rLC] ∧ ∀ X, X ≠ wK → v1 X = v X) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  have hmN : m ≤ R * C := le_trans hmR (Nat.le_mul_of_pos_right _ (by omega))
  have hnN : n ≤ R * C + 2 := by omega
  refine Runs.seq' ((opAddR cap h (A := rNN) (B := rIX) (by decide) (by decide) (by decide)
    (by rw [hIX, hNN]; nlinarith)).cost (show 18 * σ0.val rNN + 3 ≤ 18 * (R * C + 2) + 3 by rw [hNN]; omega))
    (fun τ1 h1 => ?_) (c2 := 18 * (R * C + 2) + 3 + 1 + (m * (4 * ucost W (R * C) + 4) + 1)) (by unfold chkCost; omega)
  rw [hIX, hNN, Nat.zero_add] at h1
  set σ1 := σ0.setv rIX n with hσ1
  refine Runs.seq' ((opAddR cap h1 (A := rMM) (B := rLC) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [hσ1, hLC, hMM]; nlinarith)).cost
    (show 18 * σ1.val rMM + 3 ≤ 18 * (R * C + 2) + 3 by simp (config := {decide := true}) [hσ1, hMM]; omega))
    (fun τ2 h2 => ?_) (c2 := m * (4 * ucost W (R * C) + 4) + 1) (by omega)
  set σ2 := σ1.setv rLC (σ1.val rLC + σ1.val rMM) with hσ2
  have hfr2 : SameExcept σ0 σ2 [] [rIX, rBAD, rNZ, rLC] :=
    (sameExcept_setv σ0 (by simp) _).trans (sameExcept_setv σ1 (by simp) _)
  have hc2 : MatCtx σ2 W R C a junk := hc.same hfr2 (by simp)
  have hCC2 : σ2.val rCC = C := by rw [hfr2.val (by decide), hCC]
  have hloop := Runs.count (cap := cap) (K := rLC) (body := chkBody) (4 * ucost W (R * C)) m
    (KInv σ2 W C n a v) (by omega) (fun k hk τ hτ _ => chk_step cap hc2 hcap hmR hn hCN hCC2 hbd k hk τ hτ) τ2
    ⟨σ2, v, h2, by simp (config := {decide := true}) [hσ2, hσ1], by simp (config := {decide := true}) [hσ2, hσ1, hBAD],
      by simp (config := {decide := true}) [hσ2, hσ1, hNZ], SameExcept.refl _ _ _, fun _ _ => rfl⟩
    (by rw [h2.val (by decide)]; simp (config := {decide := true}) [hσ2, hσ1, hLC, hMM])
  refine hloop.post (fun τ ⟨⟨σ3, v3, h3, h3IX, h3BAD, h3NZ, hfr3, ho⟩, hK⟩ =>
    ⟨σ3, v3, h3, h3IX, h3BAD, h3NZ, ?_, hfr2.trans hfr3, ho⟩)
  rw [← h3.val (by decide)]; exact hK

end NearCubicGates.Close.Solve
