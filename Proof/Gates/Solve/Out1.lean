import Proof.Gates.Solve.OutVal

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
open NearCubicWires.RepairRepresentation (natWord)

/-- The output-phase registers (all `0` after the elimination). -/
abbrev rIX : Reg := 23
abbrev rBAD : Reg := 22
abbrev rSY : Reg := 15
abbrev rSD : Reg := 21
abbrev rLC : Reg := 29

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by simp [natWord]

theorem natWord_flag_len (b : ℕ) (hb : b ≤ 1) : (natWord b).length = 3 := by
  rw [natWord_len]
  interval_cases b <;> simp [natBitLength]

/-! ## The sign word -/

/-- `natWord (negB y D)` from the flags `rNZ = [y ≠ 0]`, `rSY = [y < 0]`, `rSD = [D < 0]`; clears `rNZ`. -/
def signP : WMX NS NR :=
  .ifr rNZ (.seq (WMX.dec rNZ) (.ifr rSY (.ifr rSD (CounterMachine.emitL sOUT (natWord 1))
    (CounterMachine.emitL sOUT (natWord 0))) (.ifr rSD (CounterMachine.emitL sOUT (natWord 0))
    (CounterMachine.emitL sOUT (natWord 1))))) (CounterMachine.emitL sOUT (natWord 0))

section Ops
variable (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ}

theorem opSign (h : At σ0 σ W v) (y D : ℤ) (hNZ : σ0.val rNZ = (decide (y ≠ 0)).toNat)
    (hSY : σ0.val rSY = (decide (y < 0)).toNat) (hSD : σ0.val rSD = (decide (D < 0)).toNat)
    (hO : σ0.sh sOUT = (σ0.st sOUT).length) (hcap : 1 ≤ cap) :
    Runs cap signP σ 20 (fun τ => At (appO (σ0.setv rNZ 0) (natWord (negB y D))) τ W v) := by
  have l0 := natWord_flag_len 0 (by omega)
  have l1 := natWord_flag_len 1 (by omega)
  by_cases hy : y = 0
  · have e0 : σ0.setv rNZ 0 = σ0 := by
      rw [show (0 : ℕ) = σ0.val rNZ by rw [hNZ]; simp [hy], wsetv_same]
    have hn : negB y D = 0 := by unfold negB; rw [if_neg (by intro ⟨h1, _⟩; exact h1 hy)]
    rw [e0, hn]
    refine (Runs.ifrF (by rw [h.val (by decide), hNZ]; simp [hy]) (opEmit cap h _ hO)).cost (by omega)
  · have h1 : σ.val rNZ ≠ 0 := by rw [h.val (by decide), hNZ]; simp [hy]
    refine (Runs.ifrT (c := 19) h1 ?_)
    refine Runs.seq' (opDecR cap h (r := rNZ) (by decide) (by rw [hNZ]; simp [hy]; omega)) (fun τ1 h1 => ?_)
      (c2 := 17) (by omega)
    have e1 : σ0.setv rNZ (σ0.val rNZ - 1) = σ0.setv rNZ 0 := by rw [hNZ]; simp [hy]
    rw [e1] at h1
    have hO1 : (σ0.setv rNZ 0).sh sOUT = ((σ0.setv rNZ 0).st sOUT).length := by simpa using hO
    have hSY1 : τ1.val rSY = (decide (y < 0)).toNat := by
      rw [h1.val (by decide), WState.setv_val, Function.update_of_ne (by decide), hSY]
    have hSD1 : τ1.val rSD = (decide (D < 0)).toNat := by
      rw [h1.val (by decide), WState.setv_val, Function.update_of_ne (by decide), hSD]
    by_cases hyn : y < 0
    · refine (Runs.ifrT (c := 16) (by rw [hSY1]; simp [hyn]) ?_).cost (by omega)
      by_cases hDn : D < 0
      · have hn : negB y D = 1 := by unfold negB; rw [if_pos ⟨hy, iff_of_true hyn hDn⟩]
        rw [hn]
        exact (Runs.ifrT (by rw [hSD1]; simp [hDn]) (opEmit cap h1 _ hO1)).cost (by omega)
      · have hn : negB y D = 0 := by
          unfold negB; rw [if_neg (by intro ⟨_, h2⟩; exact hDn (h2.mp hyn))]
        rw [hn]
        exact (Runs.ifrF (by rw [hSD1]; simp [hDn]) (opEmit cap h1 _ hO1)).cost (by omega)
    · refine (Runs.ifrF (c := 16) (by rw [hSY1]; simp [hyn]) ?_).cost (by omega)
      by_cases hDn : D < 0
      · have hn : negB y D = 0 := by
          unfold negB; rw [if_neg (by intro ⟨_, h2⟩; exact hyn (h2.mpr hDn))]
        rw [hn]
        exact (Runs.ifrT (by rw [hSD1]; simp [hDn]) (opEmit cap h1 _ hO1)).cost (by omega)
      · have hn : negB y D = 1 := by unfold negB; rw [if_pos ⟨hy, iff_of_false hyn hDn⟩]
        rw [hn]
        exact (Runs.ifrF (by rw [hSD1]; simp [hDn]) (opEmit cap h1 _ hO1)).cost (by omega)

/-- Clear a flag (`0` or `1`). -/
theorem opClearF (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) (hb : σ0.val r ≤ 1) (hcap : 1 ≤ cap) :
    Runs cap (.ifr r (WMX.dec r) WMX.skip) σ 2 (fun τ => At (σ0.setv r 0) τ W v) := by
  rcases Nat.eq_zero_or_pos (σ0.val r) with h0 | h0
  · have e : σ0.setv r 0 = σ0 := by rw [← h0, wsetv_same]
    rw [e]
    exact (Runs.ifrF (by rw [h.val hr, h0]) (Runs.of (WXExec.skip cap σ) h)).cost (by omega)
  · have e : σ0.setv r (σ0.val r - 1) = σ0.setv r 0 := by congr 1; omega
    have := opDecR cap h hr (by omega)
    rw [e] at this
    exact Runs.ifrT (by rw [h.val hr]; omega) this

end Ops

/-! ## Part A: the values -/

def entA : WMX NS NR :=
  .seq (getAt sMAT wK rCA rCW rIX rK2) (.seq (SInt.split wK wX1 rSY rF rR) (.seq (BinW.copy wG1 wAV rF rR)
  (.seq (BinW.copy wG2 wX1 rF rR) (.seq euclidP (.seq (BinW.divmod wX1 wG1 wQ wD wE rF rR rK rT2)
  (.seq (BinW.divmod wAV wG1 wB wD wE rF rR rK rT2) (nzP wX1 wZ rNZ rF rR)))))))

def entACost (W N : ℕ) : ℕ :=
  ucost W N + 1 + (ucost W N + 1 + (ucost W N + 1 + (ucost W N + 1 + (euclidCost W + 1 + (ucost W N + 1 +
    (ucost W N + 1 + ucost W N))))))

/-- The record stream of the final matrix. -/
structure MatCtx (σ0 : MS) (W R C : ℕ) (a : ℕ → ℕ → ℤ) (junk : List Bool) : Prop where
  mat : σ0.st sMAT = recStream ((matV R C a).map (binary (W + 1))) ++ junk
  math : σ0.sh sMAT = 0

theorem entA_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {R C : ℕ} {a : ℕ → ℕ → ℤ}
    {junk : List Bool} (hc : MatCtx σ0 W R C a junk) (hcap : capE (R * C) W ≤ cap) {i n : ℕ} (hi : i < R)
    (hn : n < C) (hIX : σ0.val rIX = i * C + n) (hSY : σ0.val rSY = 0) (hNZ : σ0.val rNZ = 0) (hLE : σ0.val rLE = 0)
    (hR2 : σ0.val rR2 = 2 * (W + 1) + 1) {D : ℤ} (hD0 : D ≠ 0) (hDlt : D.natAbs < 2 ^ W) (hDA : v wAV = D.natAbs)
    (hylt : (a i n).natAbs < 2 ^ W) :
    Runs cap entA σ (entACost W (R * C)) (fun τ => ∃ σ1 v1, At σ1 τ W v1 ∧
      v1 wQ = (a i n).natAbs / Nat.gcd D.natAbs (a i n).natAbs ∧
      v1 wB = D.natAbs / Nat.gcd D.natAbs (a i n).natAbs ∧
      σ1.val rNZ = (decide (a i n ≠ 0)).toNat ∧ σ1.val rSY = (decide (a i n < 0)).toNat ∧ σ1.val rLE = 0 ∧
      SameExcept σ0 σ1 [] [rNZ, rSY, rLE] ∧ v1 wAV = v wAV ∧ v1 wZ = v wZ) := by
  obtain ⟨cap1, cap2, -⟩ := cap_facts hcap
  set N := R * C with hN
  set U := ucost W N with hUd
  have hUL : 500 * W + 700 ≤ U := lin_le_ucost W N
  have hdv : BinW.divCost (W + 1) ≤ U := div_le W N
  set y := a i n with hyd
  have hidx : i * C + n < N := idx_lt hi hn
  have hpw : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
  -- 1. `wK := encS y`
  refine Runs.seq ((opGetAt cap h (A := sMAT) (IX := rIX) (by decide) (by decide) (matV R C a) junk hc.mat hc.math
    (by rw [matV_length, hIX]; exact hidx) (by rw [matV_length, hIX, ← hN]; omega)).cost
    (by rw [hIX]; exact getAt_le W N _ hidx)) (fun τ1 h1 => ?_)
  have hx1 : (matV R C a)[σ0.val rIX]'(by rw [matV_length, hIX]; exact hidx) = encS y := by
    simp only [hIX]; exact matV_get R C a hi hn
  rw [hx1] at h1
  -- 2. `wX1 := |y|`, `rSY := [y < 0]`
  refine Runs.seq ((opSplit cap h1 (X := wK) (M := wX1) (by decide) (by decide) (by decide) (S := rSY) (by decide)
    hSY (x := y) (by simp) hylt cap2).cost (show 76 * W + 125 ≤ U by omega)) (fun τ2 h2 => ?_)
  set σ2 := σ0.setv rSY (decide (y < 0)).toNat with hσ2
  -- 3. `wG1 := |D|`, `wG2 := |y|`
  refine Runs.seq ((opCopy cap h2 (X := wG1) (Y := wAV) (by decide) (by decide) (by decide) cap2).cost
    (show 41 * (W + 1) + 3 ≤ U by omega)) (fun τ3 h3 => ?_)
  refine Runs.seq ((opCopy cap h3 (X := wG2) (Y := wX1) (by decide) (by decide) (by decide) cap2).cost
    (show 41 * (W + 1) + 3 ≤ U by omega)) (fun τ4 h4 => ?_)
  set v4 := Function.update (Function.update (Function.update (Function.update v wK (encS y)) wX1 y.natAbs) wG1
    (Function.update (Function.update v wK (encS y)) wX1 y.natAbs wAV)) wG2
    (Function.update (Function.update (Function.update v wK (encS y)) wX1 y.natAbs) wG1
      (Function.update (Function.update v wK (encS y)) wX1 y.natAbs wAV) wX1) with hv4
  have e4G1 : v4 wG1 = D.natAbs := by simp (config := {decide := true}) [Function.update_apply, hv4, hDA]
  have e4G2 : v4 wG2 = y.natAbs := by simp (config := {decide := true}) [Function.update_apply, hv4]
  have e4X1 : v4 wX1 = y.natAbs := by simp (config := {decide := true}) [Function.update_apply, hv4]
  have e4AV : v4 wAV = D.natAbs := by simp (config := {decide := true}) [Function.update_apply, hv4, hDA]
  have e4Z : v4 wZ = v wZ := by simp (config := {decide := true}) [Function.update_apply, hv4]
  -- 4. Euclid
  refine Runs.seq (euclid_spec cap h4 (by simp (config := {decide := true}) [Function.update_apply, hσ2, hNZ]) (by simp (config := {decide := true}) [Function.update_apply, hσ2, hLE]) (by simp (config := {decide := true}) [Function.update_apply, hσ2, hR2])
    (by rw [e4G1]; exact hDlt) (by rw [e4G2]; exact hylt) cap2) (fun τ5 ⟨σ5, v5, h5, h5NZ, h5LE, hfr5, h5G, ho5⟩ => ?_)
  have hDpos : 0 < D.natAbs := Int.natAbs_pos.mpr hD0
  set g := Nat.gcd D.natAbs y.natAbs with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  have hgD : g ≤ D.natAbs := Nat.gcd_le_left _ hDpos
  have e5G1 : v5 wG1 = g := by rw [h5G, e4G1, e4G2]
  have e5X1 : v5 wX1 = y.natAbs := by rw [ho5 wX1 (by decide), e4X1]
  have e5AV : v5 wAV = D.natAbs := by rw [ho5 wAV (by decide), e4AV]
  have e5Z : v5 wZ = v wZ := by rw [ho5 wZ (by decide), e4Z]
  -- 5. `wQ := |y| / g`, `wB := |D| / g`
  refine Runs.seq ((opDivmod cap h5 (A := wX1) (B := wG1) (Q := wQ) (M := wD) (E := wE) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [e5X1]; omega) (by rw [e5G1]; exact hg0)
    (by rw [e5G1]; omega) cap2).cost hdv) (fun τ6 h6 => ?_)
  refine Runs.seq ((opDivmod cap h6 (A := wAV) (B := wG1) (Q := wB) (M := wD) (E := wE) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by simp (config := {decide := true}) [Function.update_apply, e5AV]; omega)
    (by simp (config := {decide := true}) [Function.update_apply, e5G1]; exact hg0)
    (by simp (config := {decide := true}) [Function.update_apply, e5G1]; omega) cap2).cost hdv) (fun τ7 h7 => ?_)
  -- 6. `rNZ := [y ≠ 0]`
  refine (opNz cap h7 (X := wX1) (NZ := rNZ) (by decide) (by decide) (by decide) h5NZ (by simp (config := {decide := true}) [Function.update_apply, e5X1]; omega)
    cap2).cost (show 41 * (W + 1) + 12 ≤ U by omega) |>.post (fun τ8 h8 => ⟨_, _, h8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp (config := {decide := true}) [Function.update_apply, e5X1, e5G1]
  · simp (config := {decide := true}) [Function.update_apply, e5AV, e5G1]
  · simp (config := {decide := true}) [Function.update_apply, e5X1]
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), hfr5.val (by decide)]; simp (config := {decide := true}) [Function.update_apply, hσ2]
  · simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]; exact h5LE
  · exact SameExcept.trans (sameExcept_setv σ0 (by simp) _) (SameExcept.trans (hfr5.weaken (by simp) (by simp))
      (sameExcept_setv σ5 (by simp) _))
  · simp (config := {decide := true}) [Function.update_apply, e5AV, hDA]
  · simp (config := {decide := true}) [Function.update_apply, e5Z]

/-! ## Part B: the words -/

def entB : WMX NS NR :=
  .seq signP (.seq (.ifr rSY (WMX.dec rSY) WMX.skip) (.seq (printW 1) (.seq (printW 2) (addR rCC rIX rTa))))

def entBCost (W C : ℕ) : ℕ := 20 + 1 + (2 + 1 + (printCost W + 1 + (printCost W + 1 + (18 * C + 3))))

theorem entB_spec (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) (y D : ℤ) {C : ℕ}
    (hNZ : σ0.val rNZ = (decide (y ≠ 0)).toNat) (hSY : σ0.val rSY = (decide (y < 0)).toNat)
    (hSD : σ0.val rSD = (decide (D < 0)).toNat) (hO : σ0.sh sOUT = (σ0.st sOUT).length)
    (hWL : σ0.val rWL = W + 1) (hR2 : σ0.val rR2 = 2 * (W + 1) + 1) (hCC : σ0.val rCC = C)
    (hQ : v wQ = y.natAbs / Nat.gcd D.natAbs y.natAbs) (hB : v wB = D.natAbs / Nat.gcd D.natAbs y.natAbs)
    (hQlt : v wQ < 2 ^ (W + 1)) (hBlt : v wB < 2 ^ (W + 1)) (hcap : 8 * (W + 1) + 8 + σ0.val rIX + C ≤ cap) :
    Runs cap entB σ (entBCost W C) (fun τ => ∃ σ1, At σ1 τ W v ∧ σ1.st sOUT = σ0.st sOUT ++ entW y D ∧
      σ1.sh sOUT = (σ1.st sOUT).length ∧ σ1.val rNZ = 0 ∧ σ1.val rSY = 0 ∧ σ1.val rIX = σ0.val rIX + C ∧
      SameExcept σ0 σ1 [sOUT] [rNZ, rSY, rIX]) := by
  refine Runs.seq (opSign cap h y D hNZ hSY hSD hO (by omega)) (fun τ1 h1 => ?_)
  set σa := appO (σ0.setv rNZ 0) (natWord (negB y D)) with hσa
  refine Runs.seq (opClearF cap h1 (r := rSY) (by decide) (by rw [hσa, appO_val, WState.setv_val, Function.update_of_ne (by decide), hSY]; exact Bool.toNat_le _)
    (by omega)) (fun τ2 h2 => ?_)
  set σb := σa.setv rSY 0 with hσb
  have hOb : σb.sh sOUT = (σb.st sOUT).length := by simp [hσb, hσa, appO]
  refine Runs.seq (opPrint cap h2 1 (Or.inl rfl) hOb (by simp (config := {decide := true}) [Function.update_apply, hσb, hσa, appO_val, hWL])
    (by simp (config := {decide := true}) [Function.update_apply, hσb, hσa, appO_val, hR2]) hQlt (by omega)) (fun τ3 h3 => ?_)
  rw [show pP 1 = wQ from rfl] at h3
  set σc := appO σb (natWord (v wQ)) with hσc
  refine Runs.seq (opPrint cap h3 2 (Or.inr rfl) (appO_sh _ _) (by simp (config := {decide := true}) [Function.update_apply, hσc, hσb, hσa, appO_val, hWL])
    (by simp (config := {decide := true}) [Function.update_apply, hσc, hσb, hσa, appO_val, hR2]) hBlt (by omega)) (fun τ4 h4 => ?_)
  rw [show pP 2 = wB from rfl] at h4
  set σd := appO σc (natWord (v wB)) with hσd
  have hdv : ∀ r, r ≠ rNZ → r ≠ rSY → σd.val r = σ0.val r := fun r h1 h2 => by
    simp [hσd, hσc, hσb, hσa, appO_val, Function.update_of_ne h1, Function.update_of_ne h2]
  refine (opAddR cap h4 (A := rCC) (B := rIX) (by decide) (by decide) (by decide)
    (by rw [hdv _ (by decide) (by decide), hdv _ (by decide) (by decide), hCC]; omega)).cost
    (by rw [hdv _ (by decide) (by decide), hCC]) |>.post (fun τ5 h5 => ⟨_, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp only [WState.setv_st, hσd, hσc, hσb, hσa, appO_st, entW, hQ, hB, List.append_assoc]
  · simp only [WState.setv_sh, WState.setv_st]; exact appO_sh _ _
  · simp (config := {decide := true}) [Function.update_apply, hσd, hσc, hσb, hσa, appO_val]
  · simp (config := {decide := true}) [Function.update_apply, hσd, hσc, hσb, hσa, appO_val]
  · rw [WState.setv_val, Function.update_self, hdv _ (by decide) (by decide), hdv _ (by decide) (by decide), hCC]
  · refine SameExcept.trans ?_ (sameExcept_setv σd (by simp) _)
    refine SameExcept.trans ?_ ((appO_same σc _).weaken (by simp) (by simp))
    refine SameExcept.trans ?_ ((appO_same σb _).weaken (by simp) (by simp))
    refine SameExcept.trans ?_ (sameExcept_setv σa (by simp) _)
    exact SameExcept.trans (sameExcept_setv σ0 (by simp) _) ((appO_same _ _).weaken (by simp) (by simp))

end NearCubicGates.Close.Solve
