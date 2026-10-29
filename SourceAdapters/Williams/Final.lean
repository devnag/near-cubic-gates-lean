import SourceAdapters.Williams.Assembly

/-!
# W06 + W07: the time bound and `Williams14_Corollary4_4` from the published leaf

Absorb source time, simulation, loader, output conversion, cleanup, floors/log bases, and a larger
onset into `C*N²*(Nat.log 2 N)^e`. The input/output conversions fit `O(N*k+N² log N)`; increasing the fixed log
exponent is harmless. W07: assemble `MultitapeMultiplier` (`Statement.lean:1121–1132`) and prove
`Williams14_Corollary4_4` (`Statement.lean:1141`) from `RectangularProductLeaf` (`PublishedStatements/Williams.lean`).
`imp:batch` gives the near-quadratic bound, and `sec:prelim` fixes base-two algorithmic logarithms.
-/

namespace NearCubicGates.Adapters.Williams.Final

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams NearCubicGates.Adapters.Williams.Load
open NearCubicGates.Adapters.Williams.Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

set_option autoImplicit false

/-! ## W06: logarithms -/

/-- `log₂ N` (real) is at most `2·⌊log₂ N⌋` once `N ≥ 2`. -/
theorem logb_le_two_log (N : ℕ) (hN : 2 ≤ N) : Real.logb 2 N ≤ 2 * (Nat.log 2 N : ℝ) := by
  have hL : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h1 : Real.logb 2 N ≤ Real.logb 2 ((2 : ℝ) ^ (Nat.log 2 N + 1)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hlt.le)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h1
  push_cast at h1
  have : (1 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL
  linarith

/-- The leaf's real time bound as a natural one with `⌊log₂ N⌋`. -/
theorem time_nat (C e N t : ℕ) (hN : 2 ≤ N) (ht : (t : ℝ) ≤ C * (N : ℝ) ^ 2 * Real.logb 2 N ^ e) :
    t ≤ C * 2 ^ e * N ^ 2 * Nat.log 2 N ^ e := by
  have h0 : 0 ≤ Real.logb 2 (N : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N))
  have h2 : Real.logb 2 (N : ℝ) ^ e ≤ (2 * (Nat.log 2 N : ℝ)) ^ e := pow_le_pow_left₀ h0 (logb_le_two_log N hN) e
  have h3 : (t : ℝ) ≤ C * (N : ℝ) ^ 2 * (2 * (Nat.log 2 N : ℝ)) ^ e :=
    le_trans ht (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 : ((C * 2 ^ e * N ^ 2 * Nat.log 2 N ^ e : ℕ) : ℝ) = C * (N : ℝ) ^ 2 * (2 * (Nat.log 2 N : ℝ)) ^ e := by
    push_cast; ring
  exact_mod_cast h3.trans h4.symm.le

/-! ## W06: the three costs -/

theorem loaderCost_le (x k : ℕ) (hk : 1 ≤ k) : loaderCost x k ≤ (2000 + 20 * x) * (k ^ 10) ^ 2 := by
  have hN1 : 1 ≤ k ^ 10 := Nat.one_le_pow _ _ hk
  have hW := natBitLength_le hN1
  have h2W := two_pow_natBitLength_le hN1
  have hkN : k ≤ k ^ 10 := Nat.le_self_pow (by norm_num) k
  unfold loaderCost Load.toUnaryCost Load.roundCost Load.powDiffCost
  generalize natBitLength (k ^ 10) = W at *
  generalize 2 ^ W = P at *
  generalize k ^ 10 = N at *
  have f1 : W * P ≤ 2 * N ^ 2 := by nlinarith
  have f2 : k * N ≤ N ^ 2 := by nlinarith
  have f3 : k * N * x ≤ N ^ 2 * x := Nat.mul_le_mul_right _ f2
  have f4 : N ≤ N ^ 2 := by nlinarith
  have f5 : x ≤ N ^ 2 * x := by nlinarith
  have f6 : W ≤ N ^ 2 := by nlinarith
  have f7 : k ≤ N ^ 2 := by nlinarith
  nlinarith

theorem simCost_le (M : MultitapeTM) (t : ℕ) :
    simCost M t ≤ 6 * (M.extraSymbols + 4) * t + 2 * (M.extraSymbols + 4) + 2 := by
  unfold simCost
  have : (3 * (M.extraSymbols + 4) - 1) * t ≤ 3 * (M.extraSymbols + 4) * t := Nat.mul_le_mul_right _ (by omega)
  have h6 : 6 * (M.extraSymbols + 4) * t = 2 * (3 * (M.extraSymbols + 4) * t) := by ring
  omega

/-- The constant of the assembled bound. -/
def finalConst (x C e : ℕ) : ℕ := 3000 + 30 * x + 6 * (x + 4) * C * 2 ^ e

/-- **W06.** The assembled machine's step count is at most `finalConst · N² · ⌊log₂ N⌋^(e+1)` once `N ≥ 2`. -/
theorem total_le (M : MultitapeTM) (k C e t : ℕ) (hN : 2 ≤ k ^ 10)
    (ht : t ≤ C * 2 ^ e * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ e) :
    loaderCost M.extraSymbols k + 1 + (simCost M t + 1 +
        (k ^ 10 * k ^ 10 * (Format.entryCost M.extraSymbols (natBitLength (k ^ 10)) + 2) + 1)) ≤
      finalConst M.extraSymbols C e * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ (e + 1) := by
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hN
    · exact h
  have hL : 1 ≤ Nat.log 2 (k ^ 10) := Nat.log_pos (by norm_num) hN
  have hl1 := loaderCost_le M.extraSymbols k hk
  have hs1 := simCost_le M t
  unfold Format.entryCost Format.digitCost natBitLength finalConst
  generalize Nat.log 2 (k ^ 10) = L at *
  generalize k ^ 10 = N at *
  generalize M.extraSymbols = x at *
  generalize loaderCost x k = LC at *
  generalize simCost M t = SC at *
  have hLe : L ^ e ≤ L ^ (e + 1) := Nat.pow_le_pow_right hL (by omega)
  have hL1 : 1 ≤ L ^ (e + 1) := Nat.one_le_pow _ _ hL
  have hLL : L ≤ L ^ (e + 1) := by simpa using Nat.pow_le_pow_right hL (show 1 ≤ e + 1 by omega)
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have g1 : N ^ 2 ≤ N ^ 2 * L ^ (e + 1) := by nlinarith
  have g2 : N ^ 2 * L ^ e ≤ N ^ 2 * L ^ (e + 1) := Nat.mul_le_mul_left _ hLe
  have g3 : N ^ 2 * L ≤ N ^ 2 * L ^ (e + 1) := Nat.mul_le_mul_left _ hLL
  have g4 : C * 2 ^ e * N ^ 2 * L ^ e ≤ C * 2 ^ e * (N ^ 2 * L ^ (e + 1)) := by
    rw [Nat.mul_assoc (C * 2 ^ e)]; exact Nat.mul_le_mul_left _ g2
  have g5 : N * N = N ^ 2 := by ring
  rw [g5]
  nlinarith

/-! ## W07: the multiplier -/

/-- The renamed input bank is the release's `inputTapes`. -/
theorem input_eq (M : MultitapeTM) (k : ℕ) (A : Fin (k ^ 10) → Fin k → Bool) (B : Fin k → Fin (k ^ 10) → Bool) :
    (fun j => Close.CheckedPCPP.coldBank (start0 M (RepairRepresentation.natWord (k ^ 10) ++
        WilliamsLoaderForms.rowMajorBitMatrix A) (WilliamsLoaderForms.rowMajorBitMatrix B)) ((swapT M).symm j)) =
      (Bindings.Williams14.inputTapes (t := tapeCountOf M) (k ^ 10) A B) := by
  funext j
  rw [cold_rename]
  rfl

/-- **W07 (input 5).** Williams' published Corollary 4.4 / C.2, read in the textbook multitape model
(`RectangularProductLeaf`), implies the release's `Williams14_Corollary4_4`. -/
theorem williams14_of_leaf (h : RectangularProductLeaf) : Bindings.Williams14.Williams14_Corollary4_4 := by
  obtain ⟨M, inTape, outTape, C, e, N₀, hM⟩ := leaf_at_powers h
  refine ⟨max N₀ 2, finalConst M.extraSymbols C e, e + 1, ⟨?_⟩⟩
  exact {
    tapeCount := tapeCountOf M
    stateCount := (program M inTape outTape).size
    threeTapes := by unfold tapeCountOf; omega
    machine := TapeRenaming.machine (swapT M) (program M inTape outTape).compile
    outputTape := ⟨3, by unfold tapeCountOf; omega⟩
    outputFreshLeft := by simp
    outputFreshRight := by simp
    multiplies := by
      intro k A B hN
      have hN0 : N₀ ≤ k ^ 10 := le_trans (le_max_left _ _) hN
      have hN2 : 2 ≤ k ^ 10 := le_trans (le_max_right _ _) hN
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at hN2
        · exact h0
      obtain ⟨t, cf, hrun, hf, ht, hout⟩ := hM k hN0 A B
      have ht' := time_nat C e (k ^ 10) t hN2 ht
      obtain ⟨τ, hexec, hOUT⟩ := program_exec M inTape outTape k hk A B t cf hrun hf hout
        (loaderCap k + natBitLength (k ^ 10) + 1) (by omega) (by omega)
      obtain ⟨r, hr, hrt⟩ := run_cold hexec (fun _ => rfl) (fun _ => rfl) rfl
      have hrn := TapeRenaming.run_rename (swapT M) _ _ _ r hr
      have hcfg : TapeRenaming.config (swapT M) (initialConfiguration (program M inTape outTape).compile
          (Close.CheckedPCPP.coldBank (start0 M (RepairRepresentation.natWord (k ^ 10) ++
            WilliamsLoaderForms.rowMajorBitMatrix A) (WilliamsLoaderForms.rowMajorBitMatrix B)))) =
          initialConfiguration (TapeRenaming.machine (swapT M) (program M inTape outTape).compile)
            (Bindings.Williams14.inputTapes (k ^ 10) A B) := by
        apply configuration_ext
        · rfl
        · rfl
        · exact input_eq M k A B
      rw [hcfg] at hrn
      have hbound := total_le M k C e t hN2 ht'
      refine ⟨TapeRenaming.receipt (swapT M) r, ?_, ?_⟩
      · have hmore := run_moreFuel _ _ (finalConst M.extraSymbols C e * (k ^ 10) ^ 2 * Nat.log 2 (k ^ 10) ^ (e + 1) -
          (loaderCost M.extraSymbols k + 1 + (simCost M t + 1 + (k ^ 10 * k ^ 10 *
            (Format.entryCost M.extraSymbols (natBitLength (k ^ 10)) + 2) + 1)))) _ _ hrn
        rwa [Nat.add_sub_of_le hbound] at hmore
      · have h3 : (swapT M).symm ⟨3, by unfold tapeCountOf; omega⟩ = NearCubicWires.WireExponent3_5.FinalPass.Tm.sTape (nr := 16) (sOUT M) := by
          simp [swapT, Equiv.swap_apply_def, NearCubicWires.WireExponent3_5.FinalPass.Tm.sTape, sOUT, Fin.ext_iff]
        show r.final.tapes ((swapT M).symm ⟨3, _⟩) = _
        rw [h3, hrt, hOUT] }

end NearCubicGates.Adapters.Williams.Final
