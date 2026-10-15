import Proof.Wire_3_5.UnionMachineRoundDiv
import Proof.CaseAnalysis.FinalWordFunctionDock

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round
open NearCubicWires.WireExponent3_5.Cost

/-! ## Admissible answers are small -/

section Small
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- **The masked mean is a probability.** -/
theorem truth_mem (req : PrimRequest) : 0 ≤ I.truth req ∧ I.truth req ≤ 1 := by
  unfold PrimitiveInputs.truth maskedMean
  have hterm : ∀ e x, (0 : ℝ) ≤ (if I.mask req e x then (1 : ℝ) else 0) *
      ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ∧
      (if I.mask req e x then (1 : ℝ) else 0) * ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 := by
    intro e x
    have h1 : ∀ i, (0 : ℝ) ≤ (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ∧
        (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 := by
      intro i; split_ifs <;> norm_num
    have hp0 : (0 : ℝ) ≤ ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) :=
      Finset.prod_nonneg fun i _ => (h1 i).1
    have hp1 : ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) ≤ 1 :=
      Finset.prod_le_one (fun i _ => (h1 i).1) (fun i _ => (h1 i).2)
    split_ifs <;> constructor <;> nlinarith
  set S := ∑ e, ∑ x, (if I.mask req e x then (1 : ℝ) else 0) *
      ∏ i, (if req.mode.eval (req.circuits i) x then (1 : ℝ) else 0) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => Finset.sum_nonneg fun x _ => (hterm e x).1
  have hS1 : S ≤ (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by
    calc S ≤ ∑ _e : I.Seed req.mode req.n, ∑ _x : BitInput req.n, (1 : ℝ) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun x _ => (hterm e x).2
      _ = (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by
          simp [Finset.card_univ, BitInput, Fintype.card_fun, Fintype.card_bool]
  have hden : (0 : ℝ) ≤ (Fintype.card (I.Seed req.mode req.n) : ℝ) * 2 ^ req.n := by positivity
  refine ⟨div_nonneg hS0 hden, ?_⟩
  rcases hden.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · exact (div_le_one hpos).mpr hS1

/-- **An admissible call's answer is small**: `|num| < 4·den`. -/
theorem value_small (P : FusedPrimitive I) (req : PrimRequest) (h : I.Call req) :
    (P.value req).num.natAbs < 4 * (P.value req).den := by
  have he := P.error req h
  have ht := truth_mem I req
  have hD : (req.n : ℝ) ^ (-(I.D : ℝ)) ≤ 1 := by
    rcases Nat.eq_zero_or_pos req.n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.zero_rpow (by have := I.D_pos; norm_cast; omega)]; norm_num
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpos) (by have := I.D_pos; simp)
  have hv : |((P.value req : ℚ) : ℝ)| < 4 := by
    rw [abs_lt]; constructor <;> linarith [(abs_le.mp he).1, (abs_le.mp he).2]
  have hq : |P.value req| < 4 := by exact_mod_cast hv
  set v := P.value req with hvdef
  have hd : (0 : ℚ) < v.den := by exact_mod_cast v.den_pos
  have hnum : (v.num.natAbs : ℚ) = |v| * v.den := by
    have e1 : (v.num : ℚ) = v * v.den := by rw [Rat.mul_den_eq_num]
    have e2 : (v.num.natAbs : ℚ) = |(v.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e2, e1, abs_mul, abs_of_pos hd]
  have : (v.num.natAbs : ℚ) < 4 * v.den := by rw [hnum]; nlinarith [abs_nonneg v]
  exact_mod_cast this

end Small

/-! ## The call and the rounding, docked -/

section CallRound
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The rewound estimator. -/
noncomputable abbrev estRW := P.estimator.reset

/-- The rounding program's compiled machine. -/
abbrev roundM : Machine (2 + 2 + 14) roundP.toProg.size := roundP.toProg.compile

/-- **The call-and-round machine** at the slot maps `es` (estimator) and `rs` (rounding bank). -/
noncomputable def callRoundM {N : ℕ} (es : Fin (estRW P).program.tapeCount → Fin N) (rs : Fin (2 + 2 + 14) → Fin N) :
    Machine N ((estRW P).program.stateCount + roundP.toProg.size) :=
  Composition.machine (RecoveryFocus.machine es (estRW P).program.machine) (RecoveryFocus.machine rs roundM)

/-- **One primitive call and its rounded answer, at any layout.** The estimator's slots carry the framed request
and blanks, with heads `0`; the rounding bank's slots (but its stream `0`, which is the estimator's output tape)
carry the rounding program's entry bank. After the step, the rounding bank holds a state `τ` with
`MP − MN = ⌊v·2^p⌋` and `PC = p`; every tape outside the two slot images is untouched. -/
theorem callRound_step {N : ℕ} (es : Fin (estRW P).program.tapeCount → Fin N) (rs : Fin (2 + 2 + 14) → Fin N)
    (hes : Function.Injective es) (hrs : Function.Injective rs)
    (hshare : rs 0 = es (estRW P).program.outputTape)
    (hdisj : ∀ j k, es j = rs k → k = 0)
    (req : {req : PrimRequest // I.Call req}) (p cap : ℕ) (c : Bool) (H : Fin N → ℕ) (A : Fin N → List Bool)
    (hH : ∀ j, H (es j) = 0) (hin : A (es (C10WordFunctionDock.inSlot (estRW P).program)) = frame req.1.word)
    (hblank : ∀ j, j ≠ C10WordFunctionDock.inSlot (estRW P).program → A (es j) = [])
    (hRH : ∀ k, k ≠ 0 → H (rs k) = (wenc cap (parseIn (P.value req.1) p c)).H k)
    (hRA : ∀ k, k ≠ 0 → A (rs k) = (wenc cap (parseIn (P.value req.1) p c)).A k)
    (hcap : 4 * lb (P.value req.1) + 8 * 2 ^ p + 20 ≤ cap) :
    ∃ (H' : Fin N → ℕ) (A' : Fin N → List Bool),
      Step (callRoundM P es rs) (2 * B.callBudget req.1.n + 2 + 1 + roundCost (lb (P.value req.1)) p) H A H' A' ∧
      (∃ τ : RS, ((τ.val 10 : ℤ) - τ.val 11 = ⌊P.value req.1 * 2 ^ p⌋) ∧ τ.val 9 = p ∧ τ.cell = c ∧
        ∀ k, H' (rs k) = (wenc cap τ).H k ∧ A' (rs k) = (wenc cap τ).A k) ∧
      (∀ i, (∀ j, es j ≠ i) → (∀ k, rs k ≠ i) → H' i = H i ∧ A' i = A i) := by
  set v := P.value req.1 with hv
  -- the call
  obtain ⟨tout, hout, hcall⟩ := C10WordFunctionDock.rewound_dock (estRW P) es hes H A req hH hin hblank
  set H1 := dockH es H (fun _ => 0) with hH1
  set A1 := install es A tout with hA1
  -- the rounding
  obtain ⟨τ, hτ, hval, hpc, hcell⟩ := round_spec cap v p c (value_small I P req.1 req.2) hcap
  have hstep := (WExec.exec cap hτ).step
  have hR0H : H1 (rs 0) = (wenc cap (parseIn v p c)).H 0 := by
    rw [hshare, hH1, dockH_slot es hes]
    show 0 = (wenc cap (parseIn v p c)).H (sTape (0 : Fin 3))
    rw [wenc_H_s]; simp [parseIn, st3]
  have hR0A : A1 (rs 0) = (wenc cap (parseIn v p c)).A 0 := by
    rw [hshare, hA1, install_slot es hes, hout]
    show ratWord v = (wenc cap (parseIn v p c)).A (sTape (0 : Fin 3))
    rw [wenc_A_s]; simp [parseIn, st3]
  have hRHk : ∀ k, H1 (rs k) = (wenc cap (parseIn v p c)).H k := by
    intro k
    by_cases hk : k = 0
    · subst hk; exact hR0H
    · rw [hH1, dockH_other es H _ (rs k) (fun j hj => hk (hdisj j k hj))]; exact hRH k hk
  have hRAk : ∀ k, A1 (rs k) = (wenc cap (parseIn v p c)).A k := by
    intro k
    by_cases hk : k = 0
    · subst hk; exact hR0A
    · rw [hA1, install_other es A tout (rs k) (fun j hj => hk (hdisj j k hj))]; exact hRA k hk
  have hdock := hstep.dock rs hrs H1 A1 hRHk hRAk
  refine ⟨dockH rs H1 (wenc cap τ).H, install rs A1 (wenc cap τ).A, Step.seq hcall hdock, ⟨τ, hval, hpc, hcell,
    fun k => ⟨dockH_slot rs hrs _ _ k, install_slot rs hrs _ _ k⟩⟩, ?_⟩
  intro i hi1 hi2
  refine ⟨?_, ?_⟩
  · rw [dockH_other rs H1 _ i hi2, hH1, dockH_other es H _ i hi1]
  · rw [install_other rs A1 _ i hi2, hA1, install_other es A tout i hi1]

end CallRound

end NearCubicWires.WireExponent3_5.UnionMachine
