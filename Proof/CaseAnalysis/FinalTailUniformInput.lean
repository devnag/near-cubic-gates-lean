import Proof.CaseAnalysis.FinalTailUniformSlots

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformInput

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorThresholdDecision
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Parked (ph : Phase) (b : ℕ) (est : CompetitorValidity.Estimate)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool) : Prop where
  recWord : A (scratch ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est 1 1
  recH : H (scratch ph) = 0
  cmpH : ∀ j, H (cmpSlots j) = 0
  cmpA : ∀ j, A (cmpSlots j) = []
  nAH : ∀ j, H (normSlots j) = 0
  nAA : ∀ j, A (normSlots j) = []
  nBH : ∀ j, H (normSlotsB j) = 0
  nBA : ∀ j, A (normSlotsB j) = []
  wH : ∀ j, H (wordSlots j) = 0
  wA : ∀ j, A (wordSlots j) = []
  widthH : ∀ j, H (widthSlot ph j) = 0
  widthBase : A (widthSlot ph 0) = List.replicate b true
  widthWide : A (widthSlot ph 1) = List.replicate (w b) true
  privateH : ∀ j, H (privateSlot ph j) = 0
  privateA : ∀ j, A (privateSlot ph j) = []

theorem Parked.dimension_heads {ph : Phase} {b : ℕ} {est : CompetitorValidity.Estimate}
    {H : Fin bank → ℕ} {A : Fin bank → List Bool} (hp : Parked ph b est H A) :
    ∀ j, H (dimensionSlots ph j) = 0 := by
  intro j
  fin_cases j <;> first | exact hp.widthH _ | exact hp.cmpH _ | exact hp.privateH _

theorem Parked.dimension_tapes {ph : Phase} {b : ℕ} {est : CompetitorValidity.Estimate}
    {H : Fin bank → ℕ} {A : Fin bank → List Bool} (hp : Parked ph b est H A) :
    ∀ j, A (dimensionSlots ph j) = CompetitorDimensions.input (w b) j := by
  intro j
  fin_cases j <;> first | exact hp.widthWide | exact hp.cmpA _ | exact hp.privateA _

theorem dimension_private_later (ph : Phase) (j : Fin 29) (hj : 17 ≤ j.val) :
    ∀ i, dimensionSlots ph i ≠ privateSlot ph j := by
  have hprivate (l : Fin 29) (hl : l.val < 17) : privateSlot ph l ≠ privateSlot ph j := by
    intro h
    have := congrArg Fin.val (privateSlot_injective ph h)
    omega
  have hwidth : widthSlot ph 1 ≠ privateSlot ph j := by
    have := (widthSlot_range ph 1).2
    have := (privateSlot_range ph j).1
    intro h
    have := congrArg Fin.val h
    omega
  have hcmp : cmpSlots 6 ≠ privateSlot ph j := by
    have := (privateSlot_range ph j).2
    intro h
    have he := congrArg Fin.val h
    change 227 = (privateSlot ph j).val at he
    omega
  intro i
  fin_cases i <;> first | exact hwidth | exact hcmp | exact hprivate _ (by decide)

theorem constants_input_heads (ph : Phase) (lower : Bool) (H : Fin bank → ℕ)
    (hc : ∀ j, H (cmpSlots j) = 0) (hw : ∀ j, H (widthSlot ph j) = 0)
    (hp : ∀ j, H (privateSlot ph j) = 0) :
    ∀ j, H (constantSlots ph lower j) = 0 := by
  intro j
  fin_cases j <;> first | exact hc _ | exact hw _ | exact hp _

theorem constants_input_tapes (ph : Phase) (lower : Bool) (b : ℕ) (A : Fin bank → List Bool)
    (hc : A (cmpSlots 6) = List.replicate (w2 b) true)
    (hw : A (widthSlot ph 1) = List.replicate (w b) true)
    (hp : ∀ j, 17 ≤ j.val → A (privateSlot ph j) = [])
    (hz : ∀ j, j.val ≠ 6 → j.val ≠ (posSlot lower).val → j.val ≠ (negSlot lower).val →
      j.val ≠ (denSlot lower).val → A (cmpSlots j) = []) :
    ∀ j, A (constantSlots ph lower j) = CompetitorThresholdConstants.input (w b) j := by
  intro j
  fin_cases j
  all_goals first
    | exact hc
    | exact hw
    | exact hp _ (by decide)
    | exact hz _ (by cases lower <;> decide) (by cases lower <;> decide)
        (by cases lower <;> decide) (by cases lower <;> decide)

def CoreOutside (ph : Phase) (i : Fin bank) : Prop :=
  (∀ j, cmpSlots j ≠ i) ∧ (∀ j, normSlots j ≠ i) ∧
  (∀ j, normSlotsB j ≠ i) ∧ (∀ j, wordSlots j ≠ i) ∧ i ≠ scratch ph

def Outside (ph : Phase) (i : Fin bank) : Prop :=
  CoreOutside ph i ∧ ∀ j, privateSlot ph j ≠ i

theorem coreOutside_low (ph : Phase) (i : Fin bank) (hi : i.val < 218) : CoreOutside ph i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j h
    have := congrArg Fin.val h
    simp only [cmpSlots] at this
    omega
  · intro j h
    have := congrArg Fin.val h
    simp only [normSlots] at this
    omega
  · intro j h
    have := congrArg Fin.val h
    simp only [normSlotsB] at this
    omega
  · intro j h
    have := congrArg Fin.val h
    simp only [wordSlots] at this
    omega
  · intro h
    have := congrArg Fin.val h
    cases ph <;> simp only [scratch] at this <;> omega

theorem width_ne_high (ph : Phase) (j : Fin 2) (i : Fin bank) (hi : 218 ≤ i.val) :
    widthSlot ph j ≠ i := by
  have := (widthSlot_range ph j).2
  intro h
  have := congrArg Fin.val h
  omega

theorem private_ne_high (ph : Phase) (j : Fin 29) (i : Fin bank) (hi : 218 ≤ i.val) :
    privateSlot ph j ≠ i := by
  have := (privateSlot_range ph j).2
  intro h
  have := congrArg Fin.val h
  omega

theorem dimension_other_high (ph : Phase) (i : Fin bank) (hi : 218 ≤ i.val)
    (hc : cmpSlots 6 ≠ i) : ∀ j, dimensionSlots ph j ≠ i :=
  dimensionSlots_other ph i (width_ne_high ph 1 i hi) hc (fun j => private_ne_high ph j i hi)

theorem constant_other_high (ph : Phase) (lower : Bool) (i : Fin bank) (hi : 218 ≤ i.val)
    (hc : cmpSlots 6 ≠ i) (hn : cmpSlots (qnumSlot lower) ≠ i)
    (hz : cmpSlots (zeroSlot lower) ≠ i) (hd : cmpSlots (qdenSlot lower) ≠ i) :
    ∀ j, constantSlots ph lower j ≠ i :=
  constantSlots_other ph lower i (width_ne_high ph 1 i hi) hc hn hz hd
    (fun j => private_ne_high ph j i hi)

noncomputable def program (ph : Phase) (lower : Bool) (k : ℕ) (q : ℚ) :=
  Composition.machine
    (Composition.machine (dimensionProgram ph) (C10TailRecordFeedUniform.recordProgram ph lower))
    (constantProgram ph lower k q)

def budget (b k : ℕ) :=
  (CompetitorDimensions.budget (w b) + 1 + C10TailRecordFeedUniform.budget b) + 1 +
    CompetitorThresholdConstants.budget (w b) k

theorem input_run (ph : Phase) (lower : Bool) (k : ℕ) (q : ℚ) (b : ℕ)
    (est : CompetitorValidity.Estimate) (hv : est.Valid b)
    (hk : k ≤ w b) (hqn : numerator q < 2^k) (hqd : q.den < 2^k)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool) (hp : Parked ph b est H A) :
    ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step (program ph lower k q) (budget b k) H A H' A' ∧
      (∀ j, H' (cmpSlots j) = 0) ∧
      (∀ j, A' (cmpSlots j) = input lower (w b) est.positive est.negative est.denominator q j) ∧
      A' (scratch ph) = A (scratch ph) ∧
      (∀ j, A' (widthSlot ph j) = A (widthSlot ph j)) ∧
      (∀ i, Outside ph i → A' i = A i) ∧
      (∀ i, CoreOutside ph i → H' i = H i) := by
  classical
  have hsge : 218 ≤ (scratch ph).val := by cases ph <;> decide
  obtain ⟨dout, hdim, hd0, hd15⟩ := dimension_stage ph b H A hp.dimension_heads hp.dimension_tapes
  let Ad := install (dimensionSlots ph) A dout
  have hDhigh (i : Fin bank) (hi : 218 ≤ i.val) (hc : cmpSlots 6 ≠ i) : Ad i = A i :=
    install_other _ _ _ i (dimension_other_high ph i hi hc)
  have hDdriver : Ad (cmpSlots 6) = List.replicate (w2 b) true :=
    (install_slot (dimensionSlots ph) (dimensionSlots_injective ph) A dout 15).trans hd15
  have hDwidth1 : Ad (widthSlot ph 1) = A (widthSlot ph 1) :=
    ((install_slot (dimensionSlots ph) (dimensionSlots_injective ph) A dout 0).trans hd0).trans hp.widthWide.symm
  have hDwidth0 : Ad (widthSlot ph 0) = A (widthSlot ph 0) := by
    exact install_other _ _ _ _ (by cases ph <;> decide)
  have hDprivate (j : Fin 29) (hj : 17 ≤ j.val) : Ad (privateSlot ph j) = A (privateSlot ph j) := by
    exact install_other _ _ _ _ (dimension_private_later ph j hj)
  have hDrec : Ad (scratch ph) = A (scratch ph) := hDhigh _ hsge (cmp_ne_scratch ph 6)
  have hready : C10TailRecordFeedUniform.Ready ph b est H Ad := by
    refine ⟨hDrec.trans hp.recWord, hp.recH, hDdriver, hp.cmpH, ?_, hp.nAH, ?_, hp.nBH, ?_, hp.wH, ?_⟩
    · intro j hj
      exact (hDhigh _ (by dsimp [cmpSlots]; omega) (by
        intro h
        exact hj (congrArg Fin.val (cmpSlots_injective h)).symm)).trans (hp.cmpA j)
    · intro j
      exact (hDhigh _ (by dsimp [normSlots]; omega) (cmp_ne_normA 6 j)).trans (hp.nAA j)
    · intro j
      exact (hDhigh _ (by dsimp [normSlotsB]; omega) (cmp_ne_normB 6 j)).trans (hp.nBA j)
    · intro j
      exact (hDhigh _ (by dsimp [wordSlots]; omega) (cmp_ne_word 6 j)).trans (hp.wA j)
  obtain ⟨Hf, Af, hfeed, hFdriver, hFpos, hFneg, hFden, hFheads, hFblank, hFrec, hFframe, hFheadframe⟩ :=
    C10TailRecordFeedUniform.record_run ph lower b est hv H Ad hready
  have hFlow (i : Fin bank) (hi : i.val < 218) : Af i = Ad i := by
    obtain ⟨hc, ha, hb, hw, hs⟩ := coreOutside_low ph i hi
    exact hFframe i hc ha hb hw hs
  have hHflow (i : Fin bank) (hi : i.val < 218) : Hf i = H i := by
    obtain ⟨hc, ha, hb, hw, hs⟩ := coreOutside_low ph i hi
    exact hFheadframe i hc ha hb hw hs
  have hFwidth (j : Fin 2) : Af (widthSlot ph j) = A (widthSlot ph j) := by
    rw [hFlow _ (by have := (widthSlot_range ph j).2; omega)]
    fin_cases j
    · exact hDwidth0
    · exact hDwidth1
  have hFwidthH (j : Fin 2) : Hf (widthSlot ph j) = 0 :=
    (hHflow _ (by have := (widthSlot_range ph j).2; omega)).trans (hp.widthH j)
  have hFprivate (j : Fin 29) (hj : 17 ≤ j.val) : Af (privateSlot ph j) = [] :=
    ((hFlow _ (by have := (privateSlot_range ph j).2; omega)).trans (hDprivate j hj)).trans (hp.privateA j)
  have hFprivateH (j : Fin 29) : Hf (privateSlot ph j) = 0 :=
    (hHflow _ (by have := (privateSlot_range ph j).2; omega)).trans (hp.privateH j)
  have hconH := constants_input_heads ph lower Hf hFheads hFwidthH hFprivateH
  have hconA := constants_input_tapes ph lower b Af hFdriver ((hFwidth 1).trans hp.widthWide) hFprivate hFblank
  obtain ⟨cout, hconst, hc0, hc1, hc3, hc8, hc13⟩ := constant_stage ph lower b k q hk hqn hqd Hf Af hconH hconA
  let Ac := install (constantSlots ph lower) Af cout
  have hChigh (i : Fin bank) (hi : 218 ≤ i.val) (h0 : cmpSlots 6 ≠ i)
      (hn : cmpSlots (qnumSlot lower) ≠ i) (hz : cmpSlots (zeroSlot lower) ≠ i)
      (hd : cmpSlots (qdenSlot lower) ≠ i) : Ac i = Af i :=
    install_other _ _ _ _ (constant_other_high ph lower i hi h0 hn hz hd)
  have hCwidth1 : Ac (widthSlot ph 1) = A (widthSlot ph 1) :=
    ((install_slot (constantSlots ph lower) (constantSlots_injective ph lower) Af cout 1).trans hc1).trans hp.widthWide.symm
  have hCwidth0 : Ac (widthSlot ph 0) = A (widthSlot ph 0) := by
    exact (install_other _ _ _ _ (by cases ph <;> cases lower <;> decide)).trans (hFwidth 0)
  refine ⟨Hf, Ac, hdim.seq hfeed |>.seq hconst, hFheads, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rcases Nat.lt_or_ge j.val 7 with hj | hj
    · rcases C10TailFeed.slot_cover lower j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [input_pos, hChigh _ (by dsimp [cmpSlots]; omega)
          (by cases lower <;> decide) (by cases lower <;> decide)
          (by cases lower <;> decide) (by cases lower <;> decide)]
        exact hFpos
      · rw [input_neg, hChigh _ (by dsimp [cmpSlots]; omega)
          (by cases lower <;> decide) (by cases lower <;> decide)
          (by cases lower <;> decide) (by cases lower <;> decide)]
        exact hFneg
      · rw [input_qnum]
        exact (install_slot (constantSlots ph lower) (constantSlots_injective ph lower) Af cout 3).trans hc3
      · rw [input_zero]
        exact (install_slot (constantSlots ph lower) (constantSlots_injective ph lower) Af cout 8).trans hc8
      · rw [input_den, hChigh _ (by dsimp [cmpSlots]; omega)
          (by cases lower <;> decide) (by cases lower <;> decide)
          (by cases lower <;> decide) (by cases lower <;> decide)]
        exact hFden
      · rw [input_qden]
        exact (install_slot (constantSlots ph lower) (constantSlots_injective ph lower) Af cout 13).trans hc13
      · rw [input_driver]
        exact (install_slot (constantSlots ph lower) (constantSlots_injective ph lower) Af cout 0).trans hc0
    · rw [input_blank lower (w b) est.positive est.negative est.denominator q j hj]
      have hneq (l : Fin 67) (hl : l.val < 7) : cmpSlots l ≠ cmpSlots j := by
        intro h
        have := congrArg Fin.val (cmpSlots_injective h)
        omega
      rw [hChigh _ (by dsimp [cmpSlots]; omega) (hneq 6 (by decide))
        (hneq _ (C10TailFeed.qnumSlot_lt lower)) (hneq _ (C10TailFeed.zeroSlot_lt lower))
        (hneq _ (C10TailFeed.qdenSlot_lt lower))]
      exact hFblank j (by omega) (by have := C10TailFeed.posSlot_lt lower; omega)
        (by have := C10TailFeed.negSlot_lt lower; omega) (by have := C10TailFeed.denSlot_lt lower; omega)
  · rw [hChigh _ hsge (cmp_ne_scratch ph 6) (cmp_ne_scratch ph (qnumSlot lower))
      (cmp_ne_scratch ph (zeroSlot lower)) (cmp_ne_scratch ph (qdenSlot lower))]
    exact hFrec.trans hDrec
  · intro j
    fin_cases j
    · exact hCwidth0
    · exact hCwidth1
  · intro i hi
    obtain ⟨⟨hc, ha, hb, hw, hs⟩, hpv⟩ := hi
    by_cases hiw : i = widthSlot ph 1
    · subst i
      exact hCwidth1
    · have hC : Ac i = Af i := install_other _ _ _ _
        (constantSlots_other ph lower i (Ne.symm hiw) (hc 6)
          (hc (qnumSlot lower)) (hc (zeroSlot lower)) (hc (qdenSlot lower)) hpv)
      have hD : Ad i = A i := install_other _ _ _ _
        (dimensionSlots_other ph i (Ne.symm hiw) (hc 6) hpv)
      exact hC.trans ((hFframe i hc ha hb hw hs).trans hD)
  · intro i hi
    obtain ⟨hc, ha, hb, hw, hs⟩ := hi
    exact hFheadframe i hc ha hb hw hs

end NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformInput
