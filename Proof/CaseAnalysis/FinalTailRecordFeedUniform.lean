import Proof.CaseAnalysis.FinalTailFeedFixedStages

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailRecordFeedUniform

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorMonomialStream
open CompetitorThresholdDecision SignedSortKey ClockNormalize
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep (w w2 Parked)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeed
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedFixedStages

theorem field_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    field W est 1 1 0 = binary (w W) est.positive := rfl
theorem field_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    field W est 1 1 1 = binary (w W) est.negative := rfl
theorem field_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    field W est 1 1 2 = binary (w W) est.denominator := rfl

theorem field_pos_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field W est 1 1 0).length = w W := by
  rw [field_pos, binary_length]
theorem field_neg_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field W est 1 1 1).length = w W := by
  rw [field_neg, binary_length]
theorem field_den_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field W est 1 1 2).length = w W := by
  rw [field_den, binary_length]

theorem cursor_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor W est 1 1 0 = 0 := fieldCursor_zero W est 1 1

theorem cursor_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor W est 1 1 1 = 2*(w W)+1 := by
  have h : fieldCursor W est 1 1 1
      = fieldCursor W est 1 1 0 + 2*(field W est 1 1 0).length + 1 :=
    fieldCursor_succ W est 1 1 0 (by decide)
  rw [h, cursor_pos, field_pos_length, Nat.zero_add]

theorem cursor_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor W est 1 1 2 = 4*(w W)+2 := by
  have h : fieldCursor W est 1 1 2
      = fieldCursor W est 1 1 1 + 2*(field W est 1 1 1).length + 1 :=
    fieldCursor_succ W est 1 1 1 (by decide)
  rw [h, cursor_neg, field_neg_length]
  omega

theorem frame_le_w2 (W : ℕ) : 2*w W+1 ≤ w2 W := by
  unfold w2 CompetitorRationalDecision.width
  omega

structure Ready (ph : CloseoutRowsOriginalSchedule.Phase) (W : ℕ)
    (est : CompetitorValidity.Estimate) (H : Fin bank → ℕ) (A : Fin bank → List Bool) : Prop where
  recWord : A (scratch ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord W est 1 1
  recH : H (scratch ph) = 0
  driver : A (cmpSlots 6) = List.replicate (w2 W) true
  cmpH : ∀ j, H (cmpSlots j) = 0
  cmpA : ∀ j, j.val ≠ 6 → A (cmpSlots j) = []
  nAH : ∀ j, H (normSlots j) = 0
  nAA : ∀ j, A (normSlots j) = []
  nBH : ∀ j, H (normSlotsB j) = 0
  nBA : ∀ j, A (normSlotsB j) = []
  wH : ∀ j, H (wordSlots j) = 0
  wA : ∀ j, A (wordSlots j) = []

noncomputable def recordProgram (ph : CloseoutRowsOriginalSchedule.Phase) (lower : Bool) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine ((fieldProgram (scratch ph) (normSlots 1))) (rewindProgram (normSlots 1) (cmpSlots 6) (normSlots 2))) (normProgram (quintSlots (cmpSlots 6) (normSlots 1) (cmpSlots (posSlot lower)) (normSlots 3) (normSlots 4)))) (fieldProgram (scratch ph) (normSlotsB 1))) (rewindProgram (normSlotsB 1) (cmpSlots 6) (normSlotsB 2))) (normProgram (quintSlots (cmpSlots 6) (normSlotsB 1) (cmpSlots (negSlot lower)) (normSlotsB 3) (normSlotsB 4)))) (fieldProgram (scratch ph) (cmpSlots (denSlot lower)))) (rewindProgram (cmpSlots (denSlot lower)) (cmpSlots 6) (wordSlots 4))

def budget (W : ℕ) :=
  (((((((2*w W+1)+1+(2*w2 W+2))+1+(4*w2 W+4))+1+(2*w W+1))+1+(2*w2 W+2))+1+(4*w2 W+4))+1+(2*w W+1))+1+(2*w2 W+2)

theorem record_run (ph : CloseoutRowsOriginalSchedule.Phase) (lower : Bool) (W : ℕ)
    (est : CompetitorValidity.Estimate) (hv : est.Valid W)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool) (hp : Ready ph W est H A) :
    ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step (recordProgram ph lower) (budget W) H A H' A' ∧
      A' (cmpSlots 6) = List.replicate (w2 W) true ∧
      A' (cmpSlots (posSlot lower)) = frame (binary (w2 W) est.positive) ∧
      A' (cmpSlots (negSlot lower)) = frame (binary (w2 W) est.negative) ∧
      A' (cmpSlots (denSlot lower)) = frame (binary (w W) est.denominator) ∧
      (∀ j, H' (cmpSlots j) = 0) ∧
      (∀ j, j.val ≠ 6 → j.val ≠ (posSlot lower).val → j.val ≠ (negSlot lower).val →
        j.val ≠ (denSlot lower).val → A' (cmpSlots j) = []) ∧
      A' (scratch ph) = A (scratch ph) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
        (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → A' i = A i) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
        (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → H' i = H i) := by
  classical
  let A1 := A
  have hA1drv : A1 (cmpSlots 6) = List.replicate (w2 W) true := hp.driver
  have hA1o : ∀ i, cmpSlots 6 ≠ i → wordSlots 0 ≠ i → A1 i = A i := fun _ _ _ => rfl
  -- ## Within-block distinctness
  have hcneq : ∀ i j : Fin 67, i.val ≠ j.val → cmpSlots i ≠ cmpSlots j := by
    intro i j hij he
    exact hij (congrArg Fin.val (cmpSlots_injective he))
  have hns : ∀ i j : Fin 5, i.val ≠ j.val → normSlots i ≠ normSlots j := by
    intro i j hij he
    exact hij (congrArg Fin.val (normSlots_injective he))
  have hnbs : ∀ i j : Fin 5, i.val ≠ j.val → normSlotsB i ≠ normSlotsB j := by
    intro i j hij he
    exact hij (congrArg Fin.val (normSlotsB_injective he))
  have hwsn : ∀ i j : Fin 6, i.val ≠ j.val → wordSlots i ≠ wordSlots j := by
    intro i j hij he
    exact hij (congrArg Fin.val (wordSlots_injective he))
  -- ## Stage 2 — lift the record's positive part onto normaliser block A, tape 1
  obtain ⟨H2, A2, st2, hA2dst, hA2src, hH2src, hH2dst, hA2o, hH2o⟩ :=
    C10TailFeedFixedStages.field_stage W est 1 1 0 (scratch ph) (normSlots 1) ((normA_ne_scratch ph 1).symm)
      H A1 (by rw [hp.recH, cursor_pos]) (hp.nAH 1)
      ((hA1o (scratch ph) (cmp_ne_scratch ph 6) (word_ne_scratch ph 0)).trans hp.recWord)
      ((hA1o (normSlots 1) (cmp_ne_normA 6 1) ((normA_ne_word 1 0).symm)).trans (hp.nAA 1))
  have hA2dst' : A2 (normSlots 1) = frame (binary (w W) est.positive) := by
    rw [hA2dst, field_pos]
  have hH2dst' : H2 (normSlots 1) = 2*(w W)+1 := by
    rw [hH2dst, field_pos_length]
  have hA2keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → cmpSlots 6 ≠ i →
      wordSlots 0 ≠ i → A2 i = A i := by
    intro i h1 h2 h3 h4
    rw [hA2o i h1 h2, hA1o i h3 h4]
  -- ## Stage 3 — reset that tape's head against the comparator's driver
  obtain ⟨H3, A3, st3, hA3src, hA3drv, hH3src, hH3drv, hA3o, hH3o⟩ :=
    C10TailFeedFixedStages.rewind_stage (normSlots 1) (cmpSlots 6) (normSlots 2) ((cmp_ne_normA 6 1).symm)
      (hns 1 2 (by decide)) (cmp_ne_normA 6 2) (w2 W) (2*(w W)+1) (frame_le_w2 W)
      (frame (binary (w W) est.positive)) H2 A2 hH2dst'
      ((hH2o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm) ((cmp_ne_normA 6 1).symm)).trans
        (hp.cmpH 6))
      ((hH2o (normSlots 2) ((normA_ne_scratch ph 2).symm) (hns 1 2 (by decide))).trans
        (hp.nAH 2))
      hA2dst'
      ((hA2o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm) ((cmp_ne_normA 6 1).symm)).trans hA1drv)
      ((hA2keep (normSlots 2) ((normA_ne_scratch ph 2).symm) (hns 1 2 (by decide))
        (cmp_ne_normA 6 2) ((normA_ne_word 2 0).symm)).trans (hp.nAA 2))
  have hH3keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      cmpSlots 6 ≠ i → H3 i = H i := by
    intro i h1 h2 h3 h4
    rw [hH3o i h2 h4 h3, hH2o i h1 h2]
  have hA3keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      cmpSlots 6 ≠ i → wordSlots 0 ≠ i → A3 i = A i := by
    intro i h1 h2 h3 h4 h5
    rw [hA3o i h2 h4 h3, hA2keep i h1 h2 h4 h5]
  -- ## Stage 4 — widen the positive part straight onto the comparator's `posSlot`
  obtain ⟨A4, st4, hA4pos, hA4drv, hA4o⟩ :=
    C10TailFeedFixedStages.norm_stage (quintSlots (cmpSlots 6) (normSlots 1) (cmpSlots (posSlot lower))
        (normSlots 3) (normSlots 4))
      (quintSlots_injective _ _ _ _ _ (cmp_ne_normA 6 1)
        (hcneq 6 (posSlot lower) (by cases lower <;> decide)) (cmp_ne_normA 6 3)
        (cmp_ne_normA 6 4) ((cmp_ne_normA (posSlot lower) 1).symm) (hns 1 3 (by decide))
        (hns 1 4 (by decide)) (cmp_ne_normA (posSlot lower) 3)
        (cmp_ne_normA (posSlot lower) 4) (hns 3 4 (by decide)))
      (w2 W) (binary (w W) est.positive) H3 A3
      (by
        intro j
        fin_cases j
        · exact hH3drv
        · exact hH3src
        · exact (hH3keep (cmpSlots (posSlot lower)) ((cmp_ne_scratch ph (posSlot lower)).symm)
            ((cmp_ne_normA (posSlot lower) 1).symm) ((cmp_ne_normA (posSlot lower) 2).symm)
            (hcneq 6 (posSlot lower) (by cases lower <;> decide))).trans (hp.cmpH _)
        · exact (hH3keep (normSlots 3) ((normA_ne_scratch ph 3).symm) (hns 1 3 (by decide))
            (hns 2 3 (by decide)) (cmp_ne_normA 6 3)).trans (hp.nAH 3)
        · exact (hH3keep (normSlots 4) ((normA_ne_scratch ph 4).symm) (hns 1 4 (by decide))
            (hns 2 4 (by decide)) (cmp_ne_normA 6 4)).trans (hp.nAH 4))
      (by
        intro j
        fin_cases j
        · exact hA3drv
        · exact hA3src
        · exact (hA3keep (cmpSlots (posSlot lower)) ((cmp_ne_scratch ph (posSlot lower)).symm)
            ((cmp_ne_normA (posSlot lower) 1).symm) ((cmp_ne_normA (posSlot lower) 2).symm)
            (hcneq 6 (posSlot lower) (by cases lower <;> decide))
            ((cmp_ne_word (posSlot lower) 0).symm)).trans (hp.cmpA _ (by cases lower <;> decide))
        · exact (hA3keep (normSlots 3) ((normA_ne_scratch ph 3).symm) (hns 1 3 (by decide))
            (hns 2 3 (by decide)) (cmp_ne_normA 6 3) ((normA_ne_word 3 0).symm)).trans
            (hp.nAA 3)
        · exact (hA3keep (normSlots 4) ((normA_ne_scratch ph 4).symm) (hns 1 4 (by decide))
            (hns 2 4 (by decide)) (cmp_ne_normA 6 4) ((normA_ne_word 4 0).symm)).trans
            (hp.nAA 4))
  have hA4pos' : A4 (cmpSlots (posSlot lower)) = frame (binary (w2 W) est.positive) := by
    have h : A4 (cmpSlots (posSlot lower))
        = frame (ClockNormalize.resize (w2 W) (binary (w W) est.positive)) := hA4pos
    rw [h]
    exact widen W est.positive hv.positive
  have hA4drv' : A4 (cmpSlots 6) = List.replicate (w2 W) true := hA4drv
  have hA4out : ∀ i : Fin bank, cmpSlots 6 ≠ i → normSlots 1 ≠ i →
      cmpSlots (posSlot lower) ≠ i → normSlots 3 ≠ i → normSlots 4 ≠ i → A4 i = A3 i := by
    intro i h0 h1 h2 h3 h4
    refine hA4o i ?_
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  -- ## Stage 5 — lift the record's negative part onto normaliser block B, tape 1
  obtain ⟨H5, A5, st5, hA5dst, hA5src, hH5src, hH5dst, hA5o, hH5o⟩ :=
    C10TailFeedFixedStages.field_stage W est 1 1 1 (scratch ph) (normSlotsB 1) ((normB_ne_scratch ph 1).symm)
      H3 A4
      (by
        rw [hH3o (scratch ph) (normA_ne_scratch ph 1) (cmp_ne_scratch ph 6)
            (normA_ne_scratch ph 2), hH2src, cursor_pos, field_pos_length, cursor_neg,
          Nat.zero_add])
      ((hH3keep (normSlotsB 1) ((normB_ne_scratch ph 1).symm) (normA_ne_normB 1 1)
        (normA_ne_normB 2 1) (cmp_ne_normB 6 1)).trans (hp.nBH 1))
      ((hA4out (scratch ph) (cmp_ne_scratch ph 6) (normA_ne_scratch ph 1)
        (cmp_ne_scratch ph (posSlot lower)) (normA_ne_scratch ph 3)
        (normA_ne_scratch ph 4)).trans
        ((hA3o (scratch ph) (normA_ne_scratch ph 1) (cmp_ne_scratch ph 6)
          (normA_ne_scratch ph 2)).trans hA2src))
      ((hA4out (normSlotsB 1) (cmp_ne_normB 6 1) (normA_ne_normB 1 1)
        (cmp_ne_normB (posSlot lower) 1) (normA_ne_normB 3 1) (normA_ne_normB 4 1)).trans
        ((hA3keep (normSlotsB 1) ((normB_ne_scratch ph 1).symm) (normA_ne_normB 1 1)
          (normA_ne_normB 2 1) (cmp_ne_normB 6 1) ((normB_ne_word 1 0).symm)).trans
          (hp.nBA 1)))
  have hA5dst' : A5 (normSlotsB 1) = frame (binary (w W) est.negative) := by
    rw [hA5dst, field_neg]
  have hH5dst' : H5 (normSlotsB 1) = 2*(w W)+1 := by
    rw [hH5dst, field_neg_length]
  -- ## Stage 6 — reset that tape's head
  obtain ⟨H6, A6, st6, hA6src, hA6drv, hH6src, hH6drv, hA6o, hH6o⟩ :=
    C10TailFeedFixedStages.rewind_stage (normSlotsB 1) (cmpSlots 6) (normSlotsB 2) ((cmp_ne_normB 6 1).symm)
      (hnbs 1 2 (by decide)) (cmp_ne_normB 6 2) (w2 W) (2*(w W)+1) (frame_le_w2 W)
      (frame (binary (w W) est.negative)) H5 A5 hH5dst'
      ((hH5o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm) ((cmp_ne_normB 6 1).symm)).trans hH3drv)
      ((hH5o (normSlotsB 2) ((normB_ne_scratch ph 2).symm) (hnbs 1 2 (by decide))).trans
        ((hH3keep (normSlotsB 2) ((normB_ne_scratch ph 2).symm) (normA_ne_normB 1 2)
          (normA_ne_normB 2 2) (cmp_ne_normB 6 2)).trans (hp.nBH 2)))
      hA5dst'
      ((hA5o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm) ((cmp_ne_normB 6 1).symm)).trans hA4drv')
      ((hA5o (normSlotsB 2) ((normB_ne_scratch ph 2).symm) (hnbs 1 2 (by decide))).trans
        ((hA4out (normSlotsB 2) (cmp_ne_normB 6 2) (normA_ne_normB 1 2)
          (cmp_ne_normB (posSlot lower) 2) (normA_ne_normB 3 2) (normA_ne_normB 4 2)).trans
          ((hA3keep (normSlotsB 2) ((normB_ne_scratch ph 2).symm) (normA_ne_normB 1 2)
            (normA_ne_normB 2 2) (cmp_ne_normB 6 2) ((normB_ne_word 2 0).symm)).trans
            (hp.nBA 2))))
  have hH6keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      normSlotsB 1 ≠ i → normSlotsB 2 ≠ i → cmpSlots 6 ≠ i → H6 i = H i := by
    intro i h1 h2 h3 h4 h5 h6
    rw [hH6o i h4 h6 h5, hH5o i h1 h4, hH3keep i h1 h2 h3 h6]
  have hA6keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      normSlots 3 ≠ i → normSlots 4 ≠ i → normSlotsB 1 ≠ i → normSlotsB 2 ≠ i →
      cmpSlots 6 ≠ i → cmpSlots (posSlot lower) ≠ i → wordSlots 0 ≠ i → A6 i = A i := by
    intro i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [hA6o i h6 h8 h7, hA5o i h1 h6, hA4out i h8 h2 h9 h4 h5, hA3keep i h1 h2 h3 h8 h10]
  -- ## Stage 7 — widen the negative part straight onto the comparator's `negSlot`
  obtain ⟨A7, st7, hA7neg, hA7drv, hA7o⟩ :=
    C10TailFeedFixedStages.norm_stage (quintSlots (cmpSlots 6) (normSlotsB 1) (cmpSlots (negSlot lower))
        (normSlotsB 3) (normSlotsB 4))
      (quintSlots_injective _ _ _ _ _ (cmp_ne_normB 6 1)
        (hcneq 6 (negSlot lower) (by cases lower <;> decide)) (cmp_ne_normB 6 3)
        (cmp_ne_normB 6 4) ((cmp_ne_normB (negSlot lower) 1).symm) (hnbs 1 3 (by decide))
        (hnbs 1 4 (by decide)) (cmp_ne_normB (negSlot lower) 3)
        (cmp_ne_normB (negSlot lower) 4) (hnbs 3 4 (by decide)))
      (w2 W) (binary (w W) est.negative) H6 A6
      (by
        intro j
        fin_cases j
        · exact hH6drv
        · exact hH6src
        · exact (hH6keep (cmpSlots (negSlot lower)) ((cmp_ne_scratch ph (negSlot lower)).symm)
            ((cmp_ne_normA (negSlot lower) 1).symm) ((cmp_ne_normA (negSlot lower) 2).symm)
            ((cmp_ne_normB (negSlot lower) 1).symm) ((cmp_ne_normB (negSlot lower) 2).symm)
            (hcneq 6 (negSlot lower) (by cases lower <;> decide))).trans (hp.cmpH _)
        · exact (hH6keep (normSlotsB 3) ((normB_ne_scratch ph 3).symm) (normA_ne_normB 1 3)
            (normA_ne_normB 2 3) (hnbs 1 3 (by decide)) (hnbs 2 3 (by decide))
            (cmp_ne_normB 6 3)).trans (hp.nBH 3)
        · exact (hH6keep (normSlotsB 4) ((normB_ne_scratch ph 4).symm) (normA_ne_normB 1 4)
            (normA_ne_normB 2 4) (hnbs 1 4 (by decide)) (hnbs 2 4 (by decide))
            (cmp_ne_normB 6 4)).trans (hp.nBH 4))
      (by
        intro j
        fin_cases j
        · exact hA6drv
        · exact hA6src
        · exact (hA6keep (cmpSlots (negSlot lower)) ((cmp_ne_scratch ph (negSlot lower)).symm)
            ((cmp_ne_normA (negSlot lower) 1).symm) ((cmp_ne_normA (negSlot lower) 2).symm)
            ((cmp_ne_normA (negSlot lower) 3).symm) ((cmp_ne_normA (negSlot lower) 4).symm)
            ((cmp_ne_normB (negSlot lower) 1).symm) ((cmp_ne_normB (negSlot lower) 2).symm)
            (hcneq 6 (negSlot lower) (by cases lower <;> decide))
            (hcneq (posSlot lower) (negSlot lower) (by cases lower <;> decide))
            ((cmp_ne_word (negSlot lower) 0).symm)).trans (hp.cmpA _ (by cases lower <;> decide))
        · exact (hA6keep (normSlotsB 3) ((normB_ne_scratch ph 3).symm) (normA_ne_normB 1 3)
            (normA_ne_normB 2 3) (normA_ne_normB 3 3) (normA_ne_normB 4 3)
            (hnbs 1 3 (by decide)) (hnbs 2 3 (by decide)) (cmp_ne_normB 6 3)
            (cmp_ne_normB (posSlot lower) 3) ((normB_ne_word 3 0).symm)).trans (hp.nBA 3)
        · exact (hA6keep (normSlotsB 4) ((normB_ne_scratch ph 4).symm) (normA_ne_normB 1 4)
            (normA_ne_normB 2 4) (normA_ne_normB 3 4) (normA_ne_normB 4 4)
            (hnbs 1 4 (by decide)) (hnbs 2 4 (by decide)) (cmp_ne_normB 6 4)
            (cmp_ne_normB (posSlot lower) 4) ((normB_ne_word 4 0).symm)).trans (hp.nBA 4))
  have hA7neg' : A7 (cmpSlots (negSlot lower)) = frame (binary (w2 W) est.negative) := by
    have h : A7 (cmpSlots (negSlot lower))
        = frame (ClockNormalize.resize (w2 W) (binary (w W) est.negative)) := hA7neg
    rw [h]
    exact widen W est.negative hv.negative
  have hA7drv' : A7 (cmpSlots 6) = List.replicate (w2 W) true := hA7drv
  have hA7out : ∀ i : Fin bank, cmpSlots 6 ≠ i → normSlotsB 1 ≠ i →
      cmpSlots (negSlot lower) ≠ i → normSlotsB 3 ≠ i → normSlotsB 4 ≠ i → A7 i = A6 i := by
    intro i h0 h1 h2 h3 h4
    refine hA7o i ?_
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  -- ## Stage 8 — the denominator goes straight onto the comparator's `denSlot`
  obtain ⟨H8, A8, st8, hA8dst, hA8src, _, hH8dst, hA8o, hH8o⟩ :=
    C10TailFeedFixedStages.field_stage W est 1 1 2 (scratch ph) (cmpSlots (denSlot lower))
      ((cmp_ne_scratch ph (denSlot lower)).symm) H6 A7
      (by
        rw [hH6o (scratch ph) (normB_ne_scratch ph 1) (cmp_ne_scratch ph 6)
            (normB_ne_scratch ph 2), hH5src, cursor_neg, field_neg_length, cursor_den]
        omega)
      ((hH6keep (cmpSlots (denSlot lower)) ((cmp_ne_scratch ph (denSlot lower)).symm)
        ((cmp_ne_normA (denSlot lower) 1).symm) ((cmp_ne_normA (denSlot lower) 2).symm)
        ((cmp_ne_normB (denSlot lower) 1).symm) ((cmp_ne_normB (denSlot lower) 2).symm)
        (hcneq 6 (denSlot lower) (by cases lower <;> decide))).trans (hp.cmpH _))
      ((hA7out (scratch ph) (cmp_ne_scratch ph 6) (normB_ne_scratch ph 1)
        (cmp_ne_scratch ph (negSlot lower)) (normB_ne_scratch ph 3)
        (normB_ne_scratch ph 4)).trans
        ((hA6o (scratch ph) (normB_ne_scratch ph 1) (cmp_ne_scratch ph 6)
          (normB_ne_scratch ph 2)).trans hA5src))
      ((hA7out (cmpSlots (denSlot lower)) (hcneq 6 (denSlot lower) (by cases lower <;> decide))
        ((cmp_ne_normB (denSlot lower) 1).symm)
        (hcneq (negSlot lower) (denSlot lower) (by cases lower <;> decide))
        ((cmp_ne_normB (denSlot lower) 3).symm)
        ((cmp_ne_normB (denSlot lower) 4).symm)).trans
        ((hA6keep (cmpSlots (denSlot lower)) ((cmp_ne_scratch ph (denSlot lower)).symm)
          ((cmp_ne_normA (denSlot lower) 1).symm) ((cmp_ne_normA (denSlot lower) 2).symm)
          ((cmp_ne_normA (denSlot lower) 3).symm) ((cmp_ne_normA (denSlot lower) 4).symm)
          ((cmp_ne_normB (denSlot lower) 1).symm) ((cmp_ne_normB (denSlot lower) 2).symm)
          (hcneq 6 (denSlot lower) (by cases lower <;> decide))
          (hcneq (posSlot lower) (denSlot lower) (by cases lower <;> decide))
          ((cmp_ne_word (denSlot lower) 0).symm)).trans (hp.cmpA _ (by cases lower <;> decide))))
  have hA8dst' : A8 (cmpSlots (denSlot lower)) = frame (binary (w W) est.denominator) := by
    rw [hA8dst, field_den]
  have hH8dst' : H8 (cmpSlots (denSlot lower)) = 2*(w W)+1 := by
    rw [hH8dst, field_den_length]
  -- ## Stage 9 — reset the denominator tape's head
  obtain ⟨H9, A9, st9, hA9src, hA9drv, hH9src, hH9drv, hA9o, hH9o⟩ :=
    C10TailFeedFixedStages.rewind_stage (cmpSlots (denSlot lower)) (cmpSlots 6) (wordSlots 4)
      (hcneq (denSlot lower) 6 (by cases lower <;> decide)) (cmp_ne_word (denSlot lower) 4)
      (cmp_ne_word 6 4) (w2 W) (2*(w W)+1) (frame_le_w2 W)
      (frame (binary (w W) est.denominator)) H8 A8 hH8dst'
      ((hH8o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm)
        (hcneq (denSlot lower) 6 (by cases lower <;> decide))).trans hH6drv)
      ((hH8o (wordSlots 4) ((word_ne_scratch ph 4).symm)
        (cmp_ne_word (denSlot lower) 4)).trans
        ((hH6keep (wordSlots 4) ((word_ne_scratch ph 4).symm) (normA_ne_word 1 4)
          (normA_ne_word 2 4) (normB_ne_word 1 4) (normB_ne_word 2 4)
          (cmp_ne_word 6 4)).trans (hp.wH 4)))
      hA8dst'
      ((hA8o (cmpSlots 6) ((cmp_ne_scratch ph 6).symm)
        (hcneq (denSlot lower) 6 (by cases lower <;> decide))).trans hA7drv')
      ((hA8o (wordSlots 4) ((word_ne_scratch ph 4).symm)
        (cmp_ne_word (denSlot lower) 4)).trans
        ((hA7out (wordSlots 4) (cmp_ne_word 6 4) (normB_ne_word 1 4)
          (cmp_ne_word (negSlot lower) 4) (normB_ne_word 3 4) (normB_ne_word 4 4)).trans
          ((hA6keep (wordSlots 4) ((word_ne_scratch ph 4).symm) (normA_ne_word 1 4)
            (normA_ne_word 2 4) (normA_ne_word 3 4) (normA_ne_word 4 4) (normB_ne_word 1 4)
            (normB_ne_word 2 4) (cmp_ne_word 6 4) (cmp_ne_word (posSlot lower) 4)
            (hwsn 0 4 (by decide))).trans (hp.wA 4))))
  -- ## The bank at level 9
  have hH9keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      normSlotsB 1 ≠ i → normSlotsB 2 ≠ i → wordSlots 4 ≠ i → cmpSlots 6 ≠ i →
      cmpSlots (denSlot lower) ≠ i → H9 i = H i := by
    intro i h1 h2 h3 h4 h5 h6 h7 h8
    rw [hH9o i h8 h7 h6, hH8o i h1 h8, hH6keep i h1 h2 h3 h4 h5 h7]
  have hA9keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → normSlots 2 ≠ i →
      normSlots 3 ≠ i → normSlots 4 ≠ i → normSlotsB 1 ≠ i → normSlotsB 2 ≠ i →
      normSlotsB 3 ≠ i → normSlotsB 4 ≠ i → wordSlots 0 ≠ i → wordSlots 4 ≠ i →
      cmpSlots 6 ≠ i → cmpSlots (posSlot lower) ≠ i → cmpSlots (negSlot lower) ≠ i →
      cmpSlots (denSlot lower) ≠ i → A9 i = A i := by
    intro i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [hA9o i h15 h12 h11, hA8o i h1 h15, hA7out i h12 h6 h14 h8 h9,
      hA6keep i h1 h2 h3 h4 h5 h6 h7 h12 h13 h10]
  have hH9cmp : ∀ k : Fin 67, k.val ≠ 6 → k.val ≠ (denSlot lower).val →
      H9 (cmpSlots k) = 0 := by
    intro k h6 hd
    exact (hH9keep (cmpSlots k) ((cmp_ne_scratch ph k).symm) ((cmp_ne_normA k 1).symm)
      ((cmp_ne_normA k 2).symm) ((cmp_ne_normB k 1).symm) ((cmp_ne_normB k 2).symm)
      ((cmp_ne_word k 4).symm) (hcneq 6 k (fun hh => h6 hh.symm))
      (hcneq (denSlot lower) k (fun hh => hd hh.symm))).trans (hp.cmpH k)
  have hH9word : ∀ k : Fin 6, k.val ≠ 4 → H9 (wordSlots k) = 0 := by
    intro k hk
    exact (hH9keep (wordSlots k) ((word_ne_scratch ph k).symm) (normA_ne_word 1 k)
      (normA_ne_word 2 k) (normB_ne_word 1 k) (normB_ne_word 2 k)
      (hwsn 4 k (fun hh => hk hh.symm)) (cmp_ne_word 6 k)
      (cmp_ne_word (denSlot lower) k)).trans (hp.wH k)
  have hA9cmp : ∀ k : Fin 67, k.val ≠ 6 → k.val ≠ (posSlot lower).val →
      k.val ≠ (negSlot lower).val → k.val ≠ (denSlot lower).val → A9 (cmpSlots k) = [] := by
    intro k h6 hpos hneg hden
    exact (hA9keep (cmpSlots k) ((cmp_ne_scratch ph k).symm) ((cmp_ne_normA k 1).symm)
      ((cmp_ne_normA k 2).symm) ((cmp_ne_normA k 3).symm) ((cmp_ne_normA k 4).symm)
      ((cmp_ne_normB k 1).symm) ((cmp_ne_normB k 2).symm) ((cmp_ne_normB k 3).symm)
      ((cmp_ne_normB k 4).symm) ((cmp_ne_word k 0).symm) ((cmp_ne_word k 4).symm)
      (hcneq 6 k (fun hh => h6 hh.symm)) (hcneq (posSlot lower) k (fun hh => hpos hh.symm))
      (hcneq (negSlot lower) k (fun hh => hneg hh.symm))
      (hcneq (denSlot lower) k (fun hh => hden hh.symm))).trans (hp.cmpA k h6)
  have hA9word : ∀ k : Fin 6, k.val ≠ 0 → k.val ≠ 4 → A9 (wordSlots k) = [] := by
    intro k h0 h4
    exact (hA9keep (wordSlots k) ((word_ne_scratch ph k).symm) (normA_ne_word 1 k)
      (normA_ne_word 2 k) (normA_ne_word 3 k) (normA_ne_word 4 k) (normB_ne_word 1 k)
      (normB_ne_word 2 k) (normB_ne_word 3 k) (normB_ne_word 4 k)
      (hwsn 0 k (fun hh => h0 hh.symm)) (hwsn 4 k (fun hh => h4 hh.symm))
      (cmp_ne_word 6 k) (cmp_ne_word (posSlot lower) k) (cmp_ne_word (negSlot lower) k)
      (cmp_ne_word (denSlot lower) k)).trans (hp.wA k)
  have hA9pos : A9 (cmpSlots (posSlot lower)) = frame (binary (w2 W) est.positive) := by
    rw [hA9o (cmpSlots (posSlot lower))
        (hcneq (denSlot lower) (posSlot lower) (by cases lower <;> decide))
        (hcneq 6 (posSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (posSlot lower) 4).symm),
      hA8o (cmpSlots (posSlot lower)) ((cmp_ne_scratch ph (posSlot lower)).symm)
        (hcneq (denSlot lower) (posSlot lower) (by cases lower <;> decide)),
      hA7out (cmpSlots (posSlot lower))
        (hcneq 6 (posSlot lower) (by cases lower <;> decide))
        ((cmp_ne_normB (posSlot lower) 1).symm)
        (hcneq (negSlot lower) (posSlot lower) (by cases lower <;> decide))
        ((cmp_ne_normB (posSlot lower) 3).symm) ((cmp_ne_normB (posSlot lower) 4).symm),
      hA6o (cmpSlots (posSlot lower)) ((cmp_ne_normB (posSlot lower) 1).symm)
        (hcneq 6 (posSlot lower) (by cases lower <;> decide))
        ((cmp_ne_normB (posSlot lower) 2).symm),
      hA5o (cmpSlots (posSlot lower)) ((cmp_ne_scratch ph (posSlot lower)).symm)
        ((cmp_ne_normB (posSlot lower) 1).symm)]
    exact hA4pos'
  have hA9neg : A9 (cmpSlots (negSlot lower)) = frame (binary (w2 W) est.negative) := by
    rw [hA9o (cmpSlots (negSlot lower))
        (hcneq (denSlot lower) (negSlot lower) (by cases lower <;> decide))
        (hcneq 6 (negSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (negSlot lower) 4).symm),
      hA8o (cmpSlots (negSlot lower)) ((cmp_ne_scratch ph (negSlot lower)).symm)
        (hcneq (denSlot lower) (negSlot lower) (by cases lower <;> decide))]
    exact hA7neg'
  refine ⟨H9, A9, ?_, hA9drv, hA9pos, hA9neg, hA9src, ?_, hA9cmp, ?_, ?_, ?_⟩
  · have hrun := ((((((st2.seq st3).seq st4).seq st5).seq st6).seq st7).seq st8).seq st9
    simpa only [recordProgram, budget, field_pos_length, field_neg_length, field_den_length] using hrun
  · intro j
    by_cases h6 : j = 6
    · subst j
      exact hH9drv
    · by_cases hd : j = denSlot lower
      · subst j
        exact hH9src
      · exact hH9cmp j (fun he => h6 (Fin.ext he)) (fun he => hd (Fin.ext he))
  · rw [hA9o (scratch ph) (cmp_ne_scratch ph (denSlot lower)) (cmp_ne_scratch ph 6)
      (word_ne_scratch ph 4), hA8src, hp.recWord]
  · intro i hc hna hnb hw hsc
    exact hA9keep i hsc.symm (hna 1) (hna 2) (hna 3) (hna 4) (hnb 1) (hnb 2) (hnb 3) (hnb 4)
      (hw 0) (hw 4) (hc 6) (hc (posSlot lower)) (hc (negSlot lower)) (hc (denSlot lower))
  · intro i hc hna hnb hw hsc
    exact hH9keep i hsc.symm (hna 1) (hna 2) (hnb 1) (hnb 2) (hw 4) (hc 6)
      (hc (denSlot lower))

end NearCubicWires.RepairSource.CloseoutFinal.C10TailRecordFeedUniform
