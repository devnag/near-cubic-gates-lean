import Proof.CaseAnalysis.FinalTailUniformInput
import Proof.CaseAnalysis.FinalThresholdWidths

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedUniform

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorThresholdDecision
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev ParkedAt := C10TailUniformInput.Parked

def budget (b : ℕ) : ℕ :=
  2000*(w2 b+1)^2 + 232*w b + 439 + CompetitorDimensions.budget (w b)

theorem budget_mono {b b' : ℕ} (h : b ≤ b') : budget b ≤ budget b' := by
  have hw : w b ≤ w b' := by unfold w CompetitorRationalDecision.width; omega
  have hw2 : w2 b ≤ w2 b' := by unfold w2 CompetitorRationalDecision.width; omega
  unfold budget CompetitorDimensions.budget CompetitorDimensions.bootstrapBudget WilliamsUnaryProduct.budget
  gcongr

def thresholdBits (q : ℚ) : ℕ := max (Nat.size (numerator q)) (Nat.size q.den)

theorem thresholdBits_le (q : ℚ) (b : ℕ)
    (hn : numerator q < 2^(w b)) (hd : q.den < 2^(w b)) : thresholdBits q ≤ w b :=
  max_le (Nat.size_le.mpr hn) (Nat.size_le.mpr hd)

theorem numerator_fit (q : ℚ) : numerator q < 2^(thresholdBits q) :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))

theorem denominator_fit (q : ℚ) : q.den < 2^(thresholdBits q) :=
  (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

noncomputable def program (ph : Phase) (lower : Bool) (q : ℚ) :=
  Composition.machine (C10TailUniformInput.program ph lower (thresholdBits q) q)
    C10TailFeedFixedStages.cmpProgram

theorem fuel_le (b k : ℕ) (hk : k ≤ w b) :
    C10TailUniformInput.budget b k + 1 + 2000*(w b+1)^2 ≤ budget b := by
  have hw : w2 b = 2*w b+2 := rfl
  have hp : (w b+1)^2 ≤ (w2 b+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hc := Nat.mul_le_mul_left 2000 hp
  unfold C10TailUniformInput.budget C10TailRecordFeedUniform.budget
    CompetitorThresholdConstants.budget budget
  omega

theorem feed_uniform (ph : Phase) (lower : Bool) (q : ℚ) :
    ∃ (states : ℕ) (m : Machine bank states),
      ∀ (b : ℕ) (est : CompetitorValidity.Estimate) (_hv : est.Valid b) (_hq : 0 ≤ q)
        (_hqnum : numerator q < 2^(w b)) (_hqden : q.den < 2^(w b))
        (H : Fin bank → ℕ) (A : Fin bank → List Bool) (_hp : ParkedAt ph b est H A),
      ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
        Step m (budget b) H A H' A' ∧
        (readTapeBit (A' (cmpSlots 65)) 0 = true ↔ passes lower est.positive est.negative est.denominator q) ∧
        (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
          (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) →
          i ≠ scratch ph → (∀ j, privateSlot ph j ≠ i) → A' i = A i) ∧
        (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
          (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → H' i = H i) ∧
        H' (cmpSlots 65) = 0 ∧ A' (scratch ph) = A (scratch ph) ∧
        (∀ j, A' (widthSlot ph j) = A (widthSlot ph j)) := by
  refine ⟨_, program ph lower q, ?_⟩
  intro b est hv hq hqnum hqden H A hp
  have hk := thresholdBits_le q b hqnum hqden
  obtain ⟨Hf, Af, hprep, hheads, hinput, hrec, hwidth, hframe, hheadframe⟩ :=
    C10TailUniformInput.input_run ph lower (thresholdBits q) q b est hv hk
      (numerator_fit q) (denominator_fit q) H A hp
  obtain ⟨out, hcmp, hiff⟩ := compare_step lower (w b) est.positive est.negative est.denominator q
    (pos_lt b est hv) (neg_lt b est hv) (den_lt b est hv) hv.denominatorPositive
    hq hqnum hqden cmpSlots cmpSlots_injective Hf Af hheads hinput
  have hrun := hprep.seq hcmp
  refine ⟨Hf, install cmpSlots Af out, Step.enlarge hrun (fuel_le b (thresholdBits q) hk), ?_, ?_, ?_, hheads 65, ?_, ?_⟩
  · rw [install_slot cmpSlots cmpSlots_injective Af out 65]
    exact hiff
  · intro i hc ha hb hw hs hpv
    rw [install_other cmpSlots Af out i hc]
    exact hframe i ⟨⟨hc, ha, hb, hw, hs⟩, hpv⟩
  · intro i hc ha hb hw hs
    exact hheadframe i ⟨hc, ha, hb, hw, hs⟩
  · rw [install_other cmpSlots Af out (scratch ph) (fun j => cmp_ne_scratch ph j)]
    exact hrec
  · intro j
    have hout := C10TailUniformInput.coreOutside_low ph (widthSlot ph j)
      (by have := (widthSlot_range ph j).2; omega)
    rw [install_other cmpSlots Af out (widthSlot ph j) hout.1]
    exact hwidth j

end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedUniform
