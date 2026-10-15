import Proof.CaseAnalysis.FinalTailSlotsUniform

/-! # Fixed feeds docked into the C.10 verdict bank

Consumer: the three mean, moment, and acceptance comparisons in tail_uniform.
The docked machine is fixed before the runtime widths and records. Its frame
protects the shared prefix except the invoking phase's private scratch; it
also protects every tape outside that phase's old comparator-bank image.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedDockUniform

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorThresholdDecision
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform
  (privateSlotT widthSlotT feedSlots_private feedSlots_width PublicPrefix scratch_public width_public)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedUniform (ParkedAt)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def FeedFor (ph : Phase) (lower : Bool) (q : ℚ) {s : ℕ} (m : Machine bank s) : Prop :=
      ∀ (b : ℕ) (est : CompetitorValidity.Estimate) (_hv : est.Valid b) (_hq : 0 ≤ q)
        (_hqnum : numerator q < 2^(w b)) (_hqden : q.den < 2^(w b))
        (H : Fin bank → ℕ) (A : Fin bank → List Bool) (_hp : ParkedAt ph b est H A),
      ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
        Step m (C10TailFeedUniform.budget b) H A H' A' ∧
        (readTapeBit (A' (cmpSlots 65)) 0 = true ↔ passes lower est.positive est.negative est.denominator q) ∧
        (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
          (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) →
          i ≠ scratch ph → (∀ j, privateSlot ph j ≠ i) → A' i = A i) ∧
        (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) →
          (∀ j, normSlotsB j ≠ i) → (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → H' i = H i) ∧
        H' (cmpSlots 65) = 0 ∧ A' (scratch ph) = A (scratch ph) ∧
        (∀ j, A' (widthSlot ph j) = A (widthSlot ph j))

def PhaseParked (ph : Phase) (b : ℕ) (est : CompetitorValidity.Estimate)
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool) : Prop :=
  ParkedAt ph b est (fun j => H (feedSlots (phaseIndex ph) j)) (fun j => A (feedSlots (phaseIndex ph) j))

structure Result (ph : Phase) (lower : Bool) (q : ℚ) (est : CompetitorValidity.Estimate)
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool)
    (H' : Fin tailBank → ℕ) (A' : Fin tailBank → List Bool) : Prop where
  flag : readTapeBit (A' (feedSlots (phaseIndex ph) (cmpSlots 65))) 0 = true ↔
    passes lower est.positive est.negative est.denominator q
  flagHead : H' (feedSlots (phaseIndex ph) (cmpSlots 65)) = 0
  prefixA : ∀ i, i.val < 221 → (∀ j, privateSlotT ph j ≠ i) → A' i = A i
  prefixH : ∀ i, i.val < 221 → i ≠ scratchT ph → H' i = H i
  otherA : ∀ i, (∀ j, feedSlots (phaseIndex ph) j ≠ i) → A' i = A i
  otherH : ∀ i, (∀ j, feedSlots (phaseIndex ph) j ≠ i) → H' i = H i

noncomputable def docked {s : ℕ} (ph : Phase) (m : Machine bank s) :=
  RecoveryFocus.machine (feedSlots (phaseIndex ph)) m

theorem feed_dock {s : ℕ} (ph : Phase) (lower : Bool) (q : ℚ) (m : Machine bank s)
    (hfeed : FeedFor ph lower q m) (b : ℕ) (est : CompetitorValidity.Estimate) (hv : est.Valid b)
    (hq : 0 ≤ q) (hqnum : numerator q < 2^(w b)) (hqden : q.den < 2^(w b))
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool) (hp : PhaseParked ph b est H A) :
    ∃ (H' : Fin tailBank → ℕ) (A' : Fin tailBank → List Bool),
      Step (docked ph m) (C10TailFeedUniform.budget b) H A H' A' ∧ Result ph lower q est H A H' A' := by
  let k := phaseIndex ph
  obtain ⟨Hf, Af, hstep, hiff, htapes, hheads, hcmp65, hscr, _hwidth⟩ :=
    hfeed b est hv hq hqnum hqden _ _ hp
  have hinj := feedSlots_injective k
  have hdock := hstep.dock (feedSlots k) hinj H A (fun _ => rfl) (fun _ => rfl)
  have hchaseA : ∀ j : Fin bank, j.val < 221 → (∀ l, privateSlot ph l ≠ j) → Af j = A (feedSlots k j) := by
    intro j hj hprivate
    by_cases hs : j = scratch ph
    · rw [hs]
      exact hscr
    · exact htapes j (cmp_ne_pre j hj) (normA_ne_pre j hj) (normB_ne_pre j hj)
        (word_ne_pre j hj) hs hprivate
  have hchaseH : ∀ j : Fin bank, j.val < 221 → j ≠ scratch ph → Hf j = H (feedSlots k j) := by
    intro j hj hs
    exact hheads j (cmp_ne_pre j hj) (normA_ne_pre j hj) (normB_ne_pre j hj)
      (word_ne_pre j hj) hs
  refine ⟨dockH (feedSlots k) H Hf, install (feedSlots k) A Af, hdock, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot (feedSlots k) hinj A Af (cmpSlots 65)]
    exact hiff
  · rw [dockH_slot (feedSlots k) hinj H Hf (cmpSlots 65)]
    exact hcmp65
  · intro i hi hprivate
    have he : feedSlots k (preIdx i hi) = i := feedSlots_pre k i hi
    have hpv : ∀ l, privateSlot ph l ≠ preIdx i hi := by
      intro l hl
      apply hprivate l
      rw [← feedSlots_private k ph l, hl]
      exact he
    calc install (feedSlots k) A Af i
        = install (feedSlots k) A Af (feedSlots k (preIdx i hi)) := by rw [he]
      _ = Af (preIdx i hi) := install_slot (feedSlots k) hinj A Af (preIdx i hi)
      _ = A (feedSlots k (preIdx i hi)) := hchaseA (preIdx i hi) hi hpv
      _ = A i := by rw [he]
  · intro i hi hnei
    have he : feedSlots k (preIdx i hi) = i := feedSlots_pre k i hi
    have hne : preIdx i hi ≠ scratch ph := by
      intro hc
      apply hnei
      rw [← he, hc, feedSlots_scratch]
    calc dockH (feedSlots k) H Hf i
        = dockH (feedSlots k) H Hf (feedSlots k (preIdx i hi)) := by rw [he]
      _ = Hf (preIdx i hi) := dockH_slot (feedSlots k) hinj H Hf (preIdx i hi)
      _ = H (feedSlots k (preIdx i hi)) := hchaseH (preIdx i hi) hi hne
      _ = H i := by rw [he]
  · intro i hi
    exact install_other (feedSlots k) A Af i hi
  · intro i hi
    exact dockH_other (feedSlots k) H Hf i hi

end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedDockUniform
