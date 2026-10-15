import Proof.CaseAnalysis.FinalTailFeedDockUniform

/-! # Each C.10 feed preserves the next phase's parked input

Consumer: the three fixed feeds in tail_uniform. Comparator banks and
phase-private scratch are disjoint; the shared records and width words
survive. This closes the physical handoff between consecutive comparisons.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedDockUniform

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform
  (privateSlotT widthSlotT feedSlots_private feedSlots_width PublicPrefix scratch_public width_public)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem phaseIndex_ne {ph ph' : Phase} (hne : ph ≠ ph') : phaseIndex ph ≠ phaseIndex ph' := by
  cases ph <;> cases ph' <;> first | exact (hne rfl).elim | decide

theorem scratchT_ne {ph ph' : Phase} (hne : ph ≠ ph') : scratchT ph ≠ scratchT ph' := by
  cases ph <;> cases ph' <;> first | exact (hne rfl).elim | decide

theorem Result.head_low {ph : Phase} {lower : Bool} {q : ℚ} {est : CompetitorValidity.Estimate}
    {H H' : Fin tailBank → ℕ} {A A' : Fin tailBank → List Bool}
    (r : Result ph lower q est H A H' A') (i : Fin tailBank) (hi : i.val < 218) : H' i = H i := by
  have hs : 218 ≤ (scratchT ph).val := by cases ph <;> decide
  apply r.prefixH i (by omega)
  intro h
  have := congrArg Fin.val h
  omega

theorem Result.prefix_public {ph : Phase} {lower : Bool} {q : ℚ} {est : CompetitorValidity.Estimate}
    {H H' : Fin tailBank → ℕ} {A A' : Fin tailBank → List Bool}
    (r : Result ph lower q est H A H' A') (i : Fin tailBank) (hi : PublicPrefix i) : A' i = A i :=
  r.prefixA i hi.1 (hi.2 ph)

theorem Result.other_cmpA {ph : Phase} {lower : Bool} {q : ℚ} {est : CompetitorValidity.Estimate}
    {H H' : Fin tailBank → ℕ} {A A' : Fin tailBank → List Bool}
    (r : Result ph lower q est H A H' A') (ph' : Phase) (hne : ph ≠ ph') (j : Fin 67) :
    A' (feedSlots (phaseIndex ph') (cmpSlots j)) = A (feedSlots (phaseIndex ph') (cmpSlots j)) :=
  r.otherA _ (fun l => feedSlots_disjoint (phaseIndex_ne hne) (cmpSlots j) (cmp_ge j) l)

theorem Result.other_cmpH {ph : Phase} {lower : Bool} {q : ℚ} {est : CompetitorValidity.Estimate}
    {H H' : Fin tailBank → ℕ} {A A' : Fin tailBank → List Bool}
    (r : Result ph lower q est H A H' A') (ph' : Phase) (hne : ph ≠ ph') (j : Fin 67) :
    H' (feedSlots (phaseIndex ph') (cmpSlots j)) = H (feedSlots (phaseIndex ph') (cmpSlots j)) :=
  r.otherH _ (fun l => feedSlots_disjoint (phaseIndex_ne hne) (cmpSlots j) (cmp_ge j) l)

theorem Result.parked_of {ph ph' : Phase} {lower : Bool} {q : ℚ} {est : CompetitorValidity.Estimate}
    {H H' : Fin tailBank → ℕ} {A A' : Fin tailBank → List Bool}
    (r : Result ph lower q est H A H' A') (hne : ph ≠ ph')
    {b : ℕ} {est' : CompetitorValidity.Estimate} (hp : PhaseParked ph' b est' H A) :
    PhaseParked ph' b est' H' A' := by
  have hk := phaseIndex_ne hne
  have hslotWidth (j : Fin 2) : feedSlots (phaseIndex ph') (widthSlot ph' j) = widthSlotT ph' j :=
    feedSlots_width (phaseIndex ph') ph' j
  have hslotPrivate (j : Fin 29) : feedSlots (phaseIndex ph') (privateSlot ph' j) = privateSlotT ph' j :=
    feedSlots_private (phaseIndex ph') ph' j
  have hAhigh (j : Fin bank) (hj : 221 ≤ j.val) :
      A' (feedSlots (phaseIndex ph') j) = A (feedSlots (phaseIndex ph') j) :=
    r.otherA _ (fun l => feedSlots_disjoint hk j hj l)
  have hHhigh (j : Fin bank) (hj : 221 ≤ j.val) :
      H' (feedSlots (phaseIndex ph') j) = H (feedSlots (phaseIndex ph') j) :=
    r.otherH _ (fun l => feedSlots_disjoint hk j hj l)
  have hAwidth (j : Fin 2) : A' (widthSlotT ph' j) = A (widthSlotT ph' j) :=
    r.prefix_public _ (width_public ph' j)
  have hHwidth (j : Fin 2) : H' (widthSlotT ph' j) = H (widthSlotT ph' j) :=
    r.head_low _ (by have := (C10TailSlotsUniform.widthSlotT_range ph' j).2; omega)
  have hHprivate (j : Fin 29) : H' (privateSlotT ph' j) = H (privateSlotT ph' j) :=
    r.head_low _ (by have := (C10TailSlotsUniform.privateSlotT_range ph' j).2; omega)
  have hAprivate (j : Fin 29) : A' (privateSlotT ph' j) = A (privateSlotT ph' j) :=
    r.prefixA _ (by have := (C10TailSlotsUniform.privateSlotT_range ph' j).2; omega)
      (fun l => C10TailSlotsUniform.privateSlotT_disjoint hne l j)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [feedSlots_scratch, r.prefix_public _ (scratch_public ph')]
    simpa only [feedSlots_scratch] using hp.recWord
  · rw [feedSlots_scratch, r.prefixH _ (scratchT_lt ph') (scratchT_ne (Ne.symm hne))]
    simpa only [feedSlots_scratch] using hp.recH
  · intro j
    exact (hHhigh _ (cmp_ge j)).trans (hp.cmpH j)
  · intro j
    exact (hAhigh _ (cmp_ge j)).trans (hp.cmpA j)
  · intro j
    exact (hHhigh _ (normA_ge j)).trans (hp.nAH j)
  · intro j
    exact (hAhigh _ (normA_ge j)).trans (hp.nAA j)
  · intro j
    exact (hHhigh _ (normB_ge j)).trans (hp.nBH j)
  · intro j
    exact (hAhigh _ (normB_ge j)).trans (hp.nBA j)
  · intro j
    exact (hHhigh _ (word_ge j)).trans (hp.wH j)
  · intro j
    exact (hAhigh _ (word_ge j)).trans (hp.wA j)
  · intro j
    rw [hslotWidth, hHwidth]
    simpa only [hslotWidth] using hp.widthH j
  · rw [hslotWidth, hAwidth]
    simpa only [hslotWidth] using hp.widthBase
  · rw [hslotWidth, hAwidth]
    simpa only [hslotWidth] using hp.widthWide
  · intro j
    rw [hslotPrivate, hHprivate]
    simpa only [hslotPrivate] using hp.privateH j
  · intro j
    rw [hslotPrivate, hAprivate]
    simpa only [hslotPrivate] using hp.privateA j

end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedDockUniform
