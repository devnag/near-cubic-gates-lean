import Proof.CaseAnalysis.FinalTailFeedPreserveUniform

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open LocalBitMultitape ExtDecompositionBatch CompetitorThresholdDecision
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TailAnd
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform (PublicPrefix)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedDockUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure ParkedThree' (bP bM bC : ℕ) (eP eM eC : CompetitorValidity.Estimate)
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool) : Prop where
  penalty : PhaseParked .penalty bP eP H A
  moment : PhaseParked .moment bM eM H A
  clause : PhaseParked .clause bC eC H A
  flagA : A tailFlag = []
  flagH : H tailFlag = 0
  spareA : A tailSpare = []
  spareH : H tailSpare = 0

def TailWidths' {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (bP bM bC : ℕ) : Prop :=
  numerator (meanThreshold constants) < 2^(w bP) ∧ (meanThreshold constants).den < 2^(w bP) ∧
  numerator (momentThreshold constants) < 2^(w bM) ∧ (momentThreshold constants).den < 2^(w bM) ∧
  numerator (acceptanceThreshold constants) < 2^(w bC) ∧ (acceptanceThreshold constants).den < 2^(w bC)

theorem tailWidths'_of {source : PointwisePCPPAlgorithm} (constants : Constants source)
    {bP bM bC : ℕ} (hP : thresholdWidth constants ≤ bP)
    (hM : thresholdWidth constants ≤ bM) (hC : thresholdWidth constants ≤ bC) :
    TailWidths' constants bP bM bC := by
  obtain ⟨hp, hpd, _, _, _, _⟩ := threshold_widths constants bP hP
  obtain ⟨_, _, hm, hmd, _, _⟩ := threshold_widths constants bM hM
  obtain ⟨_, _, _, _, hc, hcd⟩ := threshold_widths constants bC hC
  exact ⟨hp, hpd, hm, hmd, hc, hcd⟩

def tbud (W : ℕ) : ℕ :=
  (((C10TailFeedUniform.budget W + 1 + C10TailFeedUniform.budget W) + 1 +
    C10TailFeedUniform.budget W) + 1 + 4) + 1 + 4

theorem tbud_mono {W W' : ℕ} (h : W ≤ W') : tbud W ≤ tbud W' := by
  have := C10TailFeedUniform.budget_mono h
  unfold tbud
  omega

noncomputable def flagProgram :=
  RecoveryFocus.machine (pairT tailFlag tailSpare) (HierarchyFixedWord.machine [false])

noncomputable def andProgram :=
  and3 (feedSlots (phaseIndex .penalty) (cmpSlots 65))
    (feedSlots (phaseIndex .moment) (cmpSlots 65))
    (feedSlots (phaseIndex .clause) (cmpSlots 65)) tailFlag

noncomputable def program {sP sM sC : ℕ}
    (mP : Machine bank sP) (mM : Machine bank sM) (mC : Machine bank sC) :=
  Composition.machine
    (Composition.machine
      (Composition.machine (Composition.machine (docked .penalty mP) (docked .moment mM)) (docked .clause mC))
      flagProgram)
    andProgram

theorem tail_uniform_heads {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    ∃ (states : ℕ) (m : Machine tailBank states),
      ∀ (bP bM bC : ℕ) (eP eM eC : CompetitorValidity.Estimate),
        eP.Valid bP → eM.Valid bM → eC.Valid bC → TailWidths' constants bP bM bC →
        ∀ (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool), ParkedThree' bP bM bC eP eM eC H A →
        ∃ H' A', Step m (tbud (max bP (max bM bC))) H A H' A' ∧
          (readTapeBit (A' tailFlag) 0 = true ↔
            (estimate eP.positive eP.negative eP.denominator ≤ 2*zeta constants ∧
             estimate eM.positive eM.negative eM.denominator ≤ 1+zeta constants ∧
             midpoint constants ≤ estimate eC.positive eC.negative eC.denominator)) ∧
          (∀ i, PublicPrefix i → A' i = A i) ∧ H' tailFlag = 0 := by
  obtain ⟨sP, mP, hmP⟩ := C10TailFeedUniform.feed_uniform .penalty false (meanThreshold constants)
  obtain ⟨sM, mM, hmM⟩ := C10TailFeedUniform.feed_uniform .moment false (momentThreshold constants)
  obtain ⟨sC, mC, hmC⟩ := C10TailFeedUniform.feed_uniform .clause true (acceptanceThreshold constants)
  refine ⟨_, program mP mM mC, ?_⟩
  intro bP bM bC eP eM eC hvP hvM hvC hwidth H A hp
  obtain ⟨hpn, hpd, hmn, hmd, hcn, hcd⟩ := hwidth
  have hqP : (0 : ℚ) ≤ meanThreshold constants := by
    unfold meanThreshold
    exact mul_nonneg (by norm_num) (zeta_positive constants).le
  have hqM : (0 : ℚ) ≤ momentThreshold constants := by
    unfold momentThreshold
    linarith [zeta_positive constants]
  have hqC : (0 : ℚ) ≤ acceptanceThreshold constants := (midpoint_positive constants).le
  obtain ⟨H1, A1, hsP, rP⟩ := C10TailFeedDockUniform.feed_dock .penalty false (meanThreshold constants)
    mP hmP bP eP hvP hqP hpn hpd H A hp.penalty
  obtain ⟨H2, A2, hsM, rM⟩ := C10TailFeedDockUniform.feed_dock .moment false (momentThreshold constants)
    mM hmM bM eM hvM hqM hmn hmd H1 A1 (rP.parked_of (by intro h; cases h) hp.moment)
  obtain ⟨H3, A3, hsC, rC⟩ := C10TailFeedDockUniform.feed_dock .clause true (acceptanceThreshold constants)
    mC hmC bC eC hvC hqC hcn hcd H2 A2
      (rM.parked_of (by intro h; cases h) (rP.parked_of (by intro h; cases h) hp.clause))
  have hOtherA (i : Fin tailBank) (hi : ∀ ph j, feedSlots (phaseIndex ph) j ≠ i) : A3 i = A i :=
    (rC.otherA i (hi .clause)).trans ((rM.otherA i (hi .moment)).trans (rP.otherA i (hi .penalty)))
  have hOtherH (i : Fin tailBank) (hi : ∀ ph j, feedSlots (phaseIndex ph) j ≠ i) : H3 i = H i :=
    (rC.otherH i (hi .clause)).trans ((rM.otherH i (hi .moment)).trans (rP.otherH i (hi .penalty)))
  have hflagH : H3 tailFlag = 0 :=
    (hOtherH _ (fun ph j => feedSlots_ne_flag (phaseIndex ph) j)).trans hp.flagH
  have hspareH : H3 tailSpare = 0 :=
    (hOtherH _ (fun ph j => feedSlots_ne_spare (phaseIndex ph) j)).trans hp.spareH
  have hflagA : A3 tailFlag = [] :=
    (hOtherA _ (fun ph j => feedSlots_ne_flag (phaseIndex ph) j)).trans hp.flagA
  have hspareA : A3 tailSpare = [] :=
    (hOtherA _ (fun ph j => feedSlots_ne_spare (phaseIndex ph) j)).trans hp.spareA
  have hinit := flag_init H3 A3 hflagH hspareH hflagA hspareA
  let A4 := install (pairT tailFlag tailSpare) A3 ![[false], List.replicate 1 false]
  have hA4flag : A4 tailFlag = [false] :=
    install_slot (pairT tailFlag tailSpare) (pairT_injective _ _ flag_ne_spare) A3 _ 0
  have hA4feed (ph : Phase) : A4 (feedSlots (phaseIndex ph) (cmpSlots 65)) =
      A3 (feedSlots (phaseIndex ph) (cmpSlots 65)) :=
    install_other _ _ _ _ (pairT_ne (feedSlots_ne_flag (phaseIndex ph) (cmpSlots 65)).symm
      (feedSlots_ne_spare (phaseIndex ph) (cmpSlots 65)).symm)
  have hPhead : H3 (feedSlots (phaseIndex .penalty) (cmpSlots 65)) = 0 := by
    rw [rC.other_cmpH .penalty (by intro h; cases h) 65, rM.other_cmpH .penalty (by intro h; cases h) 65]
    exact rP.flagHead
  have hMhead : H3 (feedSlots (phaseIndex .moment) (cmpSlots 65)) = 0 := by
    rw [rC.other_cmpH .moment (by intro h; cases h) 65]
    exact rM.flagHead
  obtain ⟨A5, hand, hiff, hAndFrame⟩ := and3_step_frame
    (feedSlots (phaseIndex .penalty) (cmpSlots 65)) (feedSlots (phaseIndex .moment) (cmpSlots 65))
    (feedSlots (phaseIndex .clause) (cmpSlots 65)) tailFlag H3 A4 hPhead hMhead rC.flagHead hflagH hA4flag
  have hsP' := Step.enlarge hsP (C10TailFeedUniform.budget_mono (le_max_left bP (max bM bC)))
  have hsM' := Step.enlarge hsM (C10TailFeedUniform.budget_mono
    ((le_max_left bM bC).trans (le_max_right bP (max bM bC))))
  have hsC' := Step.enlarge hsC (C10TailFeedUniform.budget_mono
    ((le_max_right bM bC).trans (le_max_right bP (max bM bC))))
  refine ⟨H3, A5, (((hsP'.seq hsM').seq hsC').seq hinit).seq hand, ?_, ?_, hflagH⟩
  · have hPbit : (readTapeBit (A4 (feedSlots (phaseIndex .penalty) (cmpSlots 65))) 0 = true ↔
        estimate eP.positive eP.negative eP.denominator ≤ 2*zeta constants) := by
      rw [hA4feed, rC.other_cmpA .penalty (by intro h; cases h) 65, rM.other_cmpA .penalty (by intro h; cases h) 65]
      exact rP.flag.trans (passes_false _ _ _ _)
    have hMbit : (readTapeBit (A4 (feedSlots (phaseIndex .moment) (cmpSlots 65))) 0 = true ↔
        estimate eM.positive eM.negative eM.denominator ≤ 1+zeta constants) := by
      rw [hA4feed, rC.other_cmpA .moment (by intro h; cases h) 65]
      exact rM.flag.trans (passes_false _ _ _ _)
    have hCbit : (readTapeBit (A4 (feedSlots (phaseIndex .clause) (cmpSlots 65))) 0 = true ↔
        midpoint constants ≤ estimate eC.positive eC.negative eC.denominator) := by
      rw [hA4feed]
      exact rC.flag.trans (passes_true _ _ _ _)
    exact hiff.trans (and_congr hPbit (and_congr hMbit hCbit))
  · intro i hi
    have hif : i ≠ tailFlag := by intro h; have he := congrArg Fin.val h; have := hi.1; change i.val = 473 at he; omega
    have his : i ≠ tailSpare := by intro h; have he := congrArg Fin.val h; have := hi.1; change i.val = 474 at he; omega
    rw [hAndFrame i hif]
    have hA4 : A4 i = A3 i := install_other _ _ _ _ (pairT_ne hif.symm his.symm)
    exact hA4.trans ((rC.prefix_public i hi).trans ((rM.prefix_public i hi).trans (rP.prefix_public i hi)))

theorem tail_uniform {source : PointwisePCPPAlgorithm} (constants : Constants source) :
    ∃ (states : ℕ) (m : Machine tailBank states),
      ∀ (bP bM bC : ℕ) (eP eM eC : CompetitorValidity.Estimate),
        eP.Valid bP → eM.Valid bM → eC.Valid bC → TailWidths' constants bP bM bC →
        ∀ (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool), ParkedThree' bP bM bC eP eM eC H A →
        ∃ H' A', Step m (tbud (max bP (max bM bC))) H A H' A' ∧
          (readTapeBit (A' tailFlag) 0 = true ↔
            (estimate eP.positive eP.negative eP.denominator ≤ 2*zeta constants ∧
             estimate eM.positive eM.negative eM.denominator ≤ 1+zeta constants ∧
             midpoint constants ≤ estimate eC.positive eC.negative eC.denominator)) ∧
          (∀ i, PublicPrefix i → A' i = A i) := by
  obtain ⟨states, m, hm⟩ := tail_uniform_heads constants
  refine ⟨states, m, ?_⟩
  intro bP bM bC eP eM eC hvP hvM hvC hwidth H A hpark
  obtain ⟨H', A', hrun, hiff, hframe, _hhead⟩ :=
    hm bP bM bC eP eM eC hvP hvM hvC hwidth H A hpark
  exact ⟨H', A', hrun, hiff, hframe⟩

end NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform
