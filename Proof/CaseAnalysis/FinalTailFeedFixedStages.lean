import Proof.CaseAnalysis.FinalTailFeed

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedFixedStages

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

noncomputable def fieldProgram (src dst : Fin bank) :=
  RecoveryFocus.machine (pairSlots src dst) Field.machine
noncomputable def rewindProgram (src drv log : Fin bank) :=
  RecoveryFocus.machine (triSlots src drv log) CompetitorRecordRewind.machine
noncomputable def normProgram (slots : Fin 5 → Fin bank) :=
  RecoveryFocus.machine slots ClockNormalize.machine
noncomputable def cmpProgram :=
  RecoveryFocus.machine cmpSlots CompetitorRationalDecision.machine

theorem norm_stage (slots : Fin 5 → Fin bank) (hi : Function.Injective slots)
    (width : ℕ) (bits : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (slots j) = 0)
    (hA : ∀ j, A (slots j) = ClockNormalize.input width bits j) :
    ∃ (A' : Fin bank → List Bool),
      Step (normProgram slots) (4*width+4) H A H A' ∧
      A' (slots 2) = frame (ClockNormalize.resize width bits) ∧
      A' (slots 0) = List.replicate width true ∧
      (∀ i, (∀ j, slots j ≠ i) → A' i = A i) := by
  refine ⟨_, normalize_dock_at slots hi width bits H A hH hA, ?_, ?_, ?_⟩
  · exact install_slot slots hi A (normalizeOut width bits) 2
  · exact install_slot slots hi A (normalizeOut width bits) 0
  · intro i hin
    exact install_other slots A (normalizeOut width bits) i hin

theorem field_stage (b : ℕ) (est : CompetitorValidity.Estimate) (count den : ℕ) (k : Fin 6)
    (src dst : Fin bank) (hne : src ≠ dst)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsrcH : H src = fieldCursor b est count den k) (hdstH : H dst = 0)
    (hsrcA : A src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den)
    (hdstA : A dst = []) :
    ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step (fieldProgram src dst) (2*(field b est count den k).length+1) H A H' A' ∧
      A' dst = frame (field b est count den k) ∧
      A' src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den ∧
      H' src = fieldCursor b est count den k + 2*(field b est count den k).length+1 ∧
      H' dst = 2*(field b est count den k).length+1 ∧
      (∀ i, src ≠ i → dst ≠ i → A' i = A i) ∧
      (∀ i, src ≠ i → dst ≠ i → H' i = H i) := by
  have hstep := field_dock b est count den k src dst hne H A hsrcH (by simp [hdstH, hdstA]) hsrcA
  refine ⟨_, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : install (pairSlots src dst) A
        ![CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den,
          A dst ++ frame (field b est count den k)] dst
        = A dst ++ frame (field b est count den k) := pairA1 src dst hne A _
    rw [h]
    simp [hdstA]
  · exact pairA0 src dst hne A _
  · exact pairH0 src dst hne H _
  · have h : dockH (pairSlots src dst) H
        ![fieldCursor b est count den k + 2*(field b est count den k).length+1,
          (A dst ++ frame (field b est count den k)).length] dst
        = (A dst ++ frame (field b est count den k)).length := pairH1 src dst hne H _
    rw [h]
    simp [hdstA]
  · intro i hs hd
    exact pairAout src dst A _ i hs hd
  · intro i hs hd
    exact pairHout src dst H _ i hs hd

theorem rewind_stage (src drv log : Fin bank) (hsd : src ≠ drv) (hsl : src ≠ log)
    (hdl : drv ≠ log) (C pos : ℕ) (hpos : pos ≤ C) (source : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsH : H src = pos) (hdH : H drv = 0) (hlH : H log = 0)
    (hsA : A src = source) (hdA : A drv = List.replicate C true) (hlA : A log = []) :
    ∃ (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step (rewindProgram src drv log) (2*C+2) H A H' A' ∧
      A' src = source ∧ A' drv = List.replicate C true ∧
      H' src = 0 ∧ H' drv = 0 ∧
      (∀ i, src ≠ i → drv ≠ i → log ≠ i → A' i = A i) ∧
      (∀ i, src ≠ i → drv ≠ i → log ≠ i → H' i = H i) := by
  have hinj := triSlots_injective src drv log hsd hsl hdl
  have hstep := (rewind_base source C pos hpos).dock (triSlots src drv log) hinj H A
    (by
      intro j
      fin_cases j
      · exact hsH
      · exact hdH
      · exact hlH)
    (by
      intro j
      fin_cases j
      · exact hsA
      · exact hdA
      · exact hlA)
  refine ⟨_, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact triA0 src drv log hsd hsl hdl A _
  · exact triA1 src drv log hsd hsl hdl A _
  · exact triH0 src drv log hsd hsl hdl H _
  · exact triH1 src drv log hsd hsl hdl H _
  · intro i h1 h2 h3
    exact triAout src drv log A _ i h1 h2 h3
  · intro i h1 h2 h3
    exact triHout src drv log H _ i h1 h2 h3

theorem cmp_stage (lower : Bool) (b p n d : ℕ) (q : ℚ)
    (hp : p < 2^b) (hn : n < 2^b) (hd : d < 2^b) (hdpos : 0 < d)
    (hq : 0 ≤ q) (hqn : CompetitorThresholdDecision.numerator q < 2^b) (hqd : q.den < 2^b)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (cmpSlots j) = 0)
    (hA : ∀ j, A (cmpSlots j) = CompetitorThresholdDecision.input lower b p n d q j) :
    ∃ (A' : Fin bank → List Bool),
      Step (cmpProgram) (2000*(b+1)^2) H A H A' ∧
      (readTapeBit (A' (cmpSlots 65)) 0 = true ↔
        CompetitorThresholdDecision.passes lower p n d q) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → A' i = A i) := by
  obtain ⟨out, hstep, hiff⟩ := compare_step lower b p n d q hp hn hd hdpos hq hqn hqd
    cmpSlots cmpSlots_injective H A hH hA
  refine ⟨_, hstep, ?_, ?_⟩
  · rw [compare_flag cmpSlots cmpSlots_injective A out]
    exact hiff
  · intro i hin
    exact compare_other cmpSlots A out i hin

end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedFixedStages
