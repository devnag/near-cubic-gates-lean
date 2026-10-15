import Proof.CaseAnalysis.FinalTailRecordFeedUniform
import Proof.CaseAnalysis.FinalDimensionWords
import Proof.Hierarchy.CompetitorThresholdConstants

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def phaseIndex : Phase → Fin 3
  | .penalty => 0
  | .moment => 1
  | .clause => 2

def widthSlot (ph : Phase) (j : Fin 2) : Fin bank :=
  ⟨2 + 2 * (phaseIndex ph).val + j.val, by
    have := (phaseIndex ph).isLt
    have := j.isLt
    unfold bank ext
    omega⟩

def privateSlot (ph : Phase) (j : Fin 29) : Fin bank :=
  ⟨15 + 29 * (phaseIndex ph).val + j.val, by
    have := (phaseIndex ph).isLt
    have := j.isLt
    unfold bank ext
    omega⟩

def dimensionSlots (ph : Phase) : Fin 19 → Fin bank :=
  ![widthSlot ph 1, privateSlot ph 0, privateSlot ph 1, privateSlot ph 2,
    privateSlot ph 3, privateSlot ph 4, privateSlot ph 5, privateSlot ph 6,
    privateSlot ph 7, privateSlot ph 8, privateSlot ph 9, privateSlot ph 10,
    privateSlot ph 11, privateSlot ph 12, privateSlot ph 13, cmpSlots 6,
    privateSlot ph 14, privateSlot ph 15, privateSlot ph 16]

def constantSlots (ph : Phase) (lower : Bool) : Fin 17 → Fin bank :=
  ![cmpSlots 6, widthSlot ph 1, privateSlot ph 17, cmpSlots (qnumSlot lower),
    privateSlot ph 18, privateSlot ph 19, privateSlot ph 20, privateSlot ph 21,
    cmpSlots (zeroSlot lower), privateSlot ph 22, privateSlot ph 23,
    privateSlot ph 24, privateSlot ph 25, cmpSlots (qdenSlot lower),
    privateSlot ph 26, privateSlot ph 27, privateSlot ph 28]

theorem widthSlot_range (ph : Phase) (j : Fin 2) :
    2 ≤ (widthSlot ph j).val ∧ (widthSlot ph j).val < 8 := by
  have := (phaseIndex ph).isLt
  have := j.isLt
  simp only [widthSlot]
  omega

theorem privateSlot_range (ph : Phase) (j : Fin 29) :
    15 ≤ (privateSlot ph j).val ∧ (privateSlot ph j).val < 102 := by
  have := (phaseIndex ph).isLt
  have := j.isLt
  simp only [privateSlot]
  omega

theorem privateSlot_injective (ph : Phase) : Function.Injective (privateSlot ph) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [privateSlot] at hv
  omega

theorem privateSlot_disjoint {ph ph' : Phase} (hne : ph ≠ ph') (i j : Fin 29) :
    privateSlot ph i ≠ privateSlot ph' j := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  cases ph <;> cases ph' <;> simp_all [privateSlot, phaseIndex] <;> omega

theorem dimensionSlots_injective (ph : Phase) : Function.Injective (dimensionSlots ph) := by
  cases ph <;> decide

theorem constantSlots_injective (ph : Phase) (lower : Bool) :
    Function.Injective (constantSlots ph lower) := by
  cases ph <;> cases lower <;> decide

theorem dimensionSlots_other (ph : Phase) (i : Fin bank)
    (hw : widthSlot ph 1 ≠ i) (hc : cmpSlots 6 ≠ i)
    (hp : ∀ j, privateSlot ph j ≠ i) : ∀ j, dimensionSlots ph j ≠ i := by
  intro j
  fin_cases j <;> first | exact hw | exact hc | exact hp _

theorem constantSlots_other (ph : Phase) (lower : Bool) (i : Fin bank)
    (hw : widthSlot ph 1 ≠ i) (hc : cmpSlots 6 ≠ i)
    (hn : cmpSlots (qnumSlot lower) ≠ i) (hz : cmpSlots (zeroSlot lower) ≠ i)
    (hd : cmpSlots (qdenSlot lower) ≠ i)
    (hp : ∀ j, privateSlot ph j ≠ i) : ∀ j, constantSlots ph lower j ≠ i := by
  intro j
  fin_cases j <;> first | exact hw | exact hc | exact hn | exact hz | exact hd | exact hp _

noncomputable def dimensionProgram (ph : Phase) :=
  RecoveryFocus.machine (dimensionSlots ph) CompetitorDimensions.machine

noncomputable def constantProgram (ph : Phase) (lower : Bool) (k : ℕ) (q : ℚ) :=
  RecoveryFocus.machine (constantSlots ph lower)
    (CompetitorThresholdConstants.machine k (CompetitorThresholdDecision.numerator q) q.den)

theorem dimension_stage (ph : Phase) (b : ℕ)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (dimensionSlots ph j) = 0)
    (hA : ∀ j, A (dimensionSlots ph j) = CompetitorDimensions.input (w b) j) :
    ∃ out : Fin 19 → List Bool,
      Step (dimensionProgram ph) (CompetitorDimensions.budget (w b)) H A H
        (install (dimensionSlots ph) A out) ∧
      out 0 = List.replicate (w b) true ∧ out 15 = List.replicate (w2 b) true := by
  obtain ⟨out, hr, h0, h15, _h17⟩ := CompetitorDimensions.dimensions_run (w b)
  have hstep := (step_of_clock hr).dock (dimensionSlots ph) (dimensionSlots_injective ph) H A hH hA
  rw [dockH_existing (dimensionSlots ph) H (fun _ => 0) hH] at hstep
  exact ⟨out, hstep, h0, h15⟩

theorem constant_stage (ph : Phase) (lower : Bool) (b k : ℕ) (q : ℚ)
    (hk : k ≤ w b) (hn : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (constantSlots ph lower j) = 0)
    (hA : ∀ j, A (constantSlots ph lower j) = CompetitorThresholdConstants.input (w b) j) :
    ∃ out : Fin 17 → List Bool,
      Step (constantProgram ph lower k q) (CompetitorThresholdConstants.budget (w b) k)
        H A H (install (constantSlots ph lower) A out) ∧
      out 0 = List.replicate (w2 b) true ∧ out 1 = List.replicate (w b) true ∧
      out 3 = NearCubicWires.RepairOrdinary.frame (SignedSortKey.binary (w2 b) (CompetitorThresholdDecision.numerator q)) ∧
      out 8 = NearCubicWires.RepairOrdinary.frame (SignedSortKey.binary (w2 b) 0) ∧
      out 13 = NearCubicWires.RepairOrdinary.frame (SignedSortKey.binary (w b) q.den) := by
  obtain ⟨out, hr, h0, h1, h3, h8, h13⟩ :=
    CompetitorThresholdConstants.constants_run (w b) k (CompetitorThresholdDecision.numerator q) q.den hk hn hd
  have hstep := (step_of_clock hr).dock (constantSlots ph lower)
    (constantSlots_injective ph lower) H A hH hA
  rw [dockH_existing (constantSlots ph lower) H (fun _ => 0) hH] at hstep
  exact ⟨out, hstep, h0, h1, h3, h8, h13⟩

end NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
