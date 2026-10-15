import Proof.CaseAnalysis.FinalTailSlots
import Proof.CaseAnalysis.FinalCompareDockCmp
import Proof.Hierarchy.CompetitorThresholdDecision

/-! **Decision tail, stage 2b-ii(prep) — the facts the comparator feed needs.**

Paper C.10: three tests on three estimated reals. The physical comparator reads
its four numerators and two denominators from fixed tapes whose ASSIGNMENT
depends on the test direction (`numbers lower p n q`). Here that assignment is
made explicit per operand, the six record-field cursors are computed, a bare
framed-word copy is docked, and the width facts that let the record's
`width W` operands feed a comparator of parameter `width W` are proved. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorMonomialStream
open CompetitorThresholdDecision SignedSortKey ClockNormalize
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockCmp
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairOrdinary.RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### Where each operand goes (`numbers lower p n q`, `leftDenominator`, `rightDenominator`) -/

/-- The comparator tape holding `p`. -/
def posSlot (lower : Bool) : Fin 67 := if lower then 0 else 2
/-- ... `n`. -/
def negSlot (lower : Bool) : Fin 67 := if lower then 1 else 3
/-- ... `numerator q`. -/
def qnumSlot (lower : Bool) : Fin 67 := if lower then 2 else 0
/-- ... the literal `0`. -/
def zeroSlot (lower : Bool) : Fin 67 := if lower then 3 else 1
/-- ... `d` (the estimate's denominator). -/
def denSlot (lower : Bool) : Fin 67 := if lower then 4 else 5
/-- ... `q.den`. -/
def qdenSlot (lower : Bool) : Fin 67 := if lower then 5 else 4

/-- The comparator's input, read back through those names. -/
theorem input_pos (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (posSlot lower) = frame (binary (CompetitorRationalDecision.width b) p) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, posSlot,
    CompetitorRationalProducts.input, numbers]
theorem input_neg (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (negSlot lower) = frame (binary (CompetitorRationalDecision.width b) n) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, negSlot,
    CompetitorRationalProducts.input, numbers]
theorem input_qnum (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (qnumSlot lower) =
      frame (binary (CompetitorRationalDecision.width b) (numerator q)) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, qnumSlot,
    CompetitorRationalProducts.input, numbers]
theorem input_zero (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (zeroSlot lower) = frame (binary (CompetitorRationalDecision.width b) 0) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, zeroSlot,
    CompetitorRationalProducts.input, numbers]
theorem input_den (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (denSlot lower) = frame (binary b d) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, denSlot,
    CompetitorRationalProducts.input, leftDenominator, rightDenominator]
theorem input_qden (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q (qdenSlot lower) = frame (binary b q.den) := by
  cases lower <;> simp [CompetitorThresholdDecision.input, qdenSlot,
    CompetitorRationalProducts.input, leftDenominator, rightDenominator]
theorem input_driver (lower : Bool) (b p n d : ℕ) (q : ℚ) :
    input lower b p n d q 6 = List.replicate (CompetitorRationalDecision.width b) true := by
  cases lower <;> simp [CompetitorThresholdDecision.input, CompetitorRationalProducts.input]
theorem input_blank (lower : Bool) (b p n d : ℕ) (q : ℚ) (j : Fin 67) (hj : 7 ≤ j.val) :
    input lower b p n d q j = [] := by
  cases lower <;> simp [CompetitorThresholdDecision.input, CompetitorRationalProducts.input,
    show ¬ j.val < 4 by omega, show j.val ≠ 4 by omega, show j.val ≠ 5 by omega,
    show j.val ≠ 6 by omega]

/-! ### The six field cursors of a record -/

theorem fieldCursor_zero (b : ℕ) (q : CompetitorValidity.Estimate) (c d : ℕ) :
    fieldCursor b q c d 0 = 0 := by simp [fieldCursor, allFields, fieldStream]
theorem fieldCursor_succ (b : ℕ) (q : CompetitorValidity.Estimate) (c d : ℕ) (k : Fin 6)
    (hk : k.val + 1 < 6) :
    fieldCursor b q c d ⟨k.val+1, hk⟩ = fieldCursor b q c d k + 2*(field b q c d k).length + 1 := by
  fin_cases k <;> simp [fieldCursor, allFields, fieldStream, field, List.length_append,
    frame_length] <;> omega

/-! ### A bare framed-word copy, docked -/

/-- Copy `frame bits` (alone on `src`, head `0`) onto blank `dst`. -/
theorem frame_dock (bits : List Bool) (src dst : Fin bank) (hne : src ≠ dst)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsrcH : H src = 0) (hdstH : H dst = 0) (hsrcA : A src = frame bits) (hdstA : A dst = []) :
    Step (RecoveryFocus.machine (pairSlots src dst) Field.machine) (2*bits.length+1) H A
      (dockH (pairSlots src dst) H ![2*bits.length+1, (frame bits).length])
      (install (pairSlots src dst) A ![frame bits, frame bits]) := by
  have h := (field_step_split [] bits [] []).dock (pairSlots src dst)
    (pairSlots_injective src dst hne) H A
    (by intro j; fin_cases j <;> simp [pairSlots, hsrcH, hdstH])
    (by intro j; fin_cases j <;> simp [pairSlots, hsrcA, hdstA])
  simpa using h

/-! ### Width facts: the record's `width W` operands feed a comparator of parameter `width W` -/

theorem width_le_width (x : ℕ) : x ≤ CompetitorRationalDecision.width x := by
  unfold CompetitorRationalDecision.width; omega
theorem lt_pow_width {x W : ℕ} (h : x < 2^W) : x < 2^(CompetitorRationalDecision.width W) :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (width_le_width W))
/-- A `width W` word widened to `width (width W)`. -/
theorem widen (W p : ℕ) (hp : p < 2^W) :
    frame (ClockNormalize.resize (CompetitorRationalDecision.width (CompetitorRationalDecision.width W))
      (binary (CompetitorRationalDecision.width W) p)) =
    frame (binary (CompetitorRationalDecision.width (CompetitorRationalDecision.width W)) p) :=
  frame_resize_binary _ _ p (lt_pow_width hp) (width_le_width _)

/-! ### Shared by T1 (`feed_exists`) and T2 (`tail_step`) -/

/-- Widths: the record is at `W`; the comparator's parameter is `w := width W`,
so its numerators are at `w2 := width w`. -/
abbrev w (W : ℕ) : ℕ := CompetitorRationalDecision.width W
abbrev w2 (W : ℕ) : ℕ := CompetitorRationalDecision.width (w W)

/-- The whole bank is blank-and-parked outside the record: all block heads `0`,
all block tapes `[]`, the record on `scratch ph` with its head at `0`. -/
structure Parked (ph : CloseoutRowsOriginalSchedule.Phase) (W : ℕ)
    (est : CompetitorValidity.Estimate) (H : Fin bank → ℕ) (A : Fin bank → List Bool) : Prop where
  recWord : A (scratch ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord (w W) est 1 1
  recH : H (scratch ph) = 0
  cmpH : ∀ j, H (cmpSlots j) = 0
  cmpA : ∀ j, A (cmpSlots j) = []
  nAH : ∀ j, H (normSlots j) = 0
  nAA : ∀ j, A (normSlots j) = []
  nBH : ∀ j, H (normSlotsB j) = 0
  nBA : ∀ j, A (normSlotsB j) = []
  wH : ∀ j, H (wordSlots j) = 0
  wA : ∀ j, A (wordSlots j) = []

/-! ### Slot disjointness, once -/

theorem scratch_lt (ph : CloseoutRowsOriginalSchedule.Phase) : (scratch ph).val < 221 := by
  cases ph <;> simp [scratch]
theorem cmp_ne_scratch (ph) (j : Fin 67) : cmpSlots j ≠ scratch ph := by
  cases ph <;> simp [cmpSlots, scratch, Fin.ext_iff] <;> omega
theorem normA_ne_scratch (ph) (j : Fin 5) : normSlots j ≠ scratch ph := by
  cases ph <;> simp [normSlots, scratch, Fin.ext_iff] <;> omega
theorem normB_ne_scratch (ph) (j : Fin 5) : normSlotsB j ≠ scratch ph := by
  cases ph <;> simp [normSlotsB, scratch, Fin.ext_iff] <;> omega
theorem word_ne_scratch (ph) (j : Fin 6) : wordSlots j ≠ scratch ph := by
  cases ph <;> simp [wordSlots, scratch, Fin.ext_iff] <;> omega
theorem cmp_ne_normA (i : Fin 67) (j : Fin 5) : cmpSlots i ≠ normSlots j := by
  simp [cmpSlots, normSlots, Fin.ext_iff]; omega
theorem cmp_ne_normB (i : Fin 67) (j : Fin 5) : cmpSlots i ≠ normSlotsB j := by
  simp [cmpSlots, normSlotsB, Fin.ext_iff]; omega
theorem cmp_ne_word (i : Fin 67) (j : Fin 6) : cmpSlots i ≠ wordSlots j := by
  simp [cmpSlots, wordSlots, Fin.ext_iff]; omega
theorem normA_ne_normB (i j : Fin 5) : normSlots i ≠ normSlotsB j := by
  simp [normSlots, normSlotsB, Fin.ext_iff]; omega
theorem normA_ne_word (i : Fin 5) (j : Fin 6) : normSlots i ≠ wordSlots j := by
  simp [normSlots, wordSlots, Fin.ext_iff]; omega
theorem normB_ne_word (i : Fin 5) (j : Fin 6) : normSlotsB i ≠ wordSlots j := by
  simp [normSlotsB, wordSlots, Fin.ext_iff]; omega

/-! ### The three comparator operands from a valid estimate -/

theorem pos_lt (W : ℕ) (est : CompetitorValidity.Estimate) (hv : est.Valid W) :
    est.positive < 2^(w W) := lt_pow_width hv.positive
theorem neg_lt (W : ℕ) (est : CompetitorValidity.Estimate) (hv : est.Valid W) :
    est.negative < 2^(w W) := lt_pow_width hv.negative
theorem den_lt (W : ℕ) (est : CompetitorValidity.Estimate) (hv : est.Valid W) :
    est.denominator < 2^(w W) := lt_pow_width hv.denominator

end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
