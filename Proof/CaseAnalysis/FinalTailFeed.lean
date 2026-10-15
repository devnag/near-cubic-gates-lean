import Proof.CaseAnalysis.FinalTailFeedPrep
import Proof.Hierarchy.CompetitorRecordRewind

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailFeed

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
noncomputable section

/-! ### Widths -/

/-- The comparator's numerator width: one `width` above the record's. -/
abbrev w3 (W : ℕ) : ℕ := CompetitorRationalDecision.width (w2 W)

theorem w3_eq (W : ℕ) : w3 W = 2*(w2 W)+2 := rfl

/-- A framed `w2 W`-bit word is short enough for the `w3 W` unary rewind driver. -/
theorem frame_le_w3 (W : ℕ) : 2*(w2 W)+1 ≤ w3 W := by
  have h := w3_eq W
  omega

/-! ### Three- and five-tape docking maps -/

/-- A three-tape docking map. -/
def triSlots (a b c : Fin bank) (i : Fin 3) : Fin bank :=
  if i.val = 0 then a else if i.val = 1 then b else c

theorem triSlots_injective (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (triSlots a b c) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (show a = b from h) hab
  · exact absurd (show a = c from h) hac
  · exact absurd (show b = a from h).symm hab
  · rfl
  · exact absurd (show b = c from h) hbc
  · exact absurd (show c = a from h).symm hac
  · exact absurd (show c = b from h).symm hbc
  · rfl

/-- A five-tape docking map. -/
def quintSlots (a b c d e : Fin bank) (i : Fin 5) : Fin bank :=
  if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c
  else if i.val = 3 then d else e

theorem quintSlots_injective (a b c d e : Fin bank)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective (quintSlots a b c d e) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (show a = b from h) hab
  · exact absurd (show a = c from h) hac
  · exact absurd (show a = d from h) had
  · exact absurd (show a = e from h) hae
  · exact absurd (show b = a from h).symm hab
  · rfl
  · exact absurd (show b = c from h) hbc
  · exact absurd (show b = d from h) hbd
  · exact absurd (show b = e from h) hbe
  · exact absurd (show c = a from h).symm hac
  · exact absurd (show c = b from h).symm hbc
  · rfl
  · exact absurd (show c = d from h) hcd
  · exact absurd (show c = e from h) hce
  · exact absurd (show d = a from h).symm had
  · exact absurd (show d = b from h).symm hbd
  · exact absurd (show d = c from h).symm hcd
  · rfl
  · exact absurd (show d = e from h) hde
  · exact absurd (show e = a from h).symm hae
  · exact absurd (show e = b from h).symm hbe
  · exact absurd (show e = c from h).symm hce
  · exact absurd (show e = d from h).symm hde
  · rfl

/-! ### Port projections of the two-tape and three-tape docks -/

theorem pairA0 (src dst : Fin bank) (hne : src ≠ dst) (A : Fin bank → List Bool)
    (v : Fin 2 → List Bool) : install (pairSlots src dst) A v src = v 0 :=
  install_slot (pairSlots src dst) (pairSlots_injective src dst hne) A v 0

theorem pairA1 (src dst : Fin bank) (hne : src ≠ dst) (A : Fin bank → List Bool)
    (v : Fin 2 → List Bool) : install (pairSlots src dst) A v dst = v 1 :=
  install_slot (pairSlots src dst) (pairSlots_injective src dst hne) A v 1

theorem pairAout (src dst : Fin bank) (A : Fin bank → List Bool) (v : Fin 2 → List Bool)
    (i : Fin bank) (h0 : src ≠ i) (h1 : dst ≠ i) :
    install (pairSlots src dst) A v i = A i := by
  refine install_other (pairSlots src dst) A v i ?_
  intro j
  fin_cases j
  · exact h0
  · exact h1

theorem pairH0 (src dst : Fin bank) (hne : src ≠ dst) (H : Fin bank → ℕ) (v : Fin 2 → ℕ) :
    dockH (pairSlots src dst) H v src = v 0 :=
  dockH_slot (pairSlots src dst) (pairSlots_injective src dst hne) H v 0

theorem pairH1 (src dst : Fin bank) (hne : src ≠ dst) (H : Fin bank → ℕ) (v : Fin 2 → ℕ) :
    dockH (pairSlots src dst) H v dst = v 1 :=
  dockH_slot (pairSlots src dst) (pairSlots_injective src dst hne) H v 1

theorem pairHout (src dst : Fin bank) (H : Fin bank → ℕ) (v : Fin 2 → ℕ)
    (i : Fin bank) (h0 : src ≠ i) (h1 : dst ≠ i) :
    dockH (pairSlots src dst) H v i = H i := by
  refine dockH_other (pairSlots src dst) H v i ?_
  intro j
  fin_cases j
  · exact h0
  · exact h1

theorem triA0 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A : Fin bank → List Bool) (v : Fin 3 → List Bool) :
    install (triSlots a b c) A v a = v 0 :=
  install_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) A v 0

theorem triA1 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A : Fin bank → List Bool) (v : Fin 3 → List Bool) :
    install (triSlots a b c) A v b = v 1 :=
  install_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) A v 1

theorem triAout (a b c : Fin bank) (A : Fin bank → List Bool) (v : Fin 3 → List Bool)
    (i : Fin bank) (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    install (triSlots a b c) A v i = A i := by
  refine install_other (triSlots a b c) A v i ?_
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

theorem triH0 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (H : Fin bank → ℕ) (v : Fin 3 → ℕ) : dockH (triSlots a b c) H v a = v 0 :=
  dockH_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) H v 0

theorem triH1 (a b c : Fin bank) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (H : Fin bank → ℕ) (v : Fin 3 → ℕ) : dockH (triSlots a b c) H v b = v 1 :=
  dockH_slot (triSlots a b c) (triSlots_injective a b c hab hac hbc) H v 1

theorem triHout (a b c : Fin bank) (H : Fin bank → ℕ) (v : Fin 3 → ℕ)
    (i : Fin bank) (ha : a ≠ i) (hb : b ≠ i) (hc : c ≠ i) :
    dockH (triSlots a b c) H v i = H i := by
  refine dockH_other (triSlots a b c) H v i ?_
  intro j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

/-! ### The five stage forms, each stated by PORT PROJECTION -/

/-- **Stage — one literal word.** `w0` receives `bits`; heads are untouched. -/
theorem lit_stage (bits : List Bool) (w0 w1 : Fin bank) (hne : w0 ≠ w1)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (h0 : H w0 = 0) (h1 : H w1 = 0) (a0 : A w0 = []) (a1 : A w1 = []) :
    ∃ (s : ℕ) (m : Machine bank s) (A' : Fin bank → List Bool),
      Step m (2*bits.length+2) H A H A' ∧ A' w0 = bits ∧
      (∀ i, w0 ≠ i → w1 ≠ i → A' i = A i) := by
  refine ⟨_, _, _, literal_dock bits w0 w1 hne H A h0 h1 a0 a1, ?_, ?_⟩
  · exact pairA0 w0 w1 hne A _
  · intro i hi0 hi1
    exact pairAout w0 w1 A _ i hi0 hi1

/-- **Stage — widen one framed word.** Tape `2` of the block receives the widened
word, tape `0` keeps the driver; heads are untouched. -/
theorem norm_stage (slots : Fin 5 → Fin bank) (hi : Function.Injective slots)
    (width : ℕ) (bits : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (slots j) = 0)
    (hA : ∀ j, A (slots j) = ClockNormalize.input width bits j) :
    ∃ (s : ℕ) (m : Machine bank s) (A' : Fin bank → List Bool),
      Step m (4*width+4) H A H A' ∧
      A' (slots 2) = frame (ClockNormalize.resize width bits) ∧
      A' (slots 0) = List.replicate width true ∧
      (∀ i, (∀ j, slots j ≠ i) → A' i = A i) := by
  refine ⟨_, _, _, normalize_dock_at slots hi width bits H A hH hA, ?_, ?_, ?_⟩
  · exact install_slot slots hi A (normalizeOut width bits) 2
  · exact install_slot slots hi A (normalizeOut width bits) 0
  · intro i hin
    exact install_other slots A (normalizeOut width bits) i hin

/-- **Stage — lift field `k` of a record onto a blank tape.** The record survives;
both heads advance past the copy. -/
theorem field_stage (b : ℕ) (est : CompetitorValidity.Estimate) (count den : ℕ) (k : Fin 6)
    (src dst : Fin bank) (hne : src ≠ dst)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsrcH : H src = fieldCursor b est count den k) (hdstH : H dst = 0)
    (hsrcA : A src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den)
    (hdstA : A dst = []) :
    ∃ (s : ℕ) (m : Machine bank s) (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step m (2*(field b est count den k).length+1) H A H' A' ∧
      A' dst = frame (field b est count den k) ∧
      A' src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b est count den ∧
      H' src = fieldCursor b est count den k + 2*(field b est count den k).length+1 ∧
      H' dst = 2*(field b est count den k).length+1 ∧
      (∀ i, src ≠ i → dst ≠ i → A' i = A i) ∧
      (∀ i, src ≠ i → dst ≠ i → H' i = H i) := by
  have hstep := field_dock b est count den k src dst hne H A hsrcH (by simp [hdstH, hdstA]) hsrcA
  refine ⟨_, _, _, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- One paid head reset, raw: the record rewinder walks the head on tape `0` back
to `0` against a unary driver of length `C`, changing no word. -/
theorem rewind_base (source : List Bool) (C pos : ℕ) (hpos : pos ≤ C) :
    Step CompetitorRecordRewind.machine (2*C+2)
      ![pos, 0, 0] ![source, List.replicate C true, []]
      ![0, 0, 0] ![source, List.replicate C true, List.replicate C false] := by
  obtain ⟨r, hr, hf, _⟩ := CompetitorRecordRewind.rewind_run source C pos hpos
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]
    rfl
  · rw [hf]
    rfl

/-- **Stage — one paid head reset**, docked at `src` with driver `drv` and log
`log`. The word and the driver survive; both their heads return to `0`. -/
theorem rewind_stage (src drv log : Fin bank) (hsd : src ≠ drv) (hsl : src ≠ log)
    (hdl : drv ≠ log) (C pos : ℕ) (hpos : pos ≤ C) (source : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsH : H src = pos) (hdH : H drv = 0) (hlH : H log = 0)
    (hsA : A src = source) (hdA : A drv = List.replicate C true) (hlA : A log = []) :
    ∃ (s : ℕ) (m : Machine bank s) (H' : Fin bank → ℕ) (A' : Fin bank → List Bool),
      Step m (2*C+2) H A H' A' ∧
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
  refine ⟨_, _, _, _, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact triA0 src drv log hsd hsl hdl A _
  · exact triA1 src drv log hsd hsl hdl A _
  · exact triH0 src drv log hsd hsl hdl H _
  · exact triH1 src drv log hsd hsl hdl H _
  · intro i h1 h2 h3
    exact triAout src drv log A _ i h1 h2 h3
  · intro i h1 h2 h3
    exact triHout src drv log H _ i h1 h2 h3

/-- **Stage — the comparator.** Heads are untouched; the verdict sits on slot 65. -/
theorem cmp_stage (lower : Bool) (b p n d : ℕ) (q : ℚ)
    (hp : p < 2^b) (hn : n < 2^b) (hd : d < 2^b) (hdpos : 0 < d)
    (hq : 0 ≤ q) (hqn : CompetitorThresholdDecision.numerator q < 2^b) (hqd : q.den < 2^b)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (cmpSlots j) = 0)
    (hA : ∀ j, A (cmpSlots j) = CompetitorThresholdDecision.input lower b p n d q j) :
    ∃ (s : ℕ) (m : Machine bank s) (A' : Fin bank → List Bool),
      Step m (2000*(b+1)^2) H A H A' ∧
      (readTapeBit (A' (cmpSlots 65)) 0 = true ↔
        CompetitorThresholdDecision.passes lower p n d q) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → A' i = A i) := by
  obtain ⟨out, hstep, hiff⟩ := compare_step lower b p n d q hp hn hd hdpos hq hqn hqd
    cmpSlots cmpSlots_injective H A hH hA
  refine ⟨_, _, _, hstep, ?_, ?_⟩
  · rw [compare_flag cmpSlots cmpSlots_injective A out]
    exact hiff
  · intro i hin
    exact compare_other cmpSlots A out i hin

/-! ### The three record fields the comparator needs, and their cursors -/

theorem field_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 0 = binary (w2 W) est.positive := rfl
theorem field_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 1 = binary (w2 W) est.negative := rfl
theorem field_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    field (w W) est 1 1 2 = binary (w2 W) est.denominator := rfl

theorem field_pos_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 0).length = w2 W := by
  rw [field_pos, binary_length]
theorem field_neg_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 1).length = w2 W := by
  rw [field_neg, binary_length]
theorem field_den_length (W : ℕ) (est : CompetitorValidity.Estimate) :
    (field (w W) est 1 1 2).length = w2 W := by
  rw [field_den, binary_length]

theorem cursor_pos (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 0 = 0 := fieldCursor_zero (w W) est 1 1

theorem cursor_neg (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 1 = 2*(w2 W)+1 := by
  have h : fieldCursor (w W) est 1 1 1
      = fieldCursor (w W) est 1 1 0 + 2*(field (w W) est 1 1 0).length + 1 :=
    fieldCursor_succ (w W) est 1 1 0 (by decide)
  rw [h, cursor_pos, field_pos_length, Nat.zero_add]

theorem cursor_den (W : ℕ) (est : CompetitorValidity.Estimate) :
    fieldCursor (w W) est 1 1 2 = 4*(w2 W)+2 := by
  have h : fieldCursor (w W) est 1 1 2
      = fieldCursor (w W) est 1 1 1 + 2*(field (w W) est 1 1 1).length + 1 :=
    fieldCursor_succ (w W) est 1 1 1 (by decide)
  rw [h, cursor_neg, field_neg_length]
  omega

/-! ### The seven comparator input tapes -/

theorem posSlot_lt (lower : Bool) : (posSlot lower).val < 7 := by cases lower <;> decide
theorem negSlot_lt (lower : Bool) : (negSlot lower).val < 7 := by cases lower <;> decide
theorem qnumSlot_lt (lower : Bool) : (qnumSlot lower).val < 7 := by cases lower <;> decide
theorem zeroSlot_lt (lower : Bool) : (zeroSlot lower).val < 7 := by cases lower <;> decide
theorem denSlot_lt (lower : Bool) : (denSlot lower).val < 7 := by cases lower <;> decide
theorem qdenSlot_lt (lower : Bool) : (qdenSlot lower).val < 7 := by cases lower <;> decide
theorem val65 : (65 : Fin 67).val = 65 := rfl

/-- Below `7` the comparator's block is exactly its six operands and its driver. -/
theorem slot_cover (lower : Bool) (j : Fin 67) (hj : j.val < 7) :
    j = posSlot lower ∨ j = negSlot lower ∨ j = qnumSlot lower ∨ j = zeroSlot lower ∨
      j = denSlot lower ∨ j = qdenSlot lower ∨ j = 6 := by
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨
      j.val = 6 := by omega
  cases lower
  · rcases h with h|h|h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))))
  · rcases h with h|h|h|h|h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))))

/-- **One phase, one test.** From a parked bank, the comparator's verdict on the
record's estimate against threshold `q` in direction `lower`. The machine is the
thirteen-stage sequence; its budget depends only on the widths. -/
theorem feed_exists (ph : CloseoutRowsOriginalSchedule.Phase) (lower : Bool) (q : ℚ) (W : ℕ)
    (est : CompetitorValidity.Estimate) (hv : est.Valid W)
    (hq : 0 ≤ q) (hqnum : numerator q < 2^(w W)) (hqden : q.den < 2^(w W))
    (H : Fin bank → ℕ) (A : Fin bank → List Bool) (hp : Parked ph W est H A) :
    ∃ (states : ℕ) (m : Machine bank states) (budget : ℕ) (H' : Fin bank → ℕ)
      (A' : Fin bank → List Bool),
      Step m budget H A H' A' ∧
      (readTapeBit (A' (cmpSlots 65)) 0 = true ↔
        passes lower est.positive est.negative est.denominator q) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) → (∀ j, normSlotsB j ≠ i) →
        (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → A' i = A i) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) → (∀ j, normSlotsB j ≠ i) →
        (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → H' i = H i) ∧
      H' (cmpSlots 65) = 0 ∧
      A' (scratch ph) = A (scratch ph) := by
  classical
  -- ## Widths at the comparator's parameter `b := w2 W`
  have hposb : est.positive < 2^(w2 W) := lt_pow_width (pos_lt W est hv)
  have hnegb : est.negative < 2^(w2 W) := lt_pow_width (neg_lt W est hv)
  have hdenb : est.denominator < 2^(w2 W) := lt_pow_width (den_lt W est hv)
  have hqnb : numerator q < 2^(w2 W) := lt_pow_width hqnum
  have hqdb : q.den < 2^(w2 W) := lt_pow_width hqden
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
  -- ## Stage 1 — the unary width driver on the comparator's own tape 6
  obtain ⟨_, _, A1, st1, hA1drv, hA1o⟩ :=
    lit_stage (List.replicate (w3 W) true) (cmpSlots 6) (wordSlots 0)
      (cmp_ne_word 6 0) H A (hp.cmpH 6) (hp.wH 0) (hp.cmpA 6) (hp.wA 0)
  -- ## Stage 2 — lift the record's positive part onto normaliser block A, tape 1
  obtain ⟨_, _, H2, A2, st2, hA2dst, hA2src, hH2src, hH2dst, hA2o, hH2o⟩ :=
    field_stage (w W) est 1 1 0 (scratch ph) (normSlots 1) ((normA_ne_scratch ph 1).symm)
      H A1 (by rw [hp.recH, cursor_pos]) (hp.nAH 1)
      ((hA1o (scratch ph) (cmp_ne_scratch ph 6) (word_ne_scratch ph 0)).trans hp.recWord)
      ((hA1o (normSlots 1) (cmp_ne_normA 6 1) ((normA_ne_word 1 0).symm)).trans (hp.nAA 1))
  have hA2dst' : A2 (normSlots 1) = frame (binary (w2 W) est.positive) := by
    rw [hA2dst, field_pos]
  have hH2dst' : H2 (normSlots 1) = 2*(w2 W)+1 := by
    rw [hH2dst, field_pos_length]
  have hA2keep : ∀ i : Fin bank, scratch ph ≠ i → normSlots 1 ≠ i → cmpSlots 6 ≠ i →
      wordSlots 0 ≠ i → A2 i = A i := by
    intro i h1 h2 h3 h4
    rw [hA2o i h1 h2, hA1o i h3 h4]
  -- ## Stage 3 — reset that tape's head against the comparator's driver
  obtain ⟨_, _, H3, A3, st3, hA3src, hA3drv, hH3src, hH3drv, hA3o, hH3o⟩ :=
    rewind_stage (normSlots 1) (cmpSlots 6) (normSlots 2) ((cmp_ne_normA 6 1).symm)
      (hns 1 2 (by decide)) (cmp_ne_normA 6 2) (w3 W) (2*(w2 W)+1) (frame_le_w3 W)
      (frame (binary (w2 W) est.positive)) H2 A2 hH2dst'
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
  obtain ⟨_, _, A4, st4, hA4pos, hA4drv, hA4o⟩ :=
    norm_stage (quintSlots (cmpSlots 6) (normSlots 1) (cmpSlots (posSlot lower))
        (normSlots 3) (normSlots 4))
      (quintSlots_injective _ _ _ _ _ (cmp_ne_normA 6 1)
        (hcneq 6 (posSlot lower) (by cases lower <;> decide)) (cmp_ne_normA 6 3)
        (cmp_ne_normA 6 4) ((cmp_ne_normA (posSlot lower) 1).symm) (hns 1 3 (by decide))
        (hns 1 4 (by decide)) (cmp_ne_normA (posSlot lower) 3)
        (cmp_ne_normA (posSlot lower) 4) (hns 3 4 (by decide)))
      (w3 W) (binary (w2 W) est.positive) H3 A3
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
            ((cmp_ne_word (posSlot lower) 0).symm)).trans (hp.cmpA _)
        · exact (hA3keep (normSlots 3) ((normA_ne_scratch ph 3).symm) (hns 1 3 (by decide))
            (hns 2 3 (by decide)) (cmp_ne_normA 6 3) ((normA_ne_word 3 0).symm)).trans
            (hp.nAA 3)
        · exact (hA3keep (normSlots 4) ((normA_ne_scratch ph 4).symm) (hns 1 4 (by decide))
            (hns 2 4 (by decide)) (cmp_ne_normA 6 4) ((normA_ne_word 4 0).symm)).trans
            (hp.nAA 4))
  have hA4pos' : A4 (cmpSlots (posSlot lower)) = frame (binary (w3 W) est.positive) := by
    have h : A4 (cmpSlots (posSlot lower))
        = frame (ClockNormalize.resize (w3 W) (binary (w2 W) est.positive)) := hA4pos
    rw [h]
    exact widen (w W) est.positive (pos_lt W est hv)
  have hA4drv' : A4 (cmpSlots 6) = List.replicate (w3 W) true := hA4drv
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
  obtain ⟨_, _, H5, A5, st5, hA5dst, hA5src, hH5src, hH5dst, hA5o, hH5o⟩ :=
    field_stage (w W) est 1 1 1 (scratch ph) (normSlotsB 1) ((normB_ne_scratch ph 1).symm)
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
  have hA5dst' : A5 (normSlotsB 1) = frame (binary (w2 W) est.negative) := by
    rw [hA5dst, field_neg]
  have hH5dst' : H5 (normSlotsB 1) = 2*(w2 W)+1 := by
    rw [hH5dst, field_neg_length]
  -- ## Stage 6 — reset that tape's head
  obtain ⟨_, _, H6, A6, st6, hA6src, hA6drv, hH6src, hH6drv, hA6o, hH6o⟩ :=
    rewind_stage (normSlotsB 1) (cmpSlots 6) (normSlotsB 2) ((cmp_ne_normB 6 1).symm)
      (hnbs 1 2 (by decide)) (cmp_ne_normB 6 2) (w3 W) (2*(w2 W)+1) (frame_le_w3 W)
      (frame (binary (w2 W) est.negative)) H5 A5 hH5dst'
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
  obtain ⟨_, _, A7, st7, hA7neg, hA7drv, hA7o⟩ :=
    norm_stage (quintSlots (cmpSlots 6) (normSlotsB 1) (cmpSlots (negSlot lower))
        (normSlotsB 3) (normSlotsB 4))
      (quintSlots_injective _ _ _ _ _ (cmp_ne_normB 6 1)
        (hcneq 6 (negSlot lower) (by cases lower <;> decide)) (cmp_ne_normB 6 3)
        (cmp_ne_normB 6 4) ((cmp_ne_normB (negSlot lower) 1).symm) (hnbs 1 3 (by decide))
        (hnbs 1 4 (by decide)) (cmp_ne_normB (negSlot lower) 3)
        (cmp_ne_normB (negSlot lower) 4) (hnbs 3 4 (by decide)))
      (w3 W) (binary (w2 W) est.negative) H6 A6
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
            ((cmp_ne_word (negSlot lower) 0).symm)).trans (hp.cmpA _)
        · exact (hA6keep (normSlotsB 3) ((normB_ne_scratch ph 3).symm) (normA_ne_normB 1 3)
            (normA_ne_normB 2 3) (normA_ne_normB 3 3) (normA_ne_normB 4 3)
            (hnbs 1 3 (by decide)) (hnbs 2 3 (by decide)) (cmp_ne_normB 6 3)
            (cmp_ne_normB (posSlot lower) 3) ((normB_ne_word 3 0).symm)).trans (hp.nBA 3)
        · exact (hA6keep (normSlotsB 4) ((normB_ne_scratch ph 4).symm) (normA_ne_normB 1 4)
            (normA_ne_normB 2 4) (normA_ne_normB 3 4) (normA_ne_normB 4 4)
            (hnbs 1 4 (by decide)) (hnbs 2 4 (by decide)) (cmp_ne_normB 6 4)
            (cmp_ne_normB (posSlot lower) 4) ((normB_ne_word 4 0).symm)).trans (hp.nBA 4))
  have hA7neg' : A7 (cmpSlots (negSlot lower)) = frame (binary (w3 W) est.negative) := by
    have h : A7 (cmpSlots (negSlot lower))
        = frame (ClockNormalize.resize (w3 W) (binary (w2 W) est.negative)) := hA7neg
    rw [h]
    exact widen (w W) est.negative (neg_lt W est hv)
  have hA7drv' : A7 (cmpSlots 6) = List.replicate (w3 W) true := hA7drv
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
  obtain ⟨_, _, H8, A8, st8, hA8dst, hA8src, _, hH8dst, hA8o, hH8o⟩ :=
    field_stage (w W) est 1 1 2 (scratch ph) (cmpSlots (denSlot lower))
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
          ((cmp_ne_word (denSlot lower) 0).symm)).trans (hp.cmpA _)))
  have hA8dst' : A8 (cmpSlots (denSlot lower)) = frame (binary (w2 W) est.denominator) := by
    rw [hA8dst, field_den]
  have hH8dst' : H8 (cmpSlots (denSlot lower)) = 2*(w2 W)+1 := by
    rw [hH8dst, field_den_length]
  -- ## Stage 9 — reset the denominator tape's head
  obtain ⟨_, _, H9, A9, st9, hA9src, hA9drv, hH9src, hH9drv, hA9o, hH9o⟩ :=
    rewind_stage (cmpSlots (denSlot lower)) (cmpSlots 6) (wordSlots 4)
      (hcneq (denSlot lower) 6 (by cases lower <;> decide)) (cmp_ne_word (denSlot lower) 4)
      (cmp_ne_word 6 4) (w3 W) (2*(w2 W)+1) (frame_le_w3 W)
      (frame (binary (w2 W) est.denominator)) H8 A8 hH8dst'
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
      (hcneq (denSlot lower) k (fun hh => hden hh.symm))).trans (hp.cmpA k)
  have hA9word : ∀ k : Fin 6, k.val ≠ 0 → k.val ≠ 4 → A9 (wordSlots k) = [] := by
    intro k h0 h4
    exact (hA9keep (wordSlots k) ((word_ne_scratch ph k).symm) (normA_ne_word 1 k)
      (normA_ne_word 2 k) (normA_ne_word 3 k) (normA_ne_word 4 k) (normB_ne_word 1 k)
      (normB_ne_word 2 k) (normB_ne_word 3 k) (normB_ne_word 4 k)
      (hwsn 0 k (fun hh => h0 hh.symm)) (hwsn 4 k (fun hh => h4 hh.symm))
      (cmp_ne_word 6 k) (cmp_ne_word (posSlot lower) k) (cmp_ne_word (negSlot lower) k)
      (cmp_ne_word (denSlot lower) k)).trans (hp.wA k)
  have hA9pos : A9 (cmpSlots (posSlot lower)) = frame (binary (w3 W) est.positive) := by
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
  have hA9neg : A9 (cmpSlots (negSlot lower)) = frame (binary (w3 W) est.negative) := by
    rw [hA9o (cmpSlots (negSlot lower))
        (hcneq (denSlot lower) (negSlot lower) (by cases lower <;> decide))
        (hcneq 6 (negSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (negSlot lower) 4).symm),
      hA8o (cmpSlots (negSlot lower)) ((cmp_ne_scratch ph (negSlot lower)).symm)
        (hcneq (denSlot lower) (negSlot lower) (by cases lower <;> decide))]
    exact hA7neg'
  -- ## Stage 10 — the threshold's numerator
  obtain ⟨_, _, A10, st10, hA10v, hA10o⟩ :=
    lit_stage (frame (binary (w3 W) (numerator q))) (cmpSlots (qnumSlot lower)) (wordSlots 1)
      (cmp_ne_word (qnumSlot lower) 1) H9 A9
      (hH9cmp (qnumSlot lower) (by cases lower <;> decide) (by cases lower <;> decide))
      (hH9word 1 (by decide))
      (hA9cmp (qnumSlot lower) (by cases lower <;> decide) (by cases lower <;> decide)
        (by cases lower <;> decide) (by cases lower <;> decide))
      (hA9word 1 (by decide) (by decide))
  -- ## Stage 11 — the literal zero
  obtain ⟨_, _, A11, st11, hA11v, hA11o⟩ :=
    lit_stage (frame (binary (w3 W) 0)) (cmpSlots (zeroSlot lower)) (wordSlots 2)
      (cmp_ne_word (zeroSlot lower) 2) H9 A10
      (hH9cmp (zeroSlot lower) (by cases lower <;> decide) (by cases lower <;> decide))
      (hH9word 2 (by decide))
      ((hA10o (cmpSlots (zeroSlot lower))
        (hcneq (qnumSlot lower) (zeroSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (zeroSlot lower) 1).symm)).trans
        (hA9cmp (zeroSlot lower) (by cases lower <;> decide) (by cases lower <;> decide)
          (by cases lower <;> decide) (by cases lower <;> decide)))
      ((hA10o (wordSlots 2) (cmp_ne_word (qnumSlot lower) 2) (hwsn 1 2 (by decide))).trans
        (hA9word 2 (by decide) (by decide)))
  -- ## Stage 12 — the threshold's denominator
  obtain ⟨_, _, A12, st12, hA12v, hA12o⟩ :=
    lit_stage (frame (binary (w2 W) q.den)) (cmpSlots (qdenSlot lower)) (wordSlots 3)
      (cmp_ne_word (qdenSlot lower) 3) H9 A11
      (hH9cmp (qdenSlot lower) (by cases lower <;> decide) (by cases lower <;> decide))
      (hH9word 3 (by decide))
      ((hA11o (cmpSlots (qdenSlot lower))
        (hcneq (zeroSlot lower) (qdenSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (qdenSlot lower) 2).symm)).trans
        ((hA10o (cmpSlots (qdenSlot lower))
          (hcneq (qnumSlot lower) (qdenSlot lower) (by cases lower <;> decide))
          ((cmp_ne_word (qdenSlot lower) 1).symm)).trans
          (hA9cmp (qdenSlot lower) (by cases lower <;> decide) (by cases lower <;> decide)
            (by cases lower <;> decide) (by cases lower <;> decide))))
      ((hA11o (wordSlots 3) (cmp_ne_word (zeroSlot lower) 3) (hwsn 2 3 (by decide))).trans
        ((hA10o (wordSlots 3) (cmp_ne_word (qnumSlot lower) 3)
          (hwsn 1 3 (by decide))).trans (hA9word 3 (by decide) (by decide))))
  -- ## The comparator's input, read off level 12
  have hA12keep : ∀ i : Fin bank, cmpSlots (qnumSlot lower) ≠ i →
      cmpSlots (zeroSlot lower) ≠ i → cmpSlots (qdenSlot lower) ≠ i → wordSlots 1 ≠ i →
      wordSlots 2 ≠ i → wordSlots 3 ≠ i → A12 i = A9 i := by
    intro i h1 h2 h3 h4 h5 h6
    rw [hA12o i h3 h6, hA11o i h2 h5, hA10o i h1 h4]
  have hA12drv : A12 (cmpSlots 6) = List.replicate (w3 W) true :=
    (hA12keep (cmpSlots 6) (hcneq (qnumSlot lower) 6 (by cases lower <;> decide))
      (hcneq (zeroSlot lower) 6 (by cases lower <;> decide))
      (hcneq (qdenSlot lower) 6 (by cases lower <;> decide)) ((cmp_ne_word 6 1).symm)
      ((cmp_ne_word 6 2).symm) ((cmp_ne_word 6 3).symm)).trans hA9drv
  have hA12pos : A12 (cmpSlots (posSlot lower)) = frame (binary (w3 W) est.positive) :=
    (hA12keep (cmpSlots (posSlot lower))
      (hcneq (qnumSlot lower) (posSlot lower) (by cases lower <;> decide))
      (hcneq (zeroSlot lower) (posSlot lower) (by cases lower <;> decide))
      (hcneq (qdenSlot lower) (posSlot lower) (by cases lower <;> decide))
      ((cmp_ne_word (posSlot lower) 1).symm) ((cmp_ne_word (posSlot lower) 2).symm)
      ((cmp_ne_word (posSlot lower) 3).symm)).trans hA9pos
  have hA12neg : A12 (cmpSlots (negSlot lower)) = frame (binary (w3 W) est.negative) :=
    (hA12keep (cmpSlots (negSlot lower))
      (hcneq (qnumSlot lower) (negSlot lower) (by cases lower <;> decide))
      (hcneq (zeroSlot lower) (negSlot lower) (by cases lower <;> decide))
      (hcneq (qdenSlot lower) (negSlot lower) (by cases lower <;> decide))
      ((cmp_ne_word (negSlot lower) 1).symm) ((cmp_ne_word (negSlot lower) 2).symm)
      ((cmp_ne_word (negSlot lower) 3).symm)).trans hA9neg
  have hA12den : A12 (cmpSlots (denSlot lower)) = frame (binary (w2 W) est.denominator) :=
    (hA12keep (cmpSlots (denSlot lower))
      (hcneq (qnumSlot lower) (denSlot lower) (by cases lower <;> decide))
      (hcneq (zeroSlot lower) (denSlot lower) (by cases lower <;> decide))
      (hcneq (qdenSlot lower) (denSlot lower) (by cases lower <;> decide))
      ((cmp_ne_word (denSlot lower) 1).symm) ((cmp_ne_word (denSlot lower) 2).symm)
      ((cmp_ne_word (denSlot lower) 3).symm)).trans hA9src
  have hA12qnum : A12 (cmpSlots (qnumSlot lower)) = frame (binary (w3 W) (numerator q)) := by
    rw [hA12o (cmpSlots (qnumSlot lower))
        (hcneq (qdenSlot lower) (qnumSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (qnumSlot lower) 3).symm),
      hA11o (cmpSlots (qnumSlot lower))
        (hcneq (zeroSlot lower) (qnumSlot lower) (by cases lower <;> decide))
        ((cmp_ne_word (qnumSlot lower) 2).symm)]
    exact hA10v
  have hA12zero : A12 (cmpSlots (zeroSlot lower)) = frame (binary (w3 W) 0) := by
    rw [hA12o (cmpSlots (zeroSlot lower))
      (hcneq (qdenSlot lower) (zeroSlot lower) (by cases lower <;> decide))
      ((cmp_ne_word (zeroSlot lower) 3).symm)]
    exact hA11v
  -- ## Stage 13 — the comparator
  obtain ⟨_, _, A13, st13, hA13flag, hA13o⟩ :=
    cmp_stage lower (w2 W) est.positive est.negative est.denominator q hposb hnegb hdenb
      hv.denominatorPositive hq hqnb hqdb H9 A12
      (by
        intro j
        rcases Nat.lt_or_ge j.val 7 with hj | hj
        · rcases slot_cover lower j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hH9cmp _ (by cases lower <;> decide) (by cases lower <;> decide)
          · exact hH9cmp _ (by cases lower <;> decide) (by cases lower <;> decide)
          · exact hH9cmp _ (by cases lower <;> decide) (by cases lower <;> decide)
          · exact hH9cmp _ (by cases lower <;> decide) (by cases lower <;> decide)
          · exact hH9src
          · exact hH9cmp _ (by cases lower <;> decide) (by cases lower <;> decide)
          · exact hH9drv
        · refine hH9cmp j (by omega) ?_
          have hlt := denSlot_lt lower
          omega)
      (by
        intro j
        rcases Nat.lt_or_ge j.val 7 with hj | hj
        · rcases slot_cover lower j hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [hA12pos, input_pos]
          · rw [hA12neg, input_neg]
          · rw [hA12qnum, input_qnum]
          · rw [hA12zero, input_zero]
          · rw [hA12den, input_den]
          · rw [hA12v, input_qden]
          · rw [hA12drv, input_driver]
        · rw [input_blank lower (w2 W) est.positive est.negative est.denominator q j hj,
            hA12keep (cmpSlots j)
              (hcneq (qnumSlot lower) j (by have := qnumSlot_lt lower; omega))
              (hcneq (zeroSlot lower) j (by have := zeroSlot_lt lower; omega))
              (hcneq (qdenSlot lower) j (by have := qdenSlot_lt lower; omega))
              ((cmp_ne_word j 1).symm) ((cmp_ne_word j 2).symm) ((cmp_ne_word j 3).symm)]
          exact hA9cmp j (by omega) (by have := posSlot_lt lower; omega)
            (by have := negSlot_lt lower; omega) (by have := denSlot_lt lower; omega))
  -- ## The thirteen-stage sequence
  have c2 := Step.seq st1 st2
  have c3 := Step.seq c2 st3
  have c4 := Step.seq c3 st4
  have c5 := Step.seq c4 st5
  have c6 := Step.seq c5 st6
  have c7 := Step.seq c6 st7
  have c8 := Step.seq c7 st8
  have c9 := Step.seq c8 st9
  have c10 := Step.seq c9 st10
  have c11 := Step.seq c10 st11
  have c12 := Step.seq c11 st12
  have c13 := Step.seq c12 st13
  refine ⟨_, _, _, _, _, c13, hA13flag, ?_, ?_, ?_, ?_⟩
  · intro i hc hna hnb hw hsc
    rw [hA13o i hc, hA12keep i (hc (qnumSlot lower)) (hc (zeroSlot lower))
      (hc (qdenSlot lower)) (hw 1) (hw 2) (hw 3)]
    exact hA9keep i hsc.symm (hna 1) (hna 2) (hna 3) (hna 4) (hnb 1) (hnb 2) (hnb 3) (hnb 4)
      (hw 0) (hw 4) (hc 6) (hc (posSlot lower)) (hc (negSlot lower)) (hc (denSlot lower))
  · intro i hc hna hnb hw hsc
    exact hH9keep i hsc.symm (hna 1) (hna 2) (hnb 1) (hnb 2) (hw 4) (hc 6)
      (hc (denSlot lower))
  · refine hH9cmp 65 (by decide) ?_
    rw [val65]
    have hlt := denSlot_lt lower
    omega
  · rw [hA13o (scratch ph) (fun j => cmp_ne_scratch ph j),
      hA12o (scratch ph) (cmp_ne_scratch ph (qdenSlot lower)) (word_ne_scratch ph 3),
      hA11o (scratch ph) (cmp_ne_scratch ph (zeroSlot lower)) (word_ne_scratch ph 2),
      hA10o (scratch ph) (cmp_ne_scratch ph (qnumSlot lower)) (word_ne_scratch ph 1),
      hA9o (scratch ph) (cmp_ne_scratch ph (denSlot lower)) (cmp_ne_scratch ph 6)
        (word_ne_scratch ph 4), hA8src, hp.recWord]

end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailFeed
