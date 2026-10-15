import Proof.CaseAnalysis.FinalCompareDockField
import Proof.CaseAnalysis.RowsOriginalSchedule

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch CompetitorMonomialStream
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDock
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockField
open NearCubicWires.RepairOrdinary.RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The extension. -/
abbrev ext : ℕ := 87
/-- The tail's bank. -/
abbrev bank : ℕ := 218 + ext

/-- Scratch record slot for a phase (218, 219, 220). -/
def scratch (ph : CloseoutRowsOriginalSchedule.Phase) : Fin bank :=
  match ph with
  | .penalty => ⟨218, by show 218 < 218 + 87; omega⟩
  | .moment => ⟨219, by show 219 < 218 + 87; omega⟩
  | .clause => ⟨220, by show 220 < 218 + 87; omega⟩
/-- Comparator block (221 … 287). -/
def cmpSlots (i : Fin 67) : Fin bank := ⟨221 + i.val, by show 221 + i.val < 218 + 87; omega⟩
/-- Normaliser block A (288 … 292): widens `pos`. -/
def normSlots (i : Fin 5) : Fin bank := ⟨288 + i.val, by show 288 + i.val < 218 + 87; omega⟩
/-- Normaliser block B (293 … 297): widens `neg`. A `normalize_dock` needs a CLEAN
five-tape block, and two operands are widened, so there are two blocks. -/
def normSlotsB (i : Fin 5) : Fin bank := ⟨293 + i.val, by show 293 + i.val < 218 + 87; omega⟩

def wordSlots (i : Fin 6) : Fin bank := ⟨298 + i.val, by show 298 + i.val < 218 + 87; omega⟩
/-- The AND flag (304). -/
def andFlag : Fin bank := ⟨304, by show 304 < 218 + 87; omega⟩
/-- A two-tape copier docked at `src` (tape 0) and `dst` (tape 1). -/
def pairSlots (src dst : Fin bank) (i : Fin 2) : Fin bank :=
  if i.val = 0 then src else dst

theorem cmpSlots_injective : Function.Injective cmpSlots := by
  intro i j h; simp [cmpSlots, Fin.ext_iff] at h ⊢; omega
theorem normSlots_injective : Function.Injective normSlots := by
  intro i j h; simp [normSlots, Fin.ext_iff] at h ⊢; omega
theorem normSlotsB_injective : Function.Injective normSlotsB := by
  intro i j h; simp [normSlotsB, Fin.ext_iff] at h ⊢; omega
theorem wordSlots_injective : Function.Injective wordSlots := by
  intro i j h; simp [wordSlots, Fin.ext_iff] at h ⊢; omega
theorem pairSlots_injective (src dst : Fin bank) (hne : src ≠ dst) :
    Function.Injective (pairSlots src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have h' : src = dst := by simpa [pairSlots] using h
    exact absurd h' hne
  · have h' : dst = src := by simpa [pairSlots] using h
    exact absurd h'.symm hne
  · rfl

/-- The comparator's flag slot. -/
theorem cmpSlots_65 : cmpSlots 65 = ⟨286, by show 286 < 218 + 87; omega⟩ := rfl

/-- **Dock a literal word.** From blank slots `w0 w1`, `w0` receives `bits`. -/
theorem literal_dock (bits : List Bool) (w0 w1 : Fin bank) (hne : w0 ≠ w1)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (h0 : H w0 = 0) (h1 : H w1 = 0) (a0 : A w0 = []) (a1 : A w1 = []) :
    Step (RecoveryFocus.machine (pairSlots w0 w1) (HierarchyFixedWord.machine bits))
      (2*bits.length+2) H A H
      (install (pairSlots w0 w1) A ![bits, List.replicate bits.length false]) := by
  have hstep := (word_step bits).dock (pairSlots w0 w1) (pairSlots_injective w0 w1 hne) H A
    (by intro j; fin_cases j <;> simp [pairSlots, h0, h1])
    (by intro j; fin_cases j <;> simp [pairSlots, a0, a1])
  rwa [dockH_existing (pairSlots w0 w1) H (fun _ => 0)
    (by intro j; fin_cases j <;> simp [pairSlots, h0, h1])] at hstep

/-- **Dock the normaliser** on either block. -/
theorem normalize_dock_at (slots : Fin 5 → Fin bank) (hi : Function.Injective slots)
    (width : ℕ) (bits : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (slots j) = 0)
    (hA : ∀ j, A (slots j) = ClockNormalize.input width bits j) :
    Step (RecoveryFocus.machine slots ClockNormalize.machine) (4*width+4) H A H
      (install slots A (normalizeOut width bits)) := by
  have hstep := (normalize_step width bits).dock slots hi H A hH hA
  rwa [dockH_existing slots H (fun _ => 0) hH] at hstep

theorem normalize_dock (width : ℕ) (bits : List Bool)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hH : ∀ j, H (normSlots j) = 0)
    (hA : ∀ j, A (normSlots j) = ClockNormalize.input width bits j) :
    Step (RecoveryFocus.machine normSlots ClockNormalize.machine) (4*width+4) H A H
      (install normSlots A (normalizeOut width bits)) :=
  normalize_dock_at normSlots normSlots_injective width bits H A hH hA

/-- **Dock a field copy.** Field `k` of the record on `src` (cursor at that
field) is appended to `dst`; the source head advances past the field. -/
theorem field_dock (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (k : Fin 6) (src dst : Fin bank) (hne : src ≠ dst)
    (H : Fin bank → ℕ) (A : Fin bank → List Bool)
    (hsrcH : H src = fieldCursor b q count denominator k) (hdstH : H dst = (A dst).length)
    (hsrcA : A src = CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count denominator) :
    Step (RecoveryFocus.machine (pairSlots src dst) Field.machine)
      (2*(field b q count denominator k).length+1) H A
      (dockH (pairSlots src dst) H
        ![fieldCursor b q count denominator k + 2*(field b q count denominator k).length+1,
          (A dst ++ frame (field b q count denominator k)).length])
      (install (pairSlots src dst) A
        ![CloseoutRowsEstimatorCoefficients.Stream.recordWord b q count denominator,
          A dst ++ frame (field b q count denominator k)]) :=
  (field_step b q count denominator k (A dst)).dock (pairSlots src dst)
    (pairSlots_injective src dst hne) H A
    (by intro j; fin_cases j <;> simp [pairSlots, hsrcH, hdstH])
    (by intro j; fin_cases j <;> simp [pairSlots, hsrcA])

/-- Public form of the bit-length bound the threshold widths need. -/
theorem lt_two_pow_self (n : ℕ) : n < 2^n := Nat.lt_two_pow_self

end NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
