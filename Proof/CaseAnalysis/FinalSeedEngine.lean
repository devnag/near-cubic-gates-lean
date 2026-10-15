import Proof.CaseAnalysis.FinalPrologueUniform
import Proof.CaseAnalysis.FinalWordEngines
import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.MachineModel.UWalkUnary
import Proof.PCP.ProjectionDimensionPolynomial
import Proof.Hierarchy.HierarchyProjectionPrefix

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WordEngines (dockH_all_zero)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.CloseoutSchedule
open NearCubicWires.RepairSource.SelectedRecoveryIntegration

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The sentinel strip -/

theorem strip_dock {m : ℕ} (n : ℕ) (slots : Fin 3 → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : A (slots 0) = CompareMachine.word n)
    (h1 : A (slots 1) = [])
    (h2 : A (slots 2) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots (UWalkUnary.machine false false))
        (2 * n + 6) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      A' (slots 0) = CompareMachine.word n ∧
      A' (slots 1) = List.replicate n true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨rc, hrun, htapes, hheads, hsteps⟩ := UWalkUnary.ready false false 0 n
  have hstep : Step (UWalkUnary.machine false false) (2 * n + 6) (fun _ => 0)
      (UWalkUnary.input 0 n) (fun _ => 0) (UWalkUnary.result false false 0 n) :=
    ⟨rc, hrun, funext hheads, htapes, hsteps⟩
  have hA : ∀ j : Fin 3, A (slots j) = UWalkUnary.input 0 n j := by
    intro j
    fin_cases j
    · simpa [UWalkUnary.input, UWalkUnary.source, ZeroPadding.pad_zero] using h0
    · simpa [UWalkUnary.input] using h1
    · simpa [UWalkUnary.input] using h2
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · rw [install_slot slots hinj A _ 0]
    simp [UWalkUnary.result, UWalkUnary.source, ZeroPadding.pad_zero]
  · rw [install_slot slots hinj A _ 1]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  · intro i hi
    exact install_other slots A _ i hi

/-! ## §2 The unary power `(q+1)^D` -/

theorem power_dock {m : ℕ} (D n : ℕ)
    (slots : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D) → Fin m)
    (hinj : Function.Injective slots) (H : Fin m → ℕ) (A : Fin m → List Bool)
    (hH : ∀ i, H i = 0)
    (h0 : ∀ j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D),
      j.val = 0 → A (slots j) = List.replicate n true)
    (hblank : ∀ j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D),
      j.val ≠ 0 → A (slots j) = []) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots
          (RepairSource.ProjectionNormalization.DimensionPolynomial.machine D 1))
        (RepairSource.ProjectionNormalization.DimensionPolynomial.budget D 1 n) H A H' A' ∧
      (∀ i, H' i = 0) ∧
      (∀ j : Fin (RepairSource.ProjectionNormalization.DimensionPolynomial.tapes D),
        j.val = 0 → A' (slots j) = List.replicate n true) ∧
      A' (slots (RepairSource.ProjectionNormalization.DimensionPolynomial.rawSlot D)) =
        List.replicate ((n + 1) ^ D) true ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  obtain ⟨out, hready, hsrc, hraw, _, _⟩ :=
    RepairSource.ProjectionNormalization.DimensionPolynomial.polynomial_run D 1 n Nat.one_pos
  obtain ⟨rc, hrun, htapes, hheads, hsteps⟩ := hready
  have hstep : Step (RepairSource.ProjectionNormalization.DimensionPolynomial.machine D 1)
      (RepairSource.ProjectionNormalization.DimensionPolynomial.budget D 1 n) (fun _ => 0)
      (RepairSource.ProjectionNormalization.DimensionPolynomial.input D n) (fun _ => 0) out :=
    ⟨rc, hrun, funext hheads, htapes, hsteps⟩
  have hA : ∀ j, A (slots j) =
      RepairSource.ProjectionNormalization.DimensionPolynomial.input D n j := by
    intro j
    by_cases hj : j.val = 0
    · rw [h0 j hj]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hj]
    · rw [hblank j hj]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hj]
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  have hvalue : RepairSource.ProjectionNormalization.DimensionPolynomial.value D 1 n
      = (n + 1) ^ D := by
    simp [RepairSource.ProjectionNormalization.DimensionPolynomial.value]
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_, ?_⟩
  · intro j hj
    have hje : j = ⟨0, by
        simp [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]⟩ := Fin.ext hj
    rw [hje, install_slot slots hinj A out]
    exact hsrc
  · rw [install_slot slots hinj A out]
    rw [hraw, hvalue]
  · intro i hi
    exact install_other slots A out i hi

/-! ## §3 The engine's flat layout

`tw` tapes of the width reader, then a private band of `46 + 2r + 2D` tapes:

| band offset | use |
|---|---|
| `0` | the driver word -- `hengine`'s `driverSlot` |
| `1` | the envelope exponent -- `hengine`'s `expSlot` |
| `2`, `3` | the adder's and the strip's private scratch |
| `4`, `5` | the fixed-word writer |
| `6 + i` | the dimension polynomial's window, `i = 1 .. 13+2r` |
| `20 + 2r + i` | the clause-width program's window, `i = 1 .. 25+2D` |

The two programs read the reader's own output tape `qW` in place, so no unary
copy is spent. -/

theorem rawSlot_val (r : ℕ) : (DimensionPolynomial.rawSlot r).val = 5 + 2 * r := by
  have h : (DimensionPolynomial.rawSlot r).val = 4 + 2 * r + 1 := rfl
  omega

theorem widthSlot_val (D : ℕ) : (Clause.widthSlot D).val = 24 + 2 * D := by
  have h : (Clause.widthSlot D).val = 14 + 2 * D + 10 := rfl
  omega

/-- The engine's private band. -/
def band (r D : ℕ) : ℕ := 46 + 2 * r + 2 * D

/-- The engine's tape count: the reader's tapes plus the band. -/
def tapesOf (tw r D : ℕ) : ℕ := tw + band r D

def inSlotOf {tw : ℕ} (r D : ℕ) (inW : Fin tw) : Fin (tapesOf tw r D) :=
  ⟨inW.val, by have := inW.isLt; dsimp [tapesOf, band]; omega⟩

def driverSlotOf (tw r D : ℕ) : Fin (tapesOf tw r D) :=
  ⟨tw, by dsimp [tapesOf, band]; omega⟩

def expSlotOf (tw r D : ℕ) : Fin (tapesOf tw r D) :=
  ⟨tw + 1, by dsimp [tapesOf, band]; omega⟩

def wSlotsOf (tw r D : ℕ) : Fin tw → Fin (tapesOf tw r D) :=
  fun j => ⟨j.val, by have := j.isLt; dsimp [tapesOf, band]; omega⟩

def fixSlotsOf (tw r D : ℕ) : Fin 2 → Fin (tapesOf tw r D) :=
  fun i => ⟨tw + 4 + i.val, by have := i.isLt; dsimp [tapesOf, band]; omega⟩

def polySlotsOf {tw : ℕ} (r D : ℕ) (qW : Fin tw) :
    Fin (DimensionPolynomial.tapes r) → Fin (tapesOf tw r D) :=
  fun i => ⟨if i.val = 0 then qW.val else tw + 6 + i.val, by
    have h1 := i.isLt
    have h2 := qW.isLt
    dsimp [tapesOf, band, DimensionPolynomial.tapes] at *
    split_ifs <;> omega⟩

def sumSlotsOf (tw r D : ℕ) : Fin 4 → Fin (tapesOf tw r D) :=
  fun i => ⟨if i.val = 0 then tw + 4 else if i.val = 1 then tw + 6 + (5 + 2 * r)
      else if i.val = 2 then tw else tw + 2, by
    dsimp [tapesOf, band]; split_ifs <;> omega⟩

def clauseSlotsOf {tw : ℕ} (r D : ℕ) (qW : Fin tw) :
    Fin (Clause.tapes D) → Fin (tapesOf tw r D) :=
  fun i => ⟨if i.val = 0 then qW.val else tw + 20 + 2 * r + i.val, by
    have h1 := i.isLt
    have h2 := qW.isLt
    dsimp [tapesOf, band, Clause.tapes] at *
    split_ifs <;> omega⟩

def stripSlotsOf (tw r D : ℕ) : Fin 3 → Fin (tapesOf tw r D) :=
  fun i => ⟨if i.val = 0 then tw + 20 + 2 * r + (24 + 2 * D)
      else if i.val = 1 then tw + 1 else tw + 3, by
    dsimp [tapesOf, band]; split_ifs <;> omega⟩

theorem wSlots_injective (tw r D : ℕ) : Function.Injective (wSlotsOf tw r D) := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin (tapesOf tw r D) => i.val) h)

theorem fixSlots_injective (tw r D : ℕ) : Function.Injective (fixSlotsOf tw r D) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapesOf tw r D) => i.val) h
  exact Fin.ext (by dsimp [fixSlotsOf] at hv; omega)

theorem polySlots_injective {tw : ℕ} (r D : ℕ) (qW : Fin tw) :
    Function.Injective (polySlotsOf r D qW) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapesOf tw r D) => i.val) h
  have ha := a.isLt
  have hb := b.isLt
  have hq := qW.isLt
  dsimp [polySlotsOf, DimensionPolynomial.tapes] at hv ha hb
  apply Fin.ext
  split_ifs at hv <;> omega

theorem sumSlots_injective (tw r D : ℕ) : Function.Injective (sumSlotsOf tw r D) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapesOf tw r D) => i.val) h
  have ha := a.isLt
  have hb := b.isLt
  dsimp [sumSlotsOf] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem clauseSlots_injective {tw : ℕ} (r D : ℕ) (qW : Fin tw) :
    Function.Injective (clauseSlotsOf r D qW) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapesOf tw r D) => i.val) h
  have ha := a.isLt
  have hb := b.isLt
  have hq := qW.isLt
  dsimp [clauseSlotsOf, Clause.tapes] at hv ha hb
  apply Fin.ext
  split_ifs at hv <;> omega

theorem stripSlots_injective (tw r D : ℕ) : Function.Injective (stripSlotsOf tw r D) := by
  intro a b h
  have hv := congrArg (fun i : Fin (tapesOf tw r D) => i.val) h
  have ha := a.isLt
  have hb := b.isLt
  dsimp [stripSlotsOf] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-! ## §4 Where each stage's slot map lands, as a `val` disjunction -/

theorem wSlots_val (tw r D : ℕ) (j : Fin tw) : (wSlotsOf tw r D j).val < tw := j.isLt

theorem fixSlots_val (tw r D : ℕ) (j : Fin 2) :
    (fixSlotsOf tw r D j).val = tw + 4 ∨ (fixSlotsOf tw r D j).val = tw + 5 := by
  have hj := j.isLt
  dsimp [fixSlotsOf]
  omega

theorem polySlots_val {tw : ℕ} (r D : ℕ) (qW : Fin tw) (j : Fin (DimensionPolynomial.tapes r)) :
    (polySlotsOf r D qW j).val = qW.val ∨
      (tw + 7 ≤ (polySlotsOf r D qW j).val ∧ (polySlotsOf r D qW j).val ≤ tw + 19 + 2 * r) := by
  have hj := j.isLt
  dsimp [polySlotsOf, DimensionPolynomial.tapes] at *
  split_ifs with h <;> omega

theorem sumSlots_val (tw r D : ℕ) (j : Fin 4) :
    (sumSlotsOf tw r D j).val = tw ∨ (sumSlotsOf tw r D j).val = tw + 2 ∨
      (sumSlotsOf tw r D j).val = tw + 4 ∨ (sumSlotsOf tw r D j).val = tw + 6 + (5 + 2 * r) := by
  dsimp [sumSlotsOf]
  split_ifs <;> omega

theorem clauseSlots_val {tw : ℕ} (r D : ℕ) (qW : Fin tw) (j : Fin (Clause.tapes D)) :
    (clauseSlotsOf r D qW j).val = qW.val ∨
      (tw + 21 + 2 * r ≤ (clauseSlotsOf r D qW j).val ∧
        (clauseSlotsOf r D qW j).val ≤ tw + 20 + 2 * r + (25 + 2 * D)) := by
  have hj := j.isLt
  dsimp [clauseSlotsOf, Clause.tapes] at *
  split_ifs with h <;> omega

theorem stripSlots_val (tw r D : ℕ) (j : Fin 3) :
    (stripSlotsOf tw r D j).val = tw + 1 ∨ (stripSlotsOf tw r D j).val = tw + 3 ∨
      (stripSlotsOf tw r D j).val = tw + 20 + 2 * r + (24 + 2 * D) := by
  dsimp [stripSlotsOf]
  split_ifs <;> omega

/-! ## §5 A width reader, docked -/

/-- Any `Step` of a machine on its own layout, moved to an ambient layout at an
injective slot map, with the ambient already carrying its entry tapes. -/
theorem width_dock {tw sw m : ℕ} (W : Machine tw sw) (n : ℕ)
    (slots : Fin tw → Fin m) (hinj : Function.Injective slots)
    (H : Fin m → ℕ) (A : Fin m → List Bool) (hH : ∀ i, H i = 0)
    (tin tout : Fin tw → List Bool)
    (hstep : Step W n (fun _ => 0) tin (fun _ => 0) tout)
    (hA : ∀ j, A (slots j) = tin j) :
    ∃ (H' : Fin m → ℕ) (A' : Fin m → List Bool),
      Step (RecoveryFocus.machine slots W) n H A H' A' ∧ (∀ i, H' i = 0) ∧
      (∀ j, A' (slots j) = tout j) ∧
      (∀ i : Fin m, (∀ j, slots j ≠ i) → A' i = A i) := by
  have hdock := hstep.dock slots hinj H A (fun j => hH (slots j)) hA
  refine ⟨_, _, hdock, dockH_all_zero slots H hH, ?_, ?_⟩
  · intro j
    exact install_slot slots hinj A tout j
  · intro i hi
    exact install_other slots A tout i hi

/-! ## §6 The engine, and its fuel -/

/-- **The seed engine.**  Six stages on one flat layout: the width reader, the
dimension polynomial at exponent `r`, the fixed threshold floor, the unary adder
(driver word), the clause-width program and the sentinel strip (envelope
exponent). -/
noncomputable def engineMachine {tw sw : ℕ} (r D : ℕ) (W : Machine tw sw) (qW : Fin tw)
    (entryFloor : ℕ) :=
  Composition.machine
    (Composition.machine
      (Composition.machine
        (Composition.machine
          (Composition.machine
            (RecoveryFocus.machine (wSlotsOf tw r D) W)
            (RecoveryFocus.machine (polySlotsOf r D qW) (DimensionPolynomial.machine r 1)))
          (RecoveryFocus.machine (fixSlotsOf tw r D)
            (HierarchyFixedWord.machine (List.replicate entryFloor true))))
        (RecoveryFocus.machine (sumSlotsOf tw r D) ClockUnarySum.machine))
      (RecoveryFocus.machine (clauseSlotsOf r D qW) (Clause.machine D)))
    (RecoveryFocus.machine (stripSlotsOf tw r D) (UWalkUnary.machine false false))

/-- What the six stages cost, with the five paid bridge steps of `Step.seq`. -/
def engineFuel (r D : ℕ) (wfuel : ℕ → ℕ) (entryFloor : ℕ) (q : ℕ → ℕ) (len : ℕ) : ℕ :=
  wfuel len + 1 + DimensionPolynomial.budget r 1 (q len)
    + 1 + (2 * entryFloor + 2)
    + 1 + (2 * (entryFloor + (q len + 1) ^ r) + 6)
    + 1 + Clause.budget D (q len)
    + 1 + (2 * RepairSource.CloseoutLanguage.clauseWidth D (q len) + 6)

/-! ## §7 Slot values, and the slot identifications the chain needs -/

theorem notMem_of_val {T t : ℕ} (slots : Fin t → Fin T) (i : Fin T)
    (h : ∀ j, (slots j).val ≠ i.val) : ∀ j, slots j ≠ i :=
  fun j hj => h j (congrArg (fun z : Fin T => z.val) hj)

theorem inSlot_eq {tw : ℕ} (r D : ℕ) (inW : Fin tw) :
    inSlotOf r D inW = wSlotsOf tw r D inW := Fin.ext rfl

theorem driverSlot_eq (tw r D : ℕ) : driverSlotOf tw r D = sumSlotsOf tw r D 2 := Fin.ext rfl

theorem expSlot_eq (tw r D : ℕ) : expSlotOf tw r D = stripSlotsOf tw r D 1 := Fin.ext rfl

theorem fixSlot0_eq (tw r D : ℕ) : fixSlotsOf tw r D 0 = sumSlotsOf tw r D 0 := Fin.ext rfl

theorem polyQ_eq {tw : ℕ} (r D : ℕ) (qW : Fin tw) (j : Fin (DimensionPolynomial.tapes r))
    (hj : j.val = 0) : polySlotsOf r D qW j = wSlotsOf tw r D qW := by
  apply Fin.ext
  dsimp [polySlotsOf, wSlotsOf]
  rw [if_pos hj]

theorem clauseQ_eq {tw : ℕ} (r D : ℕ) (qW : Fin tw) :
    clauseSlotsOf r D qW (Clause.qSlot D) = wSlotsOf tw r D qW := by
  apply Fin.ext
  have h : (Clause.qSlot D).val = 0 := rfl
  dsimp [clauseSlotsOf, wSlotsOf]
  rw [if_pos h]

theorem polyRaw_eq (tw r D : ℕ) (qW : Fin tw) :
    polySlotsOf r D qW (DimensionPolynomial.rawSlot r) = sumSlotsOf tw r D 1 := by
  apply Fin.ext
  have h := rawSlot_val r
  dsimp [polySlotsOf, sumSlotsOf]
  rw [if_neg (by omega), h]

theorem clauseWidthSlot_eq (tw r D : ℕ) (qW : Fin tw) :
    clauseSlotsOf r D qW (Clause.widthSlot D) = stripSlotsOf tw r D 0 := by
  apply Fin.ext
  have h := widthSlot_val D
  dsimp [clauseSlotsOf, stripSlotsOf]
  rw [if_neg (by omega), h]

/-! ## §8 The engine runs: `hengine` from one width reader -/

theorem engine_of_widthReader_retained {tw sw : ℕ} (r D : ℕ) (hD : 1 ≤ D)
    (W : Machine tw sw) (inW qW : Fin tw) (hne : inW ≠ qW)
    (entryFloor : ℕ) (q wfuel : ℕ → ℕ)
    (hwidth : ∀ (len : ℕ) (x : BitInput len), ∃ wout : Fin tw → List Bool,
      wout inW = frame (List.ofFn x) ∧
      wout qW = List.replicate (q len) true ∧
      Step W (wfuel len) (fun _ => 0)
        (fun j => if j = inW then frame (List.ofFn x) else []) (fun _ => 0) wout) :
    ∀ (len : ℕ) (x : BitInput len),
      ∃ out : Fin (tapesOf tw r D) → List Bool,
        out (inSlotOf r D inW) = frame (List.ofFn x) ∧
        out (driverSlotOf tw r D) = List.replicate (entryFloor + (q len + 1) ^ r) true ∧
        out (expSlotOf tw r D) =
          List.replicate (RepairSource.CloseoutLanguage.clauseWidth D (q len)) true ∧
        out (stripSlotsOf tw r D 0) =
          CompareMachine.word (RepairSource.CloseoutLanguage.clauseWidth D (q len)) ∧
        Step (engineMachine r D W qW entryFloor) (engineFuel r D wfuel entryFloor q len)
          (fun _ => 0) (fun j => if j = inSlotOf r D inW then frame (List.ofFn x) else [])
          (fun _ => 0) out := by
  classical
  intro len x
  obtain ⟨wout, hwin, hwq, hwstep⟩ := hwidth len x
  have hqne : inW.val ≠ qW.val := fun h => hne (Fin.ext h)
  have hinlt := inW.isLt
  have hqlt := qW.isLt
  set A0 : Fin (tapesOf tw r D) → List Bool :=
    (fun j => if j = inSlotOf r D inW then frame (List.ofFn x) else []) with hA0def
  have hA0blank : ∀ i : Fin (tapesOf tw r D), i.val ≠ inW.val → A0 i = [] := by
    intro i hi
    have hne' : i ≠ inSlotOf r D inW := by
      intro h
      exact hi (by rw [h]; rfl)
    simp only [hA0def, if_neg hne']
  have hA0w : ∀ j : Fin tw,
      A0 (wSlotsOf tw r D j) = (if j = inW then frame (List.ofFn x) else []) := by
    intro j
    by_cases hj : j = inW
    · subst hj
      rw [← inSlot_eq r D j]
      simp [hA0def]
    · have hv : (wSlotsOf tw r D j).val ≠ inW.val := by
        have hz : (wSlotsOf tw r D j).val = j.val := rfl
        rw [hz]
        exact fun h => hj (Fin.ext h)
      rw [hA0blank _ hv, if_neg hj]
  -- stage 1: the width reader
  obtain ⟨H1, A1, hs1, hh1, ht1, hr1⟩ :=
    width_dock W (wfuel len) (wSlotsOf tw r D) (wSlots_injective tw r D) (fun _ => 0) A0
      (fun _ => rfl) (fun j => if j = inW then frame (List.ofFn x) else []) wout hwstep hA0w
  have hb1 : ∀ i : Fin (tapesOf tw r D), tw ≤ i.val → A1 i = [] := by
    intro i hi
    have hkeep : A1 i = A0 i := by
      refine hr1 i (notMem_of_val _ _ ?_)
      intro j
      have hjl := j.isLt
      have hz : (wSlotsOf tw r D j).val = j.val := rfl
      omega
    rw [hkeep]
    exact hA0blank i (by omega)
  -- stage 2: the dimension polynomial, at exponent `r`
  obtain ⟨H2, A2, hs2, hh2, ht2q, ht2raw, hr2⟩ :=
    power_dock r (q len) (polySlotsOf r D qW) (polySlots_injective r D qW) H1 A1 hh1
      (by
        intro j hj
        rw [polyQ_eq r D qW j hj, ht1 qW, hwq])
      (by
        intro j hj
        refine hb1 _ ?_
        dsimp [polySlotsOf]
        rw [if_neg hj]
        omega)
  have keep2 : ∀ i : Fin (tapesOf tw r D), i.val ≠ qW.val →
      (i.val < tw + 7 ∨ tw + 19 + 2 * r < i.val) → A2 i = A1 i := by
    intro i h1 h2
    refine hr2 i (notMem_of_val _ _ ?_)
    intro j
    have := polySlots_val r D qW j
    omega
  -- stage 3: the fixed threshold floor
  obtain ⟨H3, A3, hs3, hh3, ht3, hr3⟩ :=
    CloseoutFinalC10WordEngines.fixedWord_dock (List.replicate entryFloor true)
      (fixSlotsOf tw r D) (fixSlots_injective tw r D) H2 A2 hh2
      (by
        have hv : (fixSlotsOf tw r D 0).val = tw + 4 := rfl
        rw [keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
      (by
        have hv : (fixSlotsOf tw r D 1).val = tw + 5 := rfl
        rw [keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
  have keep3 : ∀ i : Fin (tapesOf tw r D), i.val ≠ tw + 4 → i.val ≠ tw + 5 → A3 i = A2 i := by
    intro i h1 h2
    refine hr3 i (notMem_of_val _ _ ?_)
    intro j
    have := fixSlots_val tw r D j
    omega
  -- stage 4: the unary adder -- the driver word
  obtain ⟨H4, A4, hs4, hh4, -, -, ht4c, hr4⟩ :=
    CloseoutFinalC10WordEngines.sum_dock entryFloor ((q len + 1) ^ r) (sumSlotsOf tw r D)
      (sumSlots_injective tw r D) H3 A3 hh3
      (by
        rw [← fixSlot0_eq tw r D]
        exact ht3)
      (by
        have hv : (sumSlotsOf tw r D 1).val = tw + 6 + (5 + 2 * r) := rfl
        rw [keep3 _ (by omega) (by omega), ← polyRaw_eq tw r D qW]
        exact ht2raw)
      (by
        have hv : (sumSlotsOf tw r D 2).val = tw := rfl
        rw [keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
      (by
        have hv : (sumSlotsOf tw r D 3).val = tw + 2 := rfl
        rw [keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
  have keep4 : ∀ i : Fin (tapesOf tw r D), i.val ≠ tw → i.val ≠ tw + 2 → i.val ≠ tw + 4 →
      i.val ≠ tw + 6 + (5 + 2 * r) → A4 i = A3 i := by
    intro i h1 h2 h3 h4
    refine hr4 i (notMem_of_val _ _ ?_)
    intro j
    have := sumSlots_val tw r D j
    omega
  -- stage 5: the clause-width program
  obtain ⟨H5, A5, hs5, hh5, -, ht5w, hr5⟩ :=
    CloseoutFinalC10UnaryExpDock.clauseWidth_dock D (q len) hD (clauseSlotsOf r D qW)
      (clauseSlots_injective r D qW) H4 A4 hh4
      (by
        rw [clauseQ_eq r D qW]
        have hv : (wSlotsOf tw r D qW).val = qW.val := rfl
        rw [keep4 _ (by omega) (by omega) (by omega) (by omega),
          keep3 _ (by omega) (by omega),
          ← polyQ_eq r D qW ⟨0, by dsimp [DimensionPolynomial.tapes]; omega⟩ rfl]
        exact ht2q _ rfl)
      (by
        intro j hj
        have hv : (clauseSlotsOf r D qW j).val = tw + 20 + 2 * r + j.val := by
          dsimp [clauseSlotsOf]
          rw [if_neg hj]
        rw [keep4 _ (by omega) (by omega) (by omega) (by omega),
          keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
  have keep5 : ∀ i : Fin (tapesOf tw r D), i.val ≠ qW.val →
      (i.val < tw + 21 + 2 * r ∨ tw + 20 + 2 * r + (25 + 2 * D) < i.val) → A5 i = A4 i := by
    intro i h1 h2
    refine hr5 i (notMem_of_val _ _ ?_)
    intro j
    have := clauseSlots_val r D qW j
    omega
  -- stage 6: the sentinel strip -- the envelope exponent
  obtain ⟨H6, A6, hs6, hh6, ht6a, ht6b, hr6⟩ :=
    strip_dock (RepairSource.CloseoutLanguage.clauseWidth D (q len)) (stripSlotsOf tw r D)
      (stripSlots_injective tw r D) H5 A5 hh5
      (by
        rw [← clauseWidthSlot_eq tw r D qW]
        exact ht5w)
      (by
        have hv : (stripSlotsOf tw r D 1).val = tw + 1 := rfl
        rw [keep5 _ (by omega) (by omega),
          keep4 _ (by omega) (by omega) (by omega) (by omega),
          keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
      (by
        have hv : (stripSlotsOf tw r D 2).val = tw + 3 := rfl
        rw [keep5 _ (by omega) (by omega),
          keep4 _ (by omega) (by omega) (by omega) (by omega),
          keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega)]
        exact hb1 _ (by omega))
  have keep6 : ∀ i : Fin (tapesOf tw r D), i.val ≠ tw + 1 → i.val ≠ tw + 3 →
      i.val ≠ tw + 20 + 2 * r + (24 + 2 * D) → A6 i = A5 i := by
    intro i h1 h2 h3
    refine hr6 i (notMem_of_val _ _ ?_)
    intro j
    have := stripSlots_val tw r D j
    omega
  refine ⟨A6, ?_, ?_, ?_, ht6a, ?_⟩
  · have hv : (inSlotOf r D inW).val = inW.val := rfl
    rw [keep6 _ (by omega) (by omega) (by omega),
      keep5 _ (by omega) (by omega),
      keep4 _ (by omega) (by omega) (by omega) (by omega),
      keep3 _ (by omega) (by omega), keep2 _ (by omega) (by omega),
      inSlot_eq r D inW, ht1 inW, hwin]
  · have hv : (driverSlotOf tw r D).val = tw := rfl
    rw [keep6 _ (by omega) (by omega) (by omega),
      keep5 _ (by omega) (by omega), driverSlot_eq tw r D]
    exact ht4c
  · rw [expSlot_eq tw r D]
    exact ht6b
  · have hH6 : H6 = (fun _ => 0) := funext hh6
    have hchain := ((((hs1.seq hs2).seq hs3).seq hs4).seq hs5).seq hs6
    rw [hH6] at hchain
    simp only [List.length_replicate] at hchain
    exact hchain

/-- Original engine interface, forgetting the preserved width word. -/
theorem engine_of_widthReader {tw sw : ℕ} (r D : ℕ) (hD : 1 ≤ D)
    (W : Machine tw sw) (inW qW : Fin tw) (hne : inW ≠ qW)
    (entryFloor : ℕ) (q wfuel : ℕ → ℕ)
    (hwidth : ∀ (len : ℕ) (x : BitInput len), ∃ wout : Fin tw → List Bool,
      wout inW = frame (List.ofFn x) ∧
      wout qW = List.replicate (q len) true ∧
      Step W (wfuel len) (fun _ => 0)
        (fun j => if j = inW then frame (List.ofFn x) else []) (fun _ => 0) wout) :
    ∀ (len : ℕ) (x : BitInput len),
      ∃ out : Fin (tapesOf tw r D) → List Bool,
        out (inSlotOf r D inW) = frame (List.ofFn x) ∧
        out (driverSlotOf tw r D) = List.replicate (entryFloor + (q len + 1) ^ r) true ∧
        out (expSlotOf tw r D) =
          List.replicate (RepairSource.CloseoutLanguage.clauseWidth D (q len)) true ∧
        Step (engineMachine r D W qW entryFloor) (engineFuel r D wfuel entryFloor q len)
          (fun _ => 0) (fun j => if j = inSlotOf r D inW then frame (List.ofFn x) else [])
          (fun _ => 0) out := by
  intro len x
  obtain ⟨out, hi, hd, he, _, hs⟩ := engine_of_widthReader_retained r D hD W inW qW
    hne entryFloor q wfuel hwidth len x
  exact ⟨out, hi, hd, he, hs⟩

/-! ## §9 The engine docked onto the C10 bank, and `Seed` -/

/-- The engine's own layout mapped into the `218 + (60 + extra) + 1` bank at
`extra := tapesOf tw r D + 23`: the input tape to `0`, the driver word to `218`,
the envelope exponent to `278`, and every other tape of the engine into the
seed's private band `301 ..`. -/
def bankSlots (tw r D : ℕ) (inW : Fin tw) :
    Fin (tapesOf tw r D) → Fin (218 + (60 + (tapesOf tw r D + 23)) + 1) :=
  fun j => ⟨if j.val = inW.val then 0 else if j.val = tw then 218
      else if j.val = tw + 1 then 278 else 301 + j.val, by
    have h1 := j.isLt
    split_ifs <;> omega⟩

theorem bankSlots_injective (tw r D : ℕ) (inW : Fin tw) :
    Function.Injective (bankSlots tw r D inW) := by
  intro a b h
  have hv : (bankSlots tw r D inW a).val = (bankSlots tw r D inW b).val :=
    congrArg (fun z : Fin (218 + (60 + (tapesOf tw r D + 23)) + 1) => z.val) h
  have hi := inW.isLt
  apply Fin.ext
  dsimp [bankSlots] at hv
  split_ifs at hv <;> omega

theorem bankSlots_in {tw : ℕ} (r D : ℕ) (inW : Fin tw) :
    (bankSlots tw r D inW (inSlotOf r D inW)).val = 0 := by
  have h1 : (inSlotOf r D inW).val = inW.val := rfl
  dsimp [bankSlots]
  rw [if_pos h1]

theorem bankSlots_driver (tw r D : ℕ) (inW : Fin tw) :
    (bankSlots tw r D inW (driverSlotOf tw r D)).val = 218 := by
  have h1 : (driverSlotOf tw r D).val = tw := rfl
  have hi := inW.isLt
  dsimp [bankSlots]
  split_ifs <;> omega

theorem bankSlots_exp (tw r D : ℕ) (inW : Fin tw) :
    (bankSlots tw r D inW (expSlotOf tw r D)).val = 278 := by
  have h1 : (expSlotOf tw r D).val = tw + 1 := rfl
  have hi := inW.isLt
  dsimp [bankSlots]
  split_ifs <;> omega

theorem bankSlots_private {tw : ℕ} (r D : ℕ) (inW : Fin tw)
    (j : Fin (tapesOf tw r D)) (h1 : j ≠ inSlotOf r D inW) (h2 : j ≠ driverSlotOf tw r D)
    (h3 : j ≠ expSlotOf tw r D) :
    301 ≤ (bankSlots tw r D inW j).val ∧
      (bankSlots tw r D inW j).val < 301 + tapesOf tw r D := by
  have hj := j.isLt
  have e1 : j.val ≠ inW.val := fun h => h1 (Fin.ext h)
  have e2 : j.val ≠ tw := fun h => h2 (Fin.ext h)
  have e3 : j.val ≠ tw + 1 := fun h => h3 (Fin.ext h)
  dsimp [bankSlots]
  split_ifs <;> omega

/-- **`Seed` (`Proof/CaseAnalysis/FinalPrologueUniform.lean`) from one width
reader.**  Everything `hpre` still owed except the paper's `q(N)` itself. -/
theorem seed_of_widthReader {tw sw : ℕ} (r D : ℕ) (hD : 1 ≤ D)
    (W : Machine tw sw) (inW qW : Fin tw) (hne : inW ≠ qW)
    (entryFloor : ℕ) (q wfuel : ℕ → ℕ)
    (hwidth : ∀ (len : ℕ) (x : BitInput len), ∃ wout : Fin tw → List Bool,
      wout inW = frame (List.ofFn x) ∧
      wout qW = List.replicate (q len) true ∧
      Step W (wfuel len) (fun _ => 0)
        (fun j => if j = inW then frame (List.ofFn x) else []) (fun _ => 0) wout) :
    RepairSource.CloseoutFinal.C10PrologueUniform.Seed (tapesOf tw r D)
      (fun len => entryFloor + (q len + 1) ^ r) q D (engineFuel r D wfuel entryFloor q)
      (RecoveryFocus.machine (bankSlots tw r D inW) (engineMachine r D W qW entryFloor)) :=
  RepairSource.CloseoutFinal.C10PrologueUniform.seed_of_engine (tapesOf tw r D)
    (engineMachine r D W qW entryFloor) (bankSlots tw r D inW) (bankSlots_injective tw r D inW)
    (inSlotOf r D inW) (driverSlotOf tw r D) (expSlotOf tw r D)
    (bankSlots_in r D inW) (bankSlots_driver tw r D inW) (bankSlots_exp tw r D inW)
    (bankSlots_private r D inW)
    (fun len => entryFloor + (q len + 1) ^ r) q D (engineFuel r D wfuel entryFloor q)
    (engine_of_widthReader r D hD W inW qW hne entryFloor q wfuel hwidth)

theorem entryWidthSchedule_eq (sources : RepairSource.EightSources) (k r N : ℕ) :
    RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r N
      = RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources
        + (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k N + 1) ^ r := rfl

theorem prologue_at_schedule (sources : RepairSource.EightSources) (k r D : ℕ) (hD : 1 ≤ D)
    {tw sw : ℕ} (W : Machine tw sw) (inW qW : Fin tw) (hne : inW ≠ qW) (wfuel : ℕ → ℕ)
    (hwidth : ∀ (len : ℕ) (x : BitInput len), ∃ wout : Fin tw → List Bool,
      wout inW = frame (List.ofFn x) ∧
      wout qW = List.replicate
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k len) true ∧
      Step W (wfuel len) (fun _ => 0)
        (fun j => if j = inW then frame (List.ofFn x) else []) (fun _ => 0) wout) :
    RepairSource.CloseoutFinal.C10PrologueUniform.Prologue (tapesOf tw r D + 23)
      (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D
      (RepairSource.CloseoutFinal.C10PrologueUniform.prologueFuel D
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k)
        (engineFuel r D wfuel
          (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
          (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k)))
      (RepairSource.CloseoutFinal.C10PrologueUniform.prologueMachine (tapesOf tw r D)
        (RecoveryFocus.machine (bankSlots tw r D inW)
          (engineMachine r D W qW
            (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)))) :=
  RepairSource.CloseoutFinal.C10PrologueUniform.prologue_of_seed (tapesOf tw r D)
    (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
    (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D
    (engineFuel r D wfuel
      (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k))
    _
    (seed_of_widthReader r D hD W inW qW hne
      (RepairSource.CloseoutFinal.C10PartsSchedule.thresholdFloor sources)
      (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) wfuel hwidth)

noncomputable def readerHier (sources : RepairSource.EightSources) (k : ℕ) :=
  (sources.hierarchy (fun n => n ^ (k + 2)) (PolynomialClock.ordinaryClock k)).hierarchy

noncomputable def readerPad (sources : RepairSource.EightSources) (k : ℕ) : ℕ :=
  padding sources k (PolynomialClock.ordinaryClock k)

noncomputable def readerCode (sources : RepairSource.EightSources) (k : ℕ) : List Bool :=
  RepairSource.VerifierEncoding.code (readerHier sources k).verifier

noncomputable abbrev rp (sources : RepairSource.EightSources) : ℕ :=
  (fixedProjection sources).degrees.proofLog

noncomputable abbrev rq (sources : RepairSource.EightSources) : ℕ :=
  (fixedProjection sources).degrees.queries

/-- The reader's machine: hierarchy padding, then the dimension producer. -/
noncomputable def widthReader (sources : RepairSource.EightSources) (k : ℕ) :=
  HierarchyPrefix.machine k (readerHier sources k).coefficient (readerPad sources k)
    (rp sources) (rq sources) (fixedProjection sources).coefficient (readerCode sources k)

noncomputable def readerIn (sources : RepairSource.EightSources) (k : ℕ) :
    Fin (HierarchyPrefix.tapes k (rp sources) (rq sources)) :=
  HierarchyPrefix.old k (rp sources) (rq sources)
    (HierarchyFramedInput.old k (HierarchyReduction.xTape k))

/-- The reader's output tape: `q(N)` in unary. -/
noncomputable def readerQ (sources : RepairSource.EightSources) (k : ℕ) :
    Fin (HierarchyPrefix.tapes k (rp sources) (rq sources)) :=
  HierarchyPrefix.dimensionSlots k (rp sources) (rq sources)
    (DimensionsFromInput.rawR (rp sources) (rq sources))

theorem readerIn_val (sources : RepairSource.EightSources) (k : ℕ) :
    (readerIn sources k).val = 2 := rfl

theorem rawR_ne (p q : ℕ) : (DimensionsFromInput.rawR p q).val ≠ 12 := by
  have h : (DimensionsFromInput.rawR p q).val =
      if (DimensionProducer.rawR p q).val = 0 then 27
      else 34 + ((DimensionProducer.rawR p q).val - 1) := rfl
  split_ifs at h <;> omega

theorem readerQ_val (sources : RepairSource.EightSources) (k : ℕ) :
    (readerQ sources k).val =
      HierarchyFramedInput.tapes k + (DimensionsFromInput.rawR (rp sources) (rq sources)).val := by
  have h := rawR_ne (rp sources) (rq sources)
  dsimp only [readerQ, HierarchyPrefix.dimensionSlots]
  rw [if_neg h]
  rfl

theorem readerIn_ne (sources : RepairSource.EightSources) (k : ℕ) :
    readerIn sources k ≠ readerQ sources k := by
  intro hcontra
  have h1 := readerIn_val sources k
  have h2 := readerQ_val sources k
  have h3 : HierarchyFramedInput.tapes k = HierarchyReduction.base k + 15 + 2 := rfl
  rw [hcontra] at h1
  omega

/-- The reader's budget depends on the input only through its LENGTH -- which is
what `hengine`'s `seedFuel : ℕ → ℕ` demands. -/
theorem budget_length_only (k CH Cpad p q C : ℕ) (code x y : List Bool) (hpad : k + 3 ≤ Cpad)
    (h : x.length = y.length) :
    HierarchyPrefix.budget k CH Cpad p q C code x
      = HierarchyPrefix.budget k CH Cpad p q C code y := by
  have hx := HierarchyPadding.raw_length k CH Cpad code x hpad
  have hy := HierarchyPadding.raw_length k CH Cpad code y hpad
  unfold HierarchyPrefix.budget HierarchyFramedInput.budget DimensionsFromInput.budget
    HierarchyReduction.ordinaryBudget ClockTotal.budget
  rw [hx, hy, h]

/-- The reader's fuel, as a function of the LENGTH alone. -/
noncomputable def readerFuel (sources : RepairSource.EightSources) (k n : ℕ) : ℕ :=
  HierarchyPrefix.budget k (readerHier sources k).coefficient (readerPad sources k)
    (rp sources) (rq sources) (fixedProjection sources).coefficient (readerCode sources k)
    (List.replicate n false)

theorem readerPad_ge (sources : RepairSource.EightSources) (k : ℕ) :
    k + 3 ≤ readerPad sources k := by
  show k + 3 ≤ max ((readerHier sources k).coefficient) (k + 3)
  exact le_max_right _ _

theorem reader_width (sources : RepairSource.EightSources) (k : ℕ) (x : List Bool) :
    Dimensions.width (fixedProjection sources)
        (HierarchyPadding.rawInput k (readerHier sources k).coefficient (readerPad sources k)
          (readerCode sources k) x).length
      = RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k x.length := by
  rw [HierarchyPadding.raw_length k _ _ _ x (readerPad_ge sources k)]
  rfl

theorem reader_input_eq (sources : RepairSource.EightSources) (k : ℕ) (x : List Bool) :
    HierarchyPrefix.input k (rp sources) (rq sources) x
      = fun j => if j = readerIn sources k then frame x else [] := by
  funext j
  by_cases hj : j = readerIn sources k
  · have h2 : j.val = 2 := by rw [hj, readerIn_val]
    simp only [HierarchyPrefix.input, if_pos h2, if_pos hj]
  · have h2 : j.val ≠ 2 := by
      intro h
      exact hj (Fin.ext (by rw [h, readerIn_val]))
    simp only [HierarchyPrefix.input, if_neg h2, if_neg hj]

/-- **The width reader, as `hengine`'s own shape with ONE output word.** -/
theorem width_reader (sources : RepairSource.EightSources) (k : ℕ) :
    ∀ (len : ℕ) (x : BitInput len),
      ∃ wout : Fin (HierarchyPrefix.tapes k (rp sources) (rq sources)) → List Bool,
        wout (readerIn sources k) = frame (List.ofFn x) ∧
        wout (readerQ sources k) = List.replicate
          (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k len) true ∧
        Step (widthReader sources k) (readerFuel sources k len) (fun _ => 0)
          (fun j => if j = readerIn sources k then frame (List.ofFn x) else [])
          (fun _ => 0) wout := by
  intro len x
  obtain ⟨out, hready, hx, -, -, hR, -, -, -⟩ :=
    HierarchyPrefix.prefix_run k (readerHier sources k).coefficient (readerPad sources k)
      (readerCode sources k) (List.ofFn x) (readerPad_ge sources k) (fixedProjection sources)
  obtain ⟨rc, hrun, htapes, hheads, hsteps⟩ := hready
  have hlen : (List.ofFn x).length = len := List.length_ofFn
  have hfuel : HierarchyPrefix.budget k (readerHier sources k).coefficient (readerPad sources k)
      (rp sources) (rq sources) (fixedProjection sources).coefficient (readerCode sources k)
      (List.ofFn x) = readerFuel sources k len := by
    refine budget_length_only _ _ _ _ _ _ _ _ _ (readerPad_ge sources k) ?_
    rw [hlen, List.length_replicate]
  refine ⟨out, hx, ?_, ?_⟩
  · show out (HierarchyPrefix.dimensionSlots k (rp sources) (rq sources)
      (DimensionsFromInput.rawR (rp sources) (rq sources))) = _
    rw [hR, reader_width sources k (List.ofFn x), hlen]
  · rw [← reader_input_eq sources k (List.ofFn x), ← hfuel]
    exact ⟨rc, hrun, funext hheads, htapes, hsteps⟩

/-! ## §12 `Prologue` at the pinned schedule, with NO open hypothesis -/

theorem prologue_at_schedule_closed (sources : RepairSource.EightSources) (k r D : ℕ)
    (hD : 1 ≤ D) :
    ∃ (extra ps : ℕ) (preFuel : ℕ → ℕ) (pre : Machine (218 + (60 + extra) + 1) ps),
      RepairSource.CloseoutFinal.C10PrologueUniform.Prologue extra
        (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D preFuel pre :=
  ⟨_, _, _, _,
    prologue_at_schedule sources k r D hD (widthReader sources k) (readerIn sources k)
      (readerQ sources k) (readerIn_ne sources k) (readerFuel sources k)
      (width_reader sources k)⟩

open NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)

/-- The retained sentinel width is in the seed's private region. -/
theorem retainedSlot_private {tw : ℕ} (r D : ℕ) (inW : Fin tw) :
    301 ≤ (bankSlots tw r D inW (stripSlotsOf tw r D 0)).val ∧
      (bankSlots tw r D inW (stripSlotsOf tw r D 0)).val < 301 + tapesOf tw r D := by
  have hinlt := inW.isLt
  apply bankSlots_private r D inW
  · intro h
    have hv := congrArg Fin.val h
    change tw + 20 + 2 * r + (24 + 2 * D) = inW.val at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change tw + 20 + 2 * r + (24 + 2 * D) = tw at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    change tw + 20 + 2 * r + (24 + 2 * D) = tw + 1 at hv
    omega

/-- The same closed prologue, now retaining its already computed sentinel
width word in the same actual output witness. No loader or fuel is added. -/
theorem prologue_at_schedule_closed_retained (sources : RepairSource.EightSources)
    (k r D : ℕ) (hD : 1 ≤ D) :
    ∃ (extra ps widthTape : ℕ) (preFuel : ℕ → ℕ)
      (pre : Machine (218 + (60 + extra) + 1) ps),
      301 ≤ widthTape ∧ widthTape < 218 + (60 + extra) ∧
      ∀ (len : ℕ) (x : BitInput len) (bits : List Bool),
      ∃ w : ℕ → List Bool,
        w widthTape = CompareMachine.word (clauseWidth D (widthAt sources k len)) ∧
        Step pre (preFuel len) (fun _ => 0)
          (bank [] [] [] (List.ofFn x) bits (fun _ => []))
          (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
          (Fin.addCases (motive := fun _ => List Bool)
            (bank [] (CompareMachine.word 0)
              (List.replicate (entryWidthSchedule sources k r len) true) (List.ofFn x) bits w)
            (fun _ : Fin 1 => CompareMachine.word
              (2 ^ clauseWidth D (widthAt sources k len)))) := by
  let tw := HierarchyPrefix.tapes k (rp sources) (rq sources)
  let e := tapesOf tw r D
  let slots := bankSlots tw r D (readerIn sources k)
  let sourceSlot := stripSlotsOf tw r D 0
  let seed := RecoveryFocus.machine slots
    (engineMachine r D (widthReader sources k) (readerQ sources k) (thresholdFloor sources))
  obtain ⟨hlo, hhi⟩ := retainedSlot_private r D (readerIn sources k)
  refine ⟨e + 23, _, (slots sourceSlot).val,
    prologueFuel D (widthAt sources k)
      (engineFuel r D (readerFuel sources k) (thresholdFloor sources) (widthAt sources k)),
    prologueMachine e seed, hlo, ?_, ?_⟩
  · change (bankSlots tw r D (readerIn sources k) (stripSlotsOf tw r D 0)).val < _
    change (bankSlots tw r D (readerIn sources k) (stripSlotsOf tw r D 0)).val < 301 + e at hhi
    omega
  · intro len x bits
    obtain ⟨out, hi, hd, he, hw, hs⟩ := engine_of_widthReader_retained r D hD
      (widthReader sources k) (readerIn sources k) (readerQ sources k) (readerIn_ne sources k)
      (thresholdFloor sources) (widthAt sources k) (readerFuel sources k)
      (width_reader sources k) len x
    obtain ⟨junk, hb, hc, hseed, htrace⟩ := seed_run_of_engine e
      (engineMachine r D (widthReader sources k) (readerQ sources k) (thresholdFloor sources))
      slots (bankSlots_injective tw r D (readerIn sources k))
      (inSlotOf r D (readerIn sources k)) (driverSlotOf tw r D) (expSlotOf tw r D)
      (bankSlots_in r D (readerIn sources k)) (bankSlots_driver tw r D (readerIn sources k))
      (bankSlots_exp tw r D (readerIn sources k)) (bankSlots_private r D (readerIn sources k))
      (entryWidthSchedule sources k r) (widthAt sources k) D
      (engineFuel r D (readerFuel sources k) (thresholdFloor sources) (widthAt sources k))
      len x bits out hi hd he hs
    obtain ⟨w, hpre, hkeep⟩ := prologue_run_of_seed e (entryWidthSchedule sources k r)
      (widthAt sources k) D
      (engineFuel r D (readerFuel sources k) (thresholdFloor sources) (widthAt sources k))
      seed len x bits junk hb hc hseed
    exact ⟨w, ((hkeep _ hlo hhi).trans (htrace sourceSlot)).trans hw, hpre⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SeedEngine
