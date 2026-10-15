import Proof.Wire_3_5.BlockOfRun
import Proof.Wire_3_5.BlockCost
import Proof.MachineModel.OrdinaryAdd
import Proof.MachineModel.OrdinaryCompare
import Proof.MachineModel.OrdinaryBoundedCounter
import Proof.Hierarchy.HierarchyBinaryMultiply

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RadixSemantics

/-! ## Addition -/

theorem add_config (width a b : ℕ) (backing : List Bool) :
    Add.config (Add.scanState false) (frame (binary width a)) (frame (binary width b)) 0 0 [] backing =
      ⟨Add.machine.start, ![0, 0, 0], ![frame (binary width a), frame (binary width b), backing]⟩ := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [Add.config, StablePartition.Workspace.overlay]

theorem add_runs (width a b : ℕ) (backing : List Bool) (hfit : a + b < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    ∃ r, runFrom Add.machine (2 * width + 1)
      ⟨Add.machine.start, ![0, 0, 0], ![frame (binary width a), frame (binary width b), backing]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := Add.add_run width a b backing hfit hb
  rw [add_config] at hr
  exact ⟨r, hr⟩

/-- Binary addition on framed `w`-bit words, the sum written on tape 2 over a reusable backing. -/
noncomputable def addBlock (width a b : ℕ) (backing : List Bool) (hfit : a + b < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) : Block 3 :=
  ofRunFrom Add.machine (2 * width + 1) ![0, 0, 0]
    ![frame (binary width a), frame (binary width b), backing] (add_runs width a b backing hfit hb)

theorem addBlock_out (width a b : ℕ) (backing : List Bool) (hfit : a + b < 2 ^ width)
    (hb : backing.length ≤ 2 * width + 1) :
    (addBlock width a b backing hfit hb).exitA 2 = frame (binary width (a + b)) ∧
      (addBlock width a b backing hfit hb).exitA 0 = frame (binary width a) ∧
      (addBlock width a b backing hfit hb).exitA 1 = frame (binary width b) ∧
      (addBlock width a b backing hfit hb).exitH = ![2 * width, 2 * width, 2 * width + 1] ∧
      (addBlock width a b backing hfit hb).cost = 2 * width + 1 := by
  obtain ⟨r, hr, h0, h1, h2, hh0, hh1, hh2, _⟩ := Add.add_run width a b backing hfit hb
  have hr' : runFrom Add.machine (2 * width + 1)
      ⟨Add.machine.start, ![0, 0, 0], ![frame (binary width a), frame (binary width b), backing]⟩ = some r := by
    rw [← add_config]; exact hr
  have eA := ofRunFrom_exitA Add.machine (2 * width + 1) ![0, 0, 0]
    ![frame (binary width a), frame (binary width b), backing] (add_runs width a b backing hfit hb) r hr'
  have eH := ofRunFrom_exitH Add.machine (2 * width + 1) ![0, 0, 0]
    ![frame (binary width a), frame (binary width b), backing] (add_runs width a b backing hfit hb) r hr'
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [addBlock, eA]; exact h2
  · rw [addBlock, eA]; exact h0
  · rw [addBlock, eA]; exact h1
  · rw [addBlock, eH]
    funext i
    fin_cases i
    · exact hh0
    · exact hh1
    · exact hh2

/-- The addition is within every class of degree at least 1 once the width is at most `q`. -/
theorem add_within {E : Envelope} {cls : BudgetClass} {q k psi width : ℕ} (hq : 1 ≤ q) (hw : width ≤ q)
    (hd : 1 ≤ classDeg E cls) : Within E cls 3 q k psi (2 * width + 1) :=
  Within.of_poly hq (a := 1) (by rw [pow_one]; omega) hd

/-! ## Comparison -/

theorem compare_runs (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r, runFrom Compare.machine (2 * left.length + 1)
      ⟨Compare.machine.start, ![preLeft.length, preRight.length, output.length],
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := Compare.compare_run preLeft preRight left right tailLeft tailRight output hw
  exact ⟨r, hr⟩

/-- The comparison `value left ≤ value right` of two framed words at given cursors, the decision bit
appended to the output tape. -/
noncomputable def compareBlock (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) : Block 3 :=
  ofRunFrom Compare.machine (2 * left.length + 1) ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (compare_runs preLeft preRight left right tailLeft tailRight output hw)

theorem compareBlock_out (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 2 =
        output ++ [decide (value left ≤ value right)] ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 0 =
        preLeft ++ frame left ++ tailLeft ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 1 =
        preRight ++ frame right ++ tailRight ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitH =
        ![preLeft.length + 2 * left.length, preRight.length + 2 * right.length, output.length + 1] ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).cost = 2 * left.length + 1 := by
  obtain ⟨r, hr, hf, _⟩ := Compare.compare_run preLeft preRight left right tailLeft tailRight output hw
  have eA := ofRunFrom_exitA _ _ _ _ (compare_runs preLeft preRight left right tailLeft tailRight output hw) r hr
  have eH := ofRunFrom_exitH _ _ _ _ (compare_runs preLeft preRight left right tailLeft tailRight output hw) r hr
  rw [hf] at eA eH
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eH]
    funext i
    fin_cases i <;> simp [Compare.config]

theorem compare_within {E : Envelope} {cls : BudgetClass} {q k psi len : ℕ} (hq : 1 ≤ q) (hl : len ≤ q)
    (hd : 1 ≤ classDeg E cls) : Within E cls 3 q k psi (2 * len + 1) :=
  Within.of_poly hq (a := 1) (by rw [pow_one]; omega) hd

/-! ## Increment with a constant workspace -/

theorem increment_runs (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    ∃ r, run (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
      (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
        (fun _ : Fin 1 => binary width n) (fun _ : Fin 1 => List.replicate width false)) = some r := by
  obtain ⟨_, r, _, hr, _⟩ := BoundedCounter.increment_run width n width hn (le_refl _)
  exact ⟨r, hr⟩

noncomputable def incrementRaw (width n : ℕ) (hn : n + 1 < 2 ^ width) : Block 2 :=
  ofRun (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
    (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
      (fun _ : Fin 1 => binary width n) (fun _ : Fin 1 => List.replicate width false))
    (increment_runs width n hn)

/-- The workspace padded to `w` cells, so the increment's exit bank is a function of `n`. -/
def incrementCaps (width : ℕ) : Fin 2 → ℕ := ![0, width]

theorem increment_exit (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    (padded (incrementRaw width n hn) (incrementCaps width)).exitA =
        ![binary width (n + 1), List.replicate width false] ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).exitH = (fun _ => 0) ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).entryA =
        ![binary width n, List.replicate width false] ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).entryH = (fun _ => 0) := by
  obtain ⟨next, r, hnext, hr, h0, h1, hh, _⟩ := BoundedCounter.increment_run width n width hn (le_refl _)
  have eA := ofRun_exitA _ _ _ (increment_runs width n hn) r hr
  have eH := ofRun_exitH _ _ _ (increment_runs width n hn) r hr
  refine ⟨?_, ?_, ?_, rfl⟩
  · change (fun i => ZeroPadding.pad (incrementCaps width i) ((incrementRaw width n hn).exitA i)) = _
    rw [incrementRaw, eA]
    funext i
    fin_cases i
    · simp [incrementCaps, h0]
    · simp [incrementCaps, h1, ZeroPadding.pad]
      omega
  · change (incrementRaw width n hn).exitH = _
    rw [incrementRaw, eH]
    funext i
    exact hh i
  · change (fun i => ZeroPadding.pad (incrementCaps width i) ((incrementRaw width n hn).entryA i)) = _
    funext i
    fin_cases i
    · simp [incrementCaps, incrementRaw]
      rfl
    · change ZeroPadding.pad width (List.replicate width false) = List.replicate width false
      simp [ZeroPadding.pad]

/-- **The counter increment** `binary w n ↦ binary w (n+1)`, every head at cell 0 before and after, and
a constant `w`-cell workspace, in `2w+2` steps. -/
noncomputable def incrementBlock (width n : ℕ) (hn : n + 1 < 2 ^ width) : Block 2 :=
  congrExit (padded (incrementRaw width n hn) (incrementCaps width))
    (increment_exit width n hn).2.1 (increment_exit width n hn).1

theorem incrementBlock_spec (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    (incrementBlock width n hn).entryA = ![binary width n, List.replicate width false] ∧
      (incrementBlock width n hn).entryH = (fun _ => 0) ∧
      (incrementBlock width n hn).exitA = ![binary width (n + 1), List.replicate width false] ∧
      (incrementBlock width n hn).exitH = (fun _ => 0) ∧
      (incrementBlock width n hn).cost = 2 * width + 2 :=
  ⟨(increment_exit width n hn).2.2.1, (increment_exit width n hn).2.2.2, rfl, rfl, rfl⟩

theorem increment_within {E : Envelope} {cls : BudgetClass} {q k psi width : ℕ} (hq : 1 ≤ q) (hw : width ≤ q)
    (hd : 1 ≤ classDeg E cls) : Within E cls 4 q k psi (2 * width + 2) :=
  Within.of_poly hq (a := 1) (by rw [pow_one]; omega) hd

/-! ## Multiplication -/

theorem multiply_runs (w a : ℕ) (bits : List Bool) (hfit : a * 2 ^ bits.length < 2 ^ w) :
    ∃ r, run HierarchyMultiplyEntry.machine (HierarchyMultiplyEntry.budget w bits)
      (HierarchyMultiplyEntry.input14 w a bits) = some r := by
  obtain ⟨r, hr, _⟩ := HierarchyMultiplyEntry.multiply_run w a bits hfit
  exact ⟨r, hr⟩

/-- Short binary multiplication: `frame (binary w (a · value bits))` on tape 3, every head at cell 0. -/
noncomputable def multiplyBlock (w a : ℕ) (bits : List Bool) (hfit : a * 2 ^ bits.length < 2 ^ w) : Block 14 :=
  ofRun HierarchyMultiplyEntry.machine (HierarchyMultiplyEntry.budget w bits)
    (HierarchyMultiplyEntry.input14 w a bits) (multiply_runs w a bits hfit)

theorem multiplyBlock_out (w a : ℕ) (bits : List Bool) (hfit : a * 2 ^ bits.length < 2 ^ w) :
    (multiplyBlock w a bits hfit).exitA 3 = frame (binary w (a * value bits)) ∧
      (multiplyBlock w a bits hfit).exitA 0 = frame bits ∧
      (multiplyBlock w a bits hfit).exitA 8 = frame (binary w a) ∧
      (multiplyBlock w a bits hfit).exitH = (fun _ => 0) ∧
      (multiplyBlock w a bits hfit).cost = 128 * (w + 1) * (bits.length + 1) := by
  obtain ⟨r, hr, h3, h0, h8, _, _, hh, _⟩ := HierarchyMultiplyEntry.multiply_run w a bits hfit
  have eA := ofRun_exitA _ _ _ (multiply_runs w a bits hfit) r hr
  have eH := ofRun_exitH _ _ _ (multiply_runs w a bits hfit) r hr
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [multiplyBlock, eA]; exact h3
  · rw [multiplyBlock, eA]; exact h0
  · rw [multiplyBlock, eA]; exact h8
  · rw [multiplyBlock, eH]; funext i; exact hh i

theorem multiply_within {E : Envelope} {cls : BudgetClass} {q k psi w len : ℕ} (hq : 1 ≤ q) (hw : w + 1 ≤ q)
    (hl : len + 1 ≤ q) (hd : 2 ≤ classDeg E cls) : Within E cls 128 q k psi (128 * (w + 1) * (len + 1)) := by
  refine Within.of_poly hq (a := 2) ?_ hd
  have := Nat.mul_le_mul hw hl
  rw [pow_two]
  nlinarith

/-! ## Executable twins on small words -/

theorem add_twin : Add.sum (binary 4 5) (binary 4 9) false = binary 4 14 := by decide
theorem compare_twin : Compare.decision (binary 4 5) (binary 4 9) true = true ∧
    Compare.decision (binary 4 9) (binary 4 5) true = false ∧
    Compare.decision (binary 4 7) (binary 4 7) true = true := by decide
theorem increment_twin : binary 3 5 = [true, false, true] ∧ binary 3 6 = [false, true, true] := by decide

end NearCubicWires.WireExponent3_5.Block
