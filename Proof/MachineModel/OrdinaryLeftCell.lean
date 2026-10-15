import Proof.MachineModel.OrdinaryLeftPlaneCell

/-! Generate the upper boundary and execute the left-plane cell test on the
same scalar workspace, retaining the exact whole final configuration. -/
namespace NearCubicWires.RepairOrdinary.LeftCell
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 7 ≃ Fin 7 where
  toFun := ![0, 4, 2, 5, 6, 1, 3]
  invFun := ![0, 5, 2, 6, 1, 3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 7 → Fin 7) = ![0, 5, 2, 6, 1, 3, 4] := rfl

def advance : Machine 7 7 := TapeEmbedding.machine 3 BoundaryAdvance.machine
def interval : Machine 7 9 := TapeRenaming.machine layout (TapeEmbedding.machine 2 Interval.machine)
def machine : Machine 7 16 := Composition.machine advance interval
def input (width a b rank : ℕ) (backing output : List Bool) (mask : Bool) : Configuration 7 7 :=
  ⟨advance.start, ![0, 0, 0, 0, 0, output.length, 0],
    ![frame (binary width a), frame (binary width b), backing, List.replicate (2 * width + 1) false,
      frame (binary width rank), output, [mask]]⟩
def selected (a b rank : ℕ) (mask : Bool) : Bool :=
  (decide (a ≤ rank) && !decide (a + b ≤ rank)) && mask
def finished (width a b rank : ℕ) (output : List Bool) (mask : Bool) : Configuration 7 16 :=
  ⟨15, ![2 * width, 0, 2 * width, 0, 2 * width, output.length + 1, 0],
    ![frame (binary width a), frame (binary width b), frame (binary width (a + b)),
      List.replicate (2 * width + 1) false, frame (binary width rank), output ++ [selected a b rank mask], [mask]]⟩

theorem cell_run (width a b rank : ℕ) (backing output : List Bool) (mask : Bool)
    (hfit : a + b < 2 ^ width) (hrank : rank < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 7 16,
      runFrom machine (6 * width + 6) (Composition.leftConfig 9 (input width a b rank backing output mask)) = some r ∧
      r.final = finished width a b rank output mask ∧
      r.steps = 6 * width + 6 ∧ r.peakTapeCells ≤ 14 * width + output.length + 8 := by
  obtain ⟨first, hfirst, h0, h1, h2, h3, hheads, hsteps, hpeak⟩ :=
    BoundaryAdvance.advance_run width a b backing hfit hb
  let extraHeads : Fin 3 → ℕ := ![0, output.length, 0]
  let extraTapes : Fin 3 → List Bool := ![frame (binary width rank), output, [mask]]
  have hp := TapeEmbedding.run_embed BoundaryAdvance.machine extraHeads extraTapes _ _ first hfirst
  let p := TapeEmbedding.receipt extraHeads extraTapes first
  have hi : TapeEmbedding.config extraHeads extraTapes
      (initialConfiguration BoundaryAdvance.machine (BoundaryAdvance.input width a b backing)) =
      input width a b rank backing output mask := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, input, extraHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, BoundaryAdvance.input, input, extraTapes, Fin.addCases]
  rw [hi] at hp
  have scanPrefix := Interval.interval_prefix [] [] [] (binary width a) (binary width rank) (binary width (a + b))
    [] [] [] output mask true true (by simp) (by simp)
  obtain ⟨second, hsecond, hf, hs, hspeak⟩ := scanPrefix.run (by rfl) (by simp; omega)
  have hsecond' : runFrom Interval.machine (2 * width + 1)
      (Interval.config (Interval.scanState true true) (frame (binary width a)) (frame (binary width rank))
        (frame (binary width (a + b))) 0 0 0 output mask) = some second := by simpa using hsecond
  have hfinal : second.final = Interval.config 8 (frame (binary width a)) (frame (binary width rank))
      (frame (binary width (a + b))) (2 * width) (2 * width) (2 * width) (output ++ [selected a b rank mask]) mask := by
    have ha : a < 2 ^ width := by omega
    have hl := Compare.decision_le (binary width a) (binary width rank) (by simp)
    have hh := Compare.decision_le (binary width (a + b)) (binary width rank) (by simp)
    simpa [selected, hl, hh, binary_value _ _ ha, binary_value _ _ hrank, binary_value _ _ hfit] using hf
  let retained : Fin 2 → List Bool := ![frame (binary width b), List.replicate (2 * width + 1) false]
  have he := TapeEmbedding.run_embed Interval.machine (fun _ : Fin 2 => 0) retained _ _ second hsecond'
  have hq := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 Interval.machine) _ _ _ he
  let q := TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 2 => 0) retained second)
  have hmid : Composition.restart p.final interval.start =
      TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 2 => 0) retained
        (Interval.config (Interval.scanState true true) (frame (binary width a)) (frame (binary width rank))
          (frame (binary width (a + b))) 0 0 0 output mask)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, p, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, Interval.config, extraHeads, Fin.addCases, hheads]
    · funext i
      fin_cases i <;> simp [Composition.restart, p, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, Interval.config, extraTapes, retained, Fin.addCases, h0, h1, h2, h3]
  have hq' : runFrom interval (2 * width + 1) (Composition.restart p.final interval.start) = some q := by
    rw [hmid]
    exact hq
  have hj := Composition.run_join advance interval (4 * width + 4) (2 * width + 1)
    (input width a b rank backing output mask) p q hp hq'
  have hbudget : (4 * width + 4) + 1 + (2 * width + 1) = 6 * width + 6 := by omega
  refine ⟨Composition.joinedReceipt p q, by rw [hbudget] at hj; exact hj, ?_, ?_, ?_⟩
  · apply configuration_ext
    · change second.final.control.natAdd 7 = (15 : Fin 16)
      rw [hfinal]
      change (8 : Fin 9).natAdd 7 = (15 : Fin 16)
      decide
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt,
        TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, hfinal, Interval.config, finished, Fin.addCases]
    · funext i
      fin_cases i <;> simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt,
        TapeRenaming.config, TapeEmbedding.receipt, TapeEmbedding.config, hfinal, Interval.config, finished, retained, Fin.addCases]
  · change first.steps + 1 + second.steps = _
    simp only [hsteps, binary_length] at hs ⊢
    omega
  · change max (first.peakTapeCells + TapeEmbedding.extraCells extraTapes)
      (second.peakTapeCells + TapeEmbedding.extraCells retained) ≤ _
    simp only [List.nil_append, List.append_nil, frame_length, binary_length] at hspeak
    simp [TapeEmbedding.extraCells, extraTapes, retained, Fin.sum_univ_succ]
    omega

end NearCubicWires.RepairOrdinary.LeftCell
