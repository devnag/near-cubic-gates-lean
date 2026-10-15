import Proof.MachineModel.OrdinaryBoundaryAdvance

/-! Generate the next bucket boundary and consume it in the actual cell
comparison. The matrix output is appended; its cursor is never rewound. -/
namespace NearCubicWires.RepairOrdinary.RightCell
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 6 → Fin 6) = ![3, 4, 0, 5, 1, 2] := rfl

def advance : Machine 6 7 := TapeEmbedding.machine 2 BoundaryAdvance.machine
def compare : Machine 6 5 := TapeRenaming.machine layout (TapeEmbedding.machine 3 Compare.machine)
def machine : Machine 6 12 := Composition.machine advance compare
def config (width a b rank : ℕ) (backing output : List Bool) : Configuration 6 7 :=
  ⟨advance.start, ![0, 0, 0, 0, 0, output.length],
    ![frame (binary width a), frame (binary width b), backing, List.replicate (2 * width + 1) false,
      frame (binary width rank), output]⟩

theorem cell_run (width a b rank : ℕ) (backing output : List Bool)
    (hfit : a + b < 2 ^ width) (hrank : rank < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ∃ r : ExecutionReceipt 6 12,
      runFrom machine (6 * width + 6) (Composition.leftConfig 5 (config width a b rank backing output)) = some r ∧
      r.final.tapes 5 = output ++ [decide (a + b ≤ rank)] ∧
      r.final.tapes 2 = frame (binary width (a + b)) ∧
      r.final.tapes 1 = frame (binary width b) ∧
      r.final.heads 5 = output.length + 1 ∧
      r.steps = 6 * width + 6 ∧ r.peakTapeCells ≤ 14 * width + output.length + 7 := by
  obtain ⟨first, hfirst, h0, h1, h2, h3, hheads, hsteps, hpeak⟩ :=
    BoundaryAdvance.advance_run width a b backing hfit hb
  let extraHeads : Fin 2 → ℕ := ![0, output.length]
  let extraTapes : Fin 2 → List Bool := ![frame (binary width rank), output]
  have hp := TapeEmbedding.run_embed BoundaryAdvance.machine extraHeads extraTapes _ _ first hfirst
  let p := TapeEmbedding.receipt extraHeads extraTapes first
  have hi : TapeEmbedding.config extraHeads extraTapes
      (initialConfiguration BoundaryAdvance.machine (BoundaryAdvance.input width a b backing)) =
      config width a b rank backing output := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, config, extraHeads, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, initialConfiguration, BoundaryAdvance.input, config, extraTapes, Fin.addCases]
  rw [hi] at hp
  obtain ⟨second, hsecond, hf, hs, hspeak⟩ := Compare.compare_run [] [] (binary width (a + b))
    (binary width rank) [] [] output (by simp)
  have hsecond' : runFrom Compare.machine (2 * width + 1)
      (Compare.config (Compare.scanState true) (frame (binary width (a + b))) (frame (binary width rank)) 0 0 output) =
      some second := by simpa using hsecond
  let retained : Fin 3 → List Bool := ![frame (binary width a), frame (binary width b), List.replicate (2 * width + 1) false]
  have he := TapeEmbedding.run_embed Compare.machine (fun _ : Fin 3 => 0) retained _ _ second hsecond'
  have hq := TapeRenaming.run_rename layout (TapeEmbedding.machine 3 Compare.machine) _ _ _ he
  let q := TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 3 => 0) retained second)
  have hmid : Composition.restart p.final compare.start =
      TapeRenaming.config layout (TapeEmbedding.config (fun _ : Fin 3 => 0) retained
        (Compare.config (Compare.scanState true) (frame (binary width (a + b))) (frame (binary width rank)) 0 0 output)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, p, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, Compare.config, extraHeads, Fin.addCases, hheads]
    · funext i
      fin_cases i <;> simp [Composition.restart, p, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, Compare.config, extraTapes, retained, Fin.addCases, h0, h1, h2, h3]
  have hq' : runFrom compare (2 * width + 1) (Composition.restart p.final compare.start) = some q := by
    rw [hmid]
    exact hq
  have hj := Composition.run_join advance compare (4 * width + 4) (2 * width + 1)
    (config width a b rank backing output) p q hp hq'
  have hbudget : (4 * width + 4) + 1 + (2 * width + 1) = 6 * width + 6 := by omega
  refine ⟨Composition.joinedReceipt p q, by rw [hbudget] at hj; exact hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, hf, Compare.config, Fin.addCases,
      binary_value _ _ hfit, binary_value _ _ hrank]
  · simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, hf, Compare.config, Fin.addCases]
  · simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, retained, Fin.addCases]
  · simp [Composition.joinedReceipt, Composition.rightConfig, q, TapeRenaming.receipt, TapeRenaming.config,
      TapeEmbedding.receipt, TapeEmbedding.config, hf, Compare.config, Fin.addCases]
  · change first.steps + 1 + second.steps = _
    simp only [hsteps, binary_length] at hs ⊢
    omega
  · change max (first.peakTapeCells + TapeEmbedding.extraCells extraTapes)
      (second.peakTapeCells + TapeEmbedding.extraCells retained) ≤ _
    simp only [List.nil_append, List.append_nil, frame_length, binary_length] at hspeak
    simp [TapeEmbedding.extraCells, extraTapes, retained, Fin.sum_univ_succ]
    omega

end NearCubicWires.RepairOrdinary.RightCell
