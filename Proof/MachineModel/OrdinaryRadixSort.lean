import Proof.MachineModel.OrdinaryRadixSemantics

/-! The complete sorting consumer: one actual fixed-machine run, exact sorted
permutation, explicit live output/suffix and complete ordinary resource bounds.
Input stream/width/counter production remains a separately charged caller. -/
namespace NearCubicWires.RepairOrdinary.RadixSort
open LocalBitMultitape StablePartition RadixWorkspace RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outputTape (width : ℕ) : Fin 5 := if RadixIteration.finalPhase width false then 1 else 0

theorem sort_run {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (width : ℕ) (hw : ∀ r ∈ rs, (word r).length = width) :
    ∃ sorted : List Record, ∃ junk : List Bool, ∃ r : ExecutionReceipt 5 80,
      sorted.Perm rs ∧ sorted.Pairwise (fun a b => value (word a) ≤ value (word b)) ∧
      run RadixIteration.machine (width * (10 * (stream rs).length + 12) + 1)
        (RadixIteration.boundary w false 0 width).tapes = some r ∧
      r.final.tapes (outputTape width) = stream sorted ++ junk ∧
      (stream sorted).length + junk.length ≤ capacity ∧
      (∀ i : Fin 4, r.final.heads (i.castAdd 1) = 0) ∧
      r.final.tapes 4 = RadixIteration.driver width ∧ r.final.heads 4 = width ∧
      r.steps ≤ width * (10 * (stream rs).length + 12) + 1 ∧
      r.peakTapeCells ≤ 8 * capacity + width + 2 := by
  obtain ⟨next, r, hr, hf, hs, hp⟩ := RadixIteration.iteration_run w width
  obtain ⟨hperm, hsorted⟩ := sorted_permutation width rs hw
  refine ⟨RadixIteration.records width rs, next.junk, r, hperm, hsorted, hr,
    ?_, next.inputFit, ?_, ?_, ?_, hs, hp⟩
  · rw [hf]
    cases he : RadixIteration.finalPhase width false <;>
      simp [RadixIteration.finished, RadixIteration.boundary, UnaryController.boundary,
        outputTape, he, State.phaseTapes, State.tapes, layout, Fin.addCases]
  · intro i
    rw [hf]
    simp only [RadixIteration.finished, RadixIteration.boundary,
      UnaryController.boundary, Fin.addCases_left]
  · rw [hf]
    simp [RadixIteration.finished, RadixIteration.boundary, UnaryController.boundary, Fin.addCases]
  · rw [hf]
    simp [RadixIteration.finished, RadixIteration.boundary, UnaryController.boundary, Fin.addCases]

end NearCubicWires.RepairOrdinary.RadixSort
