import Proof.MachineModel.OrdinaryPartitionPass
import Proof.MachineModel.OrdinaryRotationStage

/-! One complete ordinary radix round: stable Boolean partition followed by
record rotation, with executed links, paid resets and retained workspace. -/
namespace NearCubicWires.RepairOrdinary.RadixRound
open LocalBitMultitape StablePartition
open StablePartition.Workspace (overlay)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def records (rs : List Record) : List Record := (PartitionPass.ordered rs).map RecordRotate.rotate

@[simp] theorem stream_length (rs : List Record) : (stream (records rs)).length = (stream rs).length := by
  rw [records, RecordRotate.rotate_stream_length, PartitionPass.ordered_length]

def machine : Machine 4 38 := Composition.machine PartitionPass.machine RotationStage.machine

theorem radix_round (rs : List Record) (junk : List Bool) (old : Bool → List Bool)
    (capacity : ℕ) (hi : (stream rs).length + junk.length ≤ capacity)
    (ho : ∀ tag, (old tag).length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 38, ∃ nextJunk : List Bool,
      run machine (10 * (stream rs).length + 10)
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else old (i.val == 2))
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) = some r ∧
      r.final.tapes 1 = stream (records rs) ++ nextJunk ∧
      (∀ i : Fin 3, (r.final.tapes (i.castAdd 1)).length ≤ capacity) ∧
      r.final.tapes 3 = List.replicate (2 * capacity) false ∧
      (∀ i, r.final.heads i = 0) ∧
      r.steps ≤ 10 * (stream rs).length + 10 ∧ r.peakTapeCells ≤ 8 * capacity + 1 := by
  let input : Fin 4 → List Bool := Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
    (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else old (i.val == 2))
    (fun _ : Fin 1 => List.replicate (2 * capacity) false)
  let f := 6 * (stream rs).length + 7
  let g := 2 * (RecordRotate.recordsCost (PartitionPass.ordered rs) + 1) + 2
  obtain ⟨first, hfirst, hfirstOut, hfirstCells, hfirstCounter, hfirstHeads, hfirstSteps, hfirstPeak⟩ :=
    PartitionPass.partition_pass rs junk old capacity hi ho
  have hsource : first.final.tapes 0 = stream (PartitionPass.ordered rs) ++ junk := by
    rw [hfirstOut]
    simp only [overlay, PartitionPass.ordered_length, List.drop_left]
  have hinput : (stream (PartitionPass.ordered rs)).length + junk.length ≤ capacity := by
    simpa only [PartitionPass.ordered_length] using hi
  have hback : (first.final.tapes 1).length ≤ capacity := by simpa using hfirstCells 1
  have hunused : (first.final.tapes 2).length ≤ capacity := by simpa using hfirstCells 2
  obtain ⟨second, hsecond, hsecondOut, hsecondCells, hsecondCounter, hsecondHeads, hsecondSteps, hsecondPeak⟩ :=
    RotationStage.rotation_stage (PartitionPass.ordered rs) junk (first.final.tapes 1) (first.final.tapes 2)
      capacity hinput hback hunused
  have hentry : Composition.restart first.final RotationStage.machine.start =
      initialConfiguration RotationStage.machine
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then stream (PartitionPass.ordered rs) ++ junk
            else if i.val = 1 then first.final.tapes 1 else first.final.tapes 2)
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfirstHeads i
    · funext i
      fin_cases i
      · simpa [Composition.restart, initialConfiguration, Fin.addCases] using hsource
      · simp [Composition.restart, initialConfiguration, Fin.addCases]
      · simp [Composition.restart, initialConfiguration, Fin.addCases]
      · simpa [Composition.restart, initialConfiguration, Fin.addCases] using hfirstCounter
  have hsuffix : runFrom RotationStage.machine g (Composition.restart first.final RotationStage.machine.start) = some second := by
    rw [hentry]
    exact hsecond
  have hj := Composition.run_join PartitionPass.machine RotationStage.machine f g _ first second hfirst hsuffix
  let joined := Composition.joinedReceipt first second
  have hjrun : run machine (f + 1 + g) input = some joined := by
    simpa [run, initialConfiguration, machine, Composition.machine, Composition.leftConfig, joined, input] using hj
  have hg : g ≤ 4 * (stream rs).length + 2 := by
    have hc := RecordRotate.recordsCost_le (PartitionPass.ordered rs)
    have hl := PartitionPass.ordered_length rs
    simp only [stream, List.length_append, List.length_singleton] at hl
    simp only [g, stream, List.length_append, List.length_singleton]
    omega
  have hbudget : f + 1 + g ≤ 10 * (stream rs).length + 10 := by dsimp only [f]; omega
  have hmore := run_moreFuel machine (f + 1 + g)
    ((10 * (stream rs).length + 10) - (f + 1 + g)) input joined hjrun
  refine ⟨joined, (first.final.tapes 1).drop (stream (records rs)).length,
    ?_, hsecondOut, hsecondCells, hsecondCounter, hsecondHeads, ?_, ?_⟩
  · simpa only [Nat.add_sub_of_le hbudget] using hmore
  · change first.steps + 1 + second.steps ≤ 10 * (stream rs).length + 10
    rw [PartitionPass.ordered_length] at hsecondSteps
    omega
  · change max first.peakTapeCells second.peakTapeCells ≤ 8 * capacity + 1
    omega

end NearCubicWires.RepairOrdinary.RadixRound
