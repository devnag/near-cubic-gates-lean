import Proof.MachineModel.OrdinaryStreamConcat
import Proof.MachineModel.OrdinaryRewindWorkspace
import Proof.Foundations.OrdinaryTapeRenaming
import Proof.Foundations.OrdinaryComposition

/-! Actual split/reset → concatenate/reset application on four reused tapes.
The combined record stream returns to tape zero; source assumptions play no
role in this local ordinary-time computation. -/
namespace NearCubicWires.RepairOrdinary.PartitionPass
open LocalBitMultitape StablePartition
open StablePartition.Workspace (overlay overlay_length outputTape)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
@[simp] theorem layout_zero : layout 0 = 1 := by decide
@[simp] theorem layout_one : layout 1 = 2 := by decide
@[simp] theorem layout_two : layout 2 = 0 := by decide
@[simp] theorem layout_symm_zero : layout.symm 0 = 2 := by decide
@[simp] theorem layout_symm_one : layout.symm 1 = 0 := by decide
@[simp] theorem layout_symm_two : layout.symm 2 = 1 := by decide

def concatMachine : Machine 3 9 := TapeRenaming.machine layout StreamConcat.machine

theorem concat_layout (xs ys : List Record) (leftJunk rightJunk backing : List Bool) (capacity : ℕ)
    (hl : (stream xs).length + leftJunk.length ≤ capacity)
    (hr : (stream ys).length + rightJunk.length ≤ capacity)
    (ho : (stream (xs ++ ys)).length ≤ capacity) (hb : backing.length ≤ capacity) :
    ∃ r : ExecutionReceipt 3 9,
      run concatMachine ((stream xs).length + (stream ys).length)
        (fun i => if i.val = 0 then backing
          else if i.val = 1 then stream xs ++ leftJunk else stream ys ++ rightJunk) = some r ∧
      r.final.tapes 0 = overlay (stream (xs ++ ys)) backing ∧
      (∀ i, (r.final.tapes i).length ≤ capacity) ∧
      r.steps = (stream xs).length + (stream ys).length ∧ r.peakTapeCells ≤ 4 * capacity := by
  obtain ⟨source, hs, _, _, hout, hcells, hsteps, hpeak⟩ :=
    StreamConcat.concat_capacity xs ys leftJunk rightJunk backing capacity hl hr ho hb
  have hn := TapeRenaming.run_rename layout StreamConcat.machine
    ((stream xs).length + (stream ys).length) _ source hs
  have hinit : initialConfiguration concatMachine
        (fun i => if i.val = 0 then backing
          else if i.val = 1 then stream xs ++ leftJunk else stream ys ++ rightJunk) =
      TapeRenaming.config layout (initialConfiguration StreamConcat.machine
        (fun i => if i.val = 0 then stream xs ++ leftJunk
          else if i.val = 1 then stream ys ++ rightJunk else backing)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [initialConfiguration, TapeRenaming.config]
  refine ⟨TapeRenaming.receipt layout source, ?_, ?_, ?_, hsteps, hpeak⟩
  · change runFrom concatMachine _ _ = _
    rw [hinit]
    exact hn
  · simpa [TapeRenaming.receipt, TapeRenaming.config] using hout
  · intro i
    exact hcells (layout.symm i)

theorem concat_reset (xs ys : List Record) (leftJunk rightJunk backing : List Bool) (capacity : ℕ)
    (hl : (stream xs).length + leftJunk.length ≤ capacity)
    (hr : (stream ys).length + rightJunk.length ≤ capacity)
    (ho : (stream (xs ++ ys)).length ≤ capacity) (hb : backing.length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 11,
      run (Rewind.machine concatMachine) (2 * ((stream xs).length + (stream ys).length) + 2)
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then backing
            else if i.val = 1 then stream xs ++ leftJunk else stream ys ++ rightJunk)
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) = some r ∧
      r.final.tapes 0 = overlay (stream (xs ++ ys)) backing ∧
      (∀ i : Fin 3, (r.final.tapes (i.castAdd 1)).length ≤ capacity) ∧
      r.final.tapes 3 = List.replicate (2 * capacity) false ∧
      (∀ i, r.final.heads i = 0) ∧
      r.steps = 2 * ((stream xs).length + (stream ys).length) + 2 ∧
      r.peakTapeCells ≤ 8 * capacity := by
  obtain ⟨source, hs, hout, hcells, hsteps, hpeak⟩ :=
    concat_layout xs ys leftJunk rightJunk backing capacity hl hr ho hb
  obtain ⟨r, hrun, he, hcounter, hheads, hcount, hspace⟩ := Rewind.Workspace.reset_workspace
    concatMachine ((stream xs).length + (stream ys).length) _ source hs (2 * capacity)
  refine ⟨r, ?_, ?_, ?_, ?_, hheads, ?_, ?_⟩
  · simpa only [hsteps] using hrun
  · have h := (he 0).trans hout
    simpa using h
  · intro i
    rw [he i]
    exact hcells i
  · have hn : max (2 * capacity) source.steps = 2 * capacity := max_eq_left (by omega)
    simpa [hn] using hcounter
  · simpa only [hsteps] using hcount
  · omega

def ordered (rs : List Record) : List Record := selected false rs ++ selected true rs

theorem ordered_length (rs : List Record) : (stream (ordered rs)).length = (stream rs).length := by
  have h := selected_lengths rs
  simp [ordered, stream, recordsBits] at h ⊢
  omega

theorem selected_streams_length (rs : List Record) :
    (stream (selected false rs)).length + (stream (selected true rs)).length = (stream rs).length + 1 := by
  have h := selected_lengths rs
  simp only [stream, List.length_append, List.length_singleton]
  omega

def machine : Machine 4 22 :=
  Composition.machine (Rewind.machine StablePartition.machine) (Rewind.machine concatMachine)

theorem partition_pass (rs : List Record) (junk : List Bool) (old : Bool → List Bool)
    (capacity : ℕ) (hi : (stream rs).length + junk.length ≤ capacity)
    (ho : ∀ tag, (old tag).length ≤ capacity) :
    ∃ r : ExecutionReceipt 4 22,
      run machine (6 * (stream rs).length + 7)
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else old (i.val == 2))
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) = some r ∧
      r.final.tapes 0 = overlay (stream (ordered rs)) (stream rs ++ junk) ∧
      (∀ i : Fin 3, (r.final.tapes (i.castAdd 1)).length ≤ capacity) ∧
      r.final.tapes 3 = List.replicate (2 * capacity) false ∧
      (∀ i, r.final.heads i = 0) ∧
      r.steps ≤ 6 * (stream rs).length + 7 ∧ r.peakTapeCells ≤ 8 * capacity + 1 := by
  let input : Fin 4 → List Bool := Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
    (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk else old (i.val == 2))
    (fun _ : Fin 1 => List.replicate (2 * capacity) false)
  let f := 2 * ((stream rs).length + rs.length) + 2
  let g := 2 * ((stream (selected false rs)).length + (stream (selected true rs)).length) + 2
  obtain ⟨first, hfirst, hfirstOut, hfirstCells, hcounter, hfirstHeads, hfirstSteps, hfirstPeak⟩ :=
    Rewind.Workspace.partition_reset_fixed_workspace rs junk old capacity hi ho
  have hfirstInput : first.final.tapes 0 = stream rs ++ junk := by
    obtain ⟨raw, hraw, hrawInput, _, _, hrawSteps, _⟩ := StablePartition.Workspace.partition_workspace rs junk old
    obtain ⟨checked, hchecked, hcheckOut, _, _, _, _⟩ := Rewind.Workspace.reset_workspace
      StablePartition.machine ((stream rs).length + rs.length) _ raw hraw (2 * capacity)
    have hc : run (Rewind.machine StablePartition.machine) f input = some checked := by
      simpa only [f, input, hrawSteps] using hchecked
    have he : first = checked := Option.some.inj (hfirst.symm.trans hc)
    rw [he]
    have hh := (hcheckOut 0).trans hrawInput
    simpa using hh
  let leftJunk := (old false).drop (stream (selected false rs)).length
  let rightJunk := (old true).drop (stream (selected true rs)).length
  have hl : (stream (selected false rs)).length + leftJunk.length ≤ capacity := by
    have hc := hfirstCells (1 : Fin 3)
    have he := hfirstOut false
    change (first.final.tapes ((outputTape false).castAdd 1)).length ≤ capacity at hc
    rw [he] at hc
    simpa only [overlay, List.length_append, leftJunk] using hc
  have hr : (stream (selected true rs)).length + rightJunk.length ≤ capacity := by
    have hc := hfirstCells (2 : Fin 3)
    have he := hfirstOut true
    change (first.final.tapes ((outputTape true).castAdd 1)).length ≤ capacity at hc
    rw [he] at hc
    simpa only [overlay, List.length_append, rightJunk] using hc
  have hout : (stream (selected false rs ++ selected true rs)).length ≤ capacity := by
    change (stream (ordered rs)).length ≤ capacity
    rw [ordered_length]
    omega
  have hback : (stream rs ++ junk).length ≤ capacity := by simpa using hi
  obtain ⟨second, hsecond, hsecondOut, hsecondCells, hsecondCounter, hsecondHeads, hsecondSteps, hsecondPeak⟩ :=
    concat_reset (selected false rs) (selected true rs) leftJunk rightJunk (stream rs ++ junk)
      capacity hl hr hout hback
  have hentry : Composition.restart first.final (Rewind.machine concatMachine).start =
      initialConfiguration (Rewind.machine concatMachine)
        (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
          (fun i : Fin 3 => if i.val = 0 then stream rs ++ junk
            else if i.val = 1 then stream (selected false rs) ++ leftJunk
            else stream (selected true rs) ++ rightJunk)
          (fun _ : Fin 1 => List.replicate (2 * capacity) false)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfirstHeads i
    · funext i
      fin_cases i
      · simpa [Composition.restart, initialConfiguration, Fin.addCases] using hfirstInput
      · simpa [Composition.restart, initialConfiguration, Fin.addCases, outputTape, overlay, leftJunk] using hfirstOut false
      · simpa [Composition.restart, initialConfiguration, Fin.addCases, outputTape, overlay, rightJunk] using hfirstOut true
      · simpa [Composition.restart, initialConfiguration, Fin.addCases] using hcounter
  have hsuffix : runFrom (Rewind.machine concatMachine) g
      (Composition.restart first.final (Rewind.machine concatMachine).start) = some second := by
    rw [hentry]
    exact hsecond
  have hj := Composition.run_join (Rewind.machine StablePartition.machine) (Rewind.machine concatMachine)
    f g _ first second hfirst hsuffix
  let joined := Composition.joinedReceipt first second
  have hjrun : run machine (f + 1 + g) input = some joined := by
    simpa [run, initialConfiguration, machine, Composition.machine, Composition.leftConfig, joined, input] using hj
  have hsum := selected_streams_length rs
  have hcount := record_count_le rs
  have hbudget : f + 1 + g ≤ 6 * (stream rs).length + 7 := by
    simp only [f, g]
    simp only [stream, List.length_append, List.length_singleton] at hcount ⊢
    simp only [stream, List.length_append, List.length_singleton] at hsum
    omega
  have hmore := run_moreFuel machine (f + 1 + g)
    ((6 * (stream rs).length + 7) - (f + 1 + g)) input joined hjrun
  refine ⟨joined, ?_, hsecondOut, hsecondCells, hsecondCounter, hsecondHeads, ?_, ?_⟩
  · simpa only [Nat.add_sub_of_le hbudget] using hmore
  · change first.steps + 1 + second.steps ≤ 6 * (stream rs).length + 7
    omega
  · change max first.peakTapeCells second.peakTapeCells ≤ 8 * capacity + 1
    omega

end NearCubicWires.RepairOrdinary.PartitionPass
