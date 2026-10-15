import Proof.MachineModel.OrdinaryRadixWorkspace
import Proof.MachineModel.OrdinaryUnaryController

/-! The fixed five-tape radix loop applied to its actual reusable workspace.
The unary iteration tape is supplied explicitly and remains occupied. -/
namespace NearCubicWires.RepairOrdinary.RadixIteration
open LocalBitMultitape StablePartition RadixWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 80 := UnaryController.machine RadixWorkspace.machine

def driver (width : ℕ) : List Bool := List.replicate width true ++ [false]

@[simp] theorem driver_length (width : ℕ) : (driver width).length = width + 1 := by
  simp [driver]

theorem read_driver (position width : ℕ) (h : position < width) :
    readTapeBit (driver width) position = true := by
  induction position generalizing width with
  | zero =>
    cases width
    · omega
    · simp [driver, List.replicate_succ, readTapeBit, List.getD]
  | succ position ih =>
    cases width with
    | zero => omega
    | succ width =>
      simpa [driver, List.replicate_succ, readTapeBit, List.getD] using ih width (by omega)

theorem read_driver_end (width : ℕ) : readTapeBit (driver width) width = false := by
  simpa [driver] using Streaming.read_append (List.replicate width true) [] false

def boundary {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (phase : Bool) (position width : ℕ) : Configuration 5 80 :=
  UnaryController.boundary (s := 38) phase (fun _ => 0) (w.phaseTapes phase) position (driver width)

def finished {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (phase : Bool) (width : ℕ) : Configuration 5 80 :=
  { boundary w phase width width with control := UnaryController.stop (s := 38) phase }

theorem boundary_space {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (phase : Bool) (position width : ℕ) :
    (boundary w phase position width).tapeCells ≤ 8 * capacity + width + 2 := by
  have h := state_cells w phase
  rw [boundary, UnaryController.boundary_cells, driver_length]
  omega

theorem round_prefix {capacity : ℕ} {rs : List Record} (w : State capacity rs)
    (phase : Bool) (position width : ℕ) (hpos : position < width) :
    ∃ next : State capacity (RadixRound.records rs), ∃ steps : ℕ,
      Prefix machine (8 * capacity + width + 2) steps
        (boundary w phase position width) (boundary next (!phase) (position + 1) width) ∧
      steps ≤ 10 * (stream rs).length + 12 := by
  obtain ⟨next, r, hr, ht, hh, hs, hp⟩ := workspace_round w phase
  obtain ⟨pre, halted⟩ := UnaryController.body_prefix RadixWorkspace.machine phase
    (initialConfiguration (RadixWorkspace.machine phase) (w.phaseTapes phase)) _ r hr
    (position + 1) (driver width)
  let last : Configuration 4 38 := ⟨r.final.control, fun _ => 0, next.phaseTapes (!phase)⟩
  have hf : r.final = last := configuration_ext rfl (funext hh) ht
  rw [hf] at pre halted
  have hlast : (controlConfig (UnaryController.code phase) (TapeEmbedding.config
      (fun _ : Fin 1 => position + 1) (fun _ : Fin 1 => driver width) last)).tapeCells ≤
      8 * capacity + width + 2 := boundary_space next (!phase) (position + 1) width
  have ret := Prefix.step hlast (UnaryController.body_halted RadixWorkspace.machine phase _)
    (UnaryController.return_step RadixWorkspace.machine phase last (position + 1) (driver width) halted)
    (Prefix.refl (boundary next (!phase) (position + 1) width)
      (boundary_space next (!phase) (position + 1) width))
  have body := pre.enlarge (show r.peakTapeCells + (driver width).length ≤
      8 * capacity + width + 2 by rw [driver_length]; omega)
  have joined := body.trans ret
  have entered := Prefix.step (boundary_space w phase position width)
    (UnaryController.test_halted RadixWorkspace.machine phase)
    (UnaryController.enter_step RadixWorkspace.machine phase (fun _ => 0)
      (w.phaseTapes phase) position (driver width) (read_driver position width hpos)) joined
  refine ⟨next, r.steps + 2, ?_, by omega⟩
  exact entered

def records : ℕ → List Record → List Record
  | 0, rs => rs
  | width + 1, rs => records width (RadixRound.records rs)

def finalPhase : ℕ → Bool → Bool
  | 0, phase => phase
  | width + 1, phase => finalPhase width (!phase)

@[simp] theorem records_stream_length (width : ℕ) (rs : List Record) :
    (stream (records width rs)).length = (stream rs).length := by
  induction width generalizing rs with
  | zero => rfl
  | succ width ih => simp [records, ih]

theorem loop_prefix (remaining : ℕ) {capacity : ℕ} {rs : List Record}
    (w : State capacity rs) (phase : Bool) (position width : ℕ)
    (hw : position + remaining = width) :
    ∃ next : State capacity (records remaining rs), ∃ steps : ℕ,
      Prefix machine (8 * capacity + width + 2) steps
        (boundary w phase position width) (boundary next (finalPhase remaining phase) width width) ∧
      steps ≤ remaining * (10 * (stream rs).length + 12) := by
  induction remaining generalizing rs phase position with
  | zero =>
    have hposition : position = width := by omega
    subst position
    exact ⟨w, 0, Prefix.refl _ (boundary_space w phase width width), by simp⟩
  | succ remaining ih =>
    obtain ⟨next, first, hfirst, hbound⟩ := round_prefix w phase position width (by omega)
    obtain ⟨last, rest, hrest, hrestBound⟩ := ih next (!phase) (position + 1) (by omega)
    refine ⟨last, first + rest, hfirst.trans hrest, ?_⟩
    rw [RadixRound.stream_length] at hrestBound
    calc
      first + rest ≤ (10 * (stream rs).length + 12) +
          remaining * (10 * (stream rs).length + 12) := Nat.add_le_add hbound hrestBound
      _ = (remaining + 1) * (10 * (stream rs).length + 12) := by rw [Nat.add_mul]; omega

theorem iteration_run {capacity : ℕ} {rs : List Record} (w : State capacity rs) (width : ℕ) :
    ∃ next : State capacity (records width rs), ∃ r : ExecutionReceipt 5 80,
      run machine (width * (10 * (stream rs).length + 12) + 1)
        (boundary w false 0 width).tapes = some r ∧
      r.final = finished next (finalPhase width false) width ∧
      r.steps ≤ width * (10 * (stream rs).length + 12) + 1 ∧
      r.peakTapeCells ≤ 8 * capacity + width + 2 := by
  obtain ⟨next, steps, hp, hb⟩ := loop_prefix width w false 0 width (by omega)
  let phase := finalPhase width false
  have hs := UnaryController.stop_step RadixWorkspace.machine phase (fun _ => 0)
    (next.phaseTapes phase) width (driver width) (read_driver_end width)
  have hspace : (finished next phase width).tapeCells ≤ 8 * capacity + width + 2 :=
    boundary_space next phase width width
  have tail := Prefix.step (boundary_space next phase width width)
    (UnaryController.test_halted RadixWorkspace.machine phase) hs
    (Prefix.refl (finished next phase width) hspace)
  obtain ⟨r, hr, hf, hsteps, hpeak⟩ := (hp.trans tail).run
    (UnaryController.stop_halted RadixWorkspace.machine phase) hspace
  have hi : initialConfiguration machine (boundary w false 0 width).tapes =
      boundary w false 0 width := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 4) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp [initialConfiguration, boundary, UnaryController.boundary]
      · simp [initialConfiguration, boundary, UnaryController.boundary]
    · rfl
  refine ⟨next, r, ?_, hf, by omega, hpeak⟩
  change runFrom machine _ _ = _
  rw [hi]
  have hg := runFrom_moreFuel machine (steps + 1)
    (width * (10 * (stream rs).length + 12) - steps) _ r hr
  have he : steps + 1 + (width * (10 * (stream rs).length + 12) - steps) =
      width * (10 * (stream rs).length + 12) + 1 := by omega
  rw [he] at hg
  exact hg

end NearCubicWires.RepairOrdinary.RadixIteration
