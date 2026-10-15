import Proof.MachineModel.OrdinaryRadixRound
import Proof.Foundations.OrdinaryTapeRenaming

/-! The complete framed workspace carried by the radix-loop consumer. A round
changes its physical input role; both roles are fixed controller instances,
not a width-indexed family of programs. -/
namespace NearCubicWires.RepairOrdinary.RadixWorkspace
open LocalBitMultitape StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State (capacity : ℕ) (rs : List Record) where
  junk : List Bool
  old : Bool → List Bool
  inputFit : (stream rs).length + junk.length ≤ capacity
  oldFit : ∀ tag, (old tag).length ≤ capacity

def State.tapes {capacity : ℕ} {rs : List Record} (w : State capacity rs) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
    (fun i : Fin 3 => if i.val = 0 then stream rs ++ w.junk else w.old (i.val == 2))
    (fun _ : Fin 1 => List.replicate (2 * capacity) false)

def layout (phase : Bool) : Fin 4 ≃ Fin 4 := if phase then Equiv.swap 0 1 else Equiv.refl _

@[simp] theorem swap_two : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
@[simp] theorem swap_three : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide

def State.phaseTapes {capacity : ℕ} {rs : List Record} (w : State capacity rs) (phase : Bool) :
    Fin 4 → List Bool := w.tapes ∘ (layout phase).symm

def machine (phase : Bool) : Machine 4 38 := TapeRenaming.machine (layout phase) RadixRound.machine

theorem state_cells {capacity : ℕ} {rs : List Record} (w : State capacity rs) (phase : Bool) :
    (∑ i, (w.phaseTapes phase i).length) ≤ 5 * capacity := by
  have hi := w.inputFit
  have h0 := w.oldFit false
  have h1 := w.oldFit true
  cases phase <;> simp [State.phaseTapes, State.tapes, layout, Fin.sum_univ_succ, Fin.addCases] <;> omega

theorem workspace_round {capacity : ℕ} {rs : List Record} (w : State capacity rs) (phase : Bool) :
    ∃ next : State capacity (RadixRound.records rs), ∃ r : ExecutionReceipt 4 38,
      run (machine phase) (10 * (stream rs).length + 10) (w.phaseTapes phase) = some r ∧
      r.final.tapes = next.phaseTapes (!phase) ∧ (∀ i, r.final.heads i = 0) ∧
      r.steps ≤ 10 * (stream rs).length + 10 ∧ r.peakTapeCells ≤ 8 * capacity + 1 := by
  obtain ⟨base, nextJunk, hb, hout, hcells, hcounter, hheads, hsteps, hpeak⟩ :=
    RadixRound.radix_round rs w.junk w.old capacity w.inputFit w.oldFit
  let next : State capacity (RadixRound.records rs) := {
    junk := nextJunk
    old := fun tag => if tag then base.final.tapes 2 else base.final.tapes 0
    inputFit := by
      have hc := hcells (1 : Fin 3)
      change (base.final.tapes 1).length ≤ capacity at hc
      rw [hout] at hc
      simpa using hc
    oldFit := by
      intro tag
      cases tag
      · simpa using hcells (0 : Fin 3)
      · simpa using hcells (2 : Fin 3) }
  have hb' : run RadixRound.machine (10 * (stream rs).length + 10) w.tapes = some base := hb
  have hn := TapeRenaming.run_rename (layout phase) RadixRound.machine
    (10 * (stream rs).length + 10) _ base hb'
  have hinit : initialConfiguration (machine phase) (w.phaseTapes phase) =
      TapeRenaming.config (layout phase) (initialConfiguration RadixRound.machine w.tapes) := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  refine ⟨next, TapeRenaming.receipt (layout phase) base, ?_, ?_, ?_, hsteps, hpeak⟩
  · change runFrom (machine phase) _ _ = _
    rw [hinit]
    exact hn
  · funext i
    cases phase <;> fin_cases i <;>
      simp [TapeRenaming.receipt, TapeRenaming.config, State.phaseTapes, State.tapes,
        layout, Fin.addCases, next, hout, hcounter]
  · intro i
    exact hheads ((layout phase).symm i)

end NearCubicWires.RepairOrdinary.RadixWorkspace
