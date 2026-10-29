import Proof.Foundations.OrdinaryMachine
import SourceAdapters.Refuter.FaithfulPrefix

/-!
proof of `lem:multitape-refuter`; proof of `thm:short-pcp-ours`: a finite window for the bounded computation.
The finite state below retains every visited tape cell, actual one-sided
heads, and the machine's finite control. No transition or initial-memory
condition is replaced by a hypothesis about the desired compilation.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.LocalBitMultitape

set_option autoImplicit false

/-- A fixed finite array of observed tape cells and heads inside that array. -/
structure MachineWindow (t s width : ℕ) where
  control : Fin s
  heads : Fin t → Fin width
  cells : Fin t → Fin width → Bool

/-- Exact agreement on the finite window; cells outside it are unrestricted. -/
structure MachineWindow.Represents {t s width : ℕ}
    (a : MachineWindow t s width) (c : Configuration t s) : Prop where
  control : a.control = c.control
  heads : ∀ tape, (a.heads tape).val = c.heads tape
  cells : ∀ tape position, a.cells tape position = readTapeBit (c.tapes tape) position.val

/-- The actual initial tapes are observed cell by cell, without unframing. -/
def MachineWindow.ofConfiguration {t s width : ℕ} (c : Configuration t s)
    (h : ∀ tape, c.heads tape < width) : MachineWindow t s width where
  control := c.control
  heads := fun tape => ⟨c.heads tape, h tape⟩
  cells := fun tape position => readTapeBit (c.tapes tape) position.val

theorem MachineWindow.ofConfiguration_represents {t s width : ℕ}
    (c : Configuration t s) (h : ∀ tape, c.heads tape < width) :
    (MachineWindow.ofConfiguration c h).Represents c := ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩

def MachineWindow.scanned {t s width : ℕ} (a : MachineWindow t s width) : Fin t → Bool :=
  fun tape => a.cells tape (a.heads tape)

theorem MachineWindow.Represents.scanned {t s width : ℕ}
    {a : MachineWindow t s width} {c : Configuration t s} (h : a.Represents c) :
    a.scanned = c.scanned := by
  funext tape
  rw [MachineWindow.scanned, h.cells, h.heads]
  rfl

/-- The finite local tape update: one possible write at the old head position. -/
def MachineWindow.apply {t s width : ℕ} (a : MachineWindow t s width) (action : Action t s)
    (h : ∀ tape, (action.move tape).apply (a.heads tape).val < width) :
    MachineWindow t s width where
  control := action.nextControl
  heads := fun tape => ⟨(action.move tape).apply (a.heads tape).val, h tape⟩
  cells := fun tape position =>
    match action.write tape with
    | none => a.cells tape position
    | some value => if position = a.heads tape then value else a.cells tape position

theorem MachineWindow.Represents.apply {t s width : ℕ}
    {a : MachineWindow t s width} {c : Configuration t s} (h : a.Represents c)
    (action : Action t s)
    (hroom : ∀ tape, (action.move tape).apply (a.heads tape).val < width) :
    (a.apply action hroom).Represents (applyAction c action) := by
  constructor
  · rfl
  · intro tape
    simp only [MachineWindow.apply, applyAction, h.heads]
  · intro tape position
    simp only [MachineWindow.apply, applyAction]
    cases hw : action.write tape with
    | none => exact h.cells tape position
    | some value =>
        rw [Refuter.readTapeBit_writeTapeBit]
        have he : position = a.heads tape ↔ position.val = c.heads tape := by
          rw [← h.heads tape]
          exact Fin.ext_iff
        simp only [he, h.cells]

/-- One source transition, with genuine halts retained as an absorbing state. -/
def machineAdvance {t s : ℕ} (machine : Machine t s) (c : Configuration t s) :
    Option (Configuration t s) :=
  if machine.halted c.control then some c else step machine c

/-- One finite transition. Leaving the window is explicitly rejected. -/
def MachineWindow.advance {t s width : ℕ} (machine : Machine t s)
    (a : MachineWindow t s width) : Option (MachineWindow t s width) :=
  if machine.halted a.control then some a
  else
    match machine.rule a.control a.scanned with
    | none => none
    | some action =>
        if h : ∀ tape, (action.move tape).apply (a.heads tape).val < width then
          some (a.apply action h)
        else none

/-- proof of `lem:multitape-refuter`; proof of `thm:short-pcp-ours`: finite one-step equivalence whenever one more step fits.
Missing transition rules are preserved rather than converted to accepting halts. -/
theorem MachineWindow.advance_correct {t s width : ℕ} (machine : Machine t s)
    {a : MachineWindow t s width} {c : Configuration t s} (h : a.Represents c)
    (hroom : ∀ tape, c.heads tape + 1 < width) :
    (a.advance machine = none ∧ machineAdvance machine c = none) ∨
      ∃ b d, a.advance machine = some b ∧ machineAdvance machine c = some d ∧ b.Represents d := by
  by_cases hhalt : machine.halted c.control = true
  · right
    exact ⟨a, c, by simp [MachineWindow.advance, h.control, hhalt],
      by simp [machineAdvance, hhalt], h⟩
  · cases hrule : machine.rule c.control c.scanned with
    | none =>
        left
        constructor
        · simp [MachineWindow.advance, h.control, h.scanned, hhalt, hrule]
        · simp [machineAdvance, step, hhalt, hrule]
    | some action =>
        have hfit : ∀ tape, (action.move tape).apply (a.heads tape).val < width := by
          intro tape
          rw [h.heads]
          exact (Refuter.HeadMove.apply_le _ _).trans_lt (hroom tape)
        right
        refine ⟨a.apply action hfit, applyAction c action, ?_, ?_, h.apply action hfit⟩
        · simp only [MachineWindow.advance, h.control, h.scanned, if_neg hhalt, hrule]
          rw [dif_pos hfit]
        · simp [machineAdvance, step, hhalt, hrule]

/-- The unrolled source semantics performs exactly the supplied number of
rounds, retaining early halts and propagating a stuck computation as none. -/
def machineRounds {t s : ℕ} (machine : Machine t s) :
    ℕ → Configuration t s → Option (Configuration t s)
  | 0, c => some c
  | fuel + 1, c => (machineAdvance machine c).bind (machineRounds machine fuel)

theorem machineRounds_of_halted {t s : ℕ} (machine : Machine t s)
    (c : Configuration t s) (h : machine.halted c.control = true) (fuel : ℕ) :
    machineRounds machine fuel c = some c := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [machineRounds, machineAdvance, h] using ih

/-- The absorbing-round semantics returns a halted verdict exactly when the
original bounded interpreter returns its actual execution result. -/
theorem machineRounds_halted_eq_run {t s : ℕ} (machine : Machine t s)
    (fuel : ℕ) (c : Configuration t s) :
    (machineRounds machine fuel c).bind (fun d => if machine.halted d.control then some d else none) =
      (runFrom machine fuel c).map ExecutionReceipt.final := by
  induction fuel generalizing c with
  | zero => simp [machineRounds, runFrom]
  | succ fuel ih =>
      by_cases hh : machine.halted c.control = true
      · rw [machineRounds_of_halted machine c hh]
        simp [runFrom, hh]
      · simp only [machineRounds, machineAdvance, if_neg hh, runFrom]
        cases hs : step machine c with
        | none => simp
        | some d =>
            simp only [Option.bind_some]
            rw [ih]
            cases hr : runFrom machine fuel d <;> rfl

end NearCubicGates.Adapters.Compile
