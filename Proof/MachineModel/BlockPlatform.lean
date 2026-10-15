import Proof.MachineModel.Runs
import Proof.MachineModel.Layout

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t u : ℕ}

/-- A machine together with the entry bank it starts from, the exit bank it
reaches, and the fuel that suffices. The state count is packed so that
`Composition.machine`, which adds state counts, still yields a `Block`. -/
structure Block (t : ℕ) where
  states : ℕ
  machine : Machine t states
  cost : ℕ
  entryH : Fin t → ℕ
  entryA : Fin t → List Bool
  exitH : Fin t → ℕ
  exitA : Fin t → List Bool
  run : Step machine cost entryH entryA exitH exitA

def ofStep {s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ} {a0 a1 : Fin t → List Bool}
    (h : Step p n h0 a0 h1 a1) : Block t :=
  ⟨s, p, n, h0, a0, h1, a1, h⟩

@[simp] theorem ofStep_cost {s n : ℕ} {p : Machine t s} {h0 h1 : Fin t → ℕ}
    {a0 a1 : Fin t → List Bool} (h : Step p n h0 a0 h1 a1) : (ofStep h).cost = n := rfl

/-- Sequential composition. The seam is stated once, as the two hypotheses;
the cost is `b.cost + 1 + c.cost`, the extra step being the paid bridge. -/
def seq (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) : Block t where
  states := b.states + c.states
  machine := Composition.machine b.machine c.machine
  cost := b.cost + 1 + c.cost
  entryH := b.entryH
  entryA := b.entryA
  exitH := c.exitH
  exitA := c.exitA
  run := by
    refine Step.seq b.run ?_
    rw [hH, hA]
    exact c.run

@[simp] theorem seq_cost (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) :
    (seq b c hH hA).cost = b.cost + 1 + c.cost := rfl

@[simp] theorem seq_entryH (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) :
    (seq b c hH hA).entryH = b.entryH := rfl

@[simp] theorem seq_exitA (b c : Block t) (hH : b.exitH = c.entryH) (hA : b.exitA = c.entryA) :
    (seq b c hH hA).exitA = c.exitA := rfl

/-- Weaken the cost to whatever the consumer's budget actually is. Stating the
final budget once here is what removes the per-junction `omega` reassociation. -/
def upto (b : Block t) (n : ℕ) (h : b.cost ≤ n) : Block t :=
  { b with cost := n, run := b.run.enlarge h }

@[simp] theorem upto_cost (b : Block t) (n : ℕ) (h : b.cost ≤ n) : (upto b n h).cost = n := rfl

/-- Retained false backing on every tape, at once. -/
def padded (b : Block t) (cap : Fin t → ℕ) : Block t :=
  { b with entryA := fun i => ZeroPadding.pad (cap i) (b.entryA i),
           exitA := fun i => ZeroPadding.pad (cap i) (b.exitA i),
           run := b.run.pad cap }

@[simp] theorem padded_cost (b : Block t) (cap : Fin t → ℕ) : (padded b cap).cost = b.cost := rfl

/-- Dock a worker into an ambient layout along an injective slot map. The
ambient entry bank must already carry the worker's inputs at its slots. -/
def focusedInto (b : Block t) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = b.entryH j) (hA : ∀ j, A (slots j) = b.entryA j) : Block u where
  states := b.states
  machine := RecoveryFocus.machine slots b.machine
  cost := b.cost
  entryH := H
  entryA := A
  exitH := dockH slots H b.exitH
  exitA := install slots A b.exitA
  run := b.run.dock slots hi H A hH hA

/-! ### Only the focused ports moved

Proved once, generically. This is the property that otherwise gets re-proved
per machine by `fin_cases i <;> simp` over the whole port range, and it is
exactly what a caller's loop hypothesis needs in order to reuse a body. -/

theorem focusedInto_outside_heads (b : Block t) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = b.entryH j) (hA : ∀ j, A (slots j) = b.entryA j)
    (i : Fin u) (hne : ∀ j, slots j ≠ i) :
    (focusedInto b slots hi H A hH hA).exitH i = H i :=
  dockH_other slots H b.exitH i hne

theorem focusedInto_outside_tapes (b : Block t) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = b.entryH j) (hA : ∀ j, A (slots j) = b.entryA j)
    (i : Fin u) (hne : ∀ j, slots j ≠ i) :
    (focusedInto b slots hi H A hH hA).exitA i = A i :=
  install_other slots A b.exitA i hne

@[simp] theorem focusedInto_cost (b : Block t) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = b.entryH j) (hA : ∀ j, A (slots j) = b.entryA j) :
    (focusedInto b slots hi H A hH hA).cost = b.cost := rfl

/-- A three-stage chain, to show the seams and the cost compose without any
per-junction arithmetic beyond one final `upto`. -/
def seq₃ (a b c : Block t)
    (h₁H : a.exitH = b.entryH) (h₁A : a.exitA = b.entryA)
    (h₂H : b.exitH = c.entryH) (h₂A : b.exitA = c.entryA) : Block t :=
  seq (seq a b h₁H h₁A) c h₂H h₂A

@[simp] theorem seq₃_cost (a b c : Block t)
    (h₁H : a.exitH = b.entryH) (h₁A : a.exitA = b.entryA)
    (h₂H : b.exitH = c.entryH) (h₂A : b.exitA = c.entryA) :
    (seq₃ a b c h₁H h₁A h₂H h₂A).cost = a.cost + 1 + b.cost + 1 + c.cost := rfl

end
end NearCubicWires.BlockPlatform
