import Proof.MachineModel.BlockPlatform
import Proof.CaseAnalysis.RowsDegreeLoop

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t s e : ℕ}

/-- Rewrite the exit bank along proved equalities, without restating the rest. -/
def congrExit (b : Block t) {H : Fin t → ℕ} {A : Fin t → List Bool}
    (hH : b.exitH = H) (hA : b.exitA = A) : Block t :=
  { b with exitH := H, exitA := A, run := b.run.congr hH hA }

@[simp] theorem congrExit_cost (b : Block t) {H : Fin t → ℕ} {A : Fin t → List Bool}
    (hH : b.exitH = H) (hA : b.exitA = A) : (congrExit b hH hA).cost = b.cost := rfl

/-- Extension by `e` fresh tapes carrying `eh`/`et` throughout. -/
def embedded (b : Block t) (eh : Fin e → ℕ) (et : Fin e → List Bool) : Block (t+e) where
  states := b.states
  machine := TapeEmbedding.machine e b.machine
  cost := b.cost
  entryH := Fin.addCases b.entryH eh
  entryA := Fin.addCases b.entryA et
  exitH := Fin.addCases b.exitH eh
  exitA := Fin.addCases b.exitA et
  run := b.run.embed eh et

@[simp] theorem embedded_cost (b : Block t) (eh : Fin e → ℕ) (et : Fin e → List Bool) :
    (embedded b eh et).cost = b.cost := rfl

/-- The paid clear-and-restore. Selected ports return to head zero; the added
tape is the reset workspace. Cost is `2*cost+2`, as `MaskedReset` charges. -/
def masked (b : Block t) (selected : Fin t → Bool) (cap : ℕ)
    (hstart : ∀ i, selected i = true → b.entryH i = 0) (hcap : b.cost ≤ cap) : Block (t+1) where
  states := b.states + 2
  machine := MaskedReset.machine b.machine selected
  cost := 2*b.cost+2
  entryH := Fin.addCases b.entryH (fun _ : Fin 1 => 0)
  entryA := Fin.addCases b.entryA (fun _ : Fin 1 => List.replicate cap false)
  exitH := Fin.addCases (fun i => if selected i then 0 else b.exitH i) (fun _ : Fin 1 => 0)
  exitA := Fin.addCases b.exitA (fun _ : Fin 1 => List.replicate cap false)
  run := b.run.mask selected hstart hcap

@[simp] theorem masked_cost (b : Block t) (selected : Fin t → Bool) (cap : ℕ)
    (hstart : ∀ i, selected i = true → b.entryH i = 0) (hcap : b.cost ≤ cap) :
    (masked b selected cap hstart hcap).cost = 2*b.cost+2 := rfl

/-! ## Bounded iteration -/

/-- A uniform cell body: one machine, one cost, and a `Step` from the `j`-th
cell configuration to the `(j+1)`-st with `emit j` appended to the output.

This is the shape a loop body actually has to satisfy, stated in the same
vocabulary as every other Block, so it can be built with `seq`, `focusedInto`,
`padded` and `masked` rather than by unfolding receipts. -/
structure Cells (t s : ℕ) where
  body : Machine t s
  cost : ℕ
  bound : ℕ
  source : ℕ → List Bool → Configuration t s
  emit : ℕ → List Bool
  entry : ∀ j, j < bound → ∀ out, (source j out).control = body.start
  step : ∀ j, j < bound → ∀ out,
    Step body cost (source j out).heads (source j out).tapes
      (source (j+1) (out ++ emit j)).heads (source (j+1) (out ++ emit j)).tapes

/-- The `Step` body, re-presented in the raw receipt form `loop_run` expects. -/
theorem Cells.supplier (c : Cells t s) (j : ℕ) (hj : j < c.bound) (out : List Bool) :
    ∃ r, runFrom c.body c.cost (c.source j out) = some r ∧
      r.final.heads = (c.source (j+1) (out ++ c.emit j)).heads ∧
      r.final.tapes = (c.source (j+1) (out ++ c.emit j)).tapes ∧ r.steps ≤ c.cost := by
  obtain ⟨r, hr, hh, ht, hs⟩ := c.step j hj out
  have hc : (⟨c.body.start, (c.source j out).heads, (c.source j out).tapes⟩ :
      Configuration t s) = c.source j out :=
    configuration_ext (c.entry j hj out).symm rfl rfl
  rw [hc] at hr
  exact ⟨r, hr, hh, ht, hs⟩

/-- The whole bounded loop, at `bound*(cost+3)+3`. One application of the
existing `CloseoutRowsDegreeLoop.loop_run`; no new machine and no new induction. -/
theorem Cells.run (c : Cells t s) (out : List Bool) :
    ∃ r, runFrom (CloseoutRowsDegreeLoop.machine c.body) (c.bound*(c.cost+3)+3)
        (RepeatMachine.cfg 0 (c.source 0 out) c.bound 1) = some r ∧
      r.final = RepeatMachine.cfg 3
        (c.source c.bound (out ++ (List.range c.bound).flatMap c.emit)) c.bound 1 ∧
      r.steps ≤ c.bound*(c.cost+3)+3 :=
  CloseoutRowsDegreeLoop.loop_run c.body c.source c.emit c.cost c.bound
    (fun j hj out => c.entry j hj out) (fun j hj out => c.supplier j hj out) out

/-- Cost of the loop, named once so a caller's budget comparison is one step. -/
def Cells.budget (c : Cells t s) : ℕ := c.bound*(c.cost+3)+3

@[simp] theorem Cells.budget_eq (c : Cells t s) :
    c.budget = c.bound*(c.cost+3)+3 := rfl

theorem Cells.budget_le (c : Cells t s) {n : ℕ} (h : c.bound*(c.cost+3)+3 ≤ n) :
    c.budget ≤ n := h

end
end NearCubicWires.BlockPlatform
