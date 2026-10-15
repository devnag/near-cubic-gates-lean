import Proof.MachineModel.OrdinaryControlPrefix
import Proof.Foundations.OrdinaryTapeEmbedding

/-! A fixed two-phase loop. The loop count is read from an actual unary tape;
neither the finite transition table nor its tape count depends on that count.
Each test, body transition, return and final stop is an ordinary local step. -/
namespace NearCubicWires.RepairOrdinary.UnaryController
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def embed {s : ℕ} (phase : Bool) (i : Fin (s + 2)) : Fin ((s + 2) + (s + 2)) :=
  if phase then i.natAdd (s + 2) else i.castAdd (s + 2)

def code {s : ℕ} (phase : Bool) (i : Fin s) : Fin ((s + 2) + (s + 2)) :=
  embed phase (i.castAdd 2)

def test {s : ℕ} (phase : Bool) : Fin ((s + 2) + (s + 2)) :=
  embed phase ((0 : Fin 2).natAdd s)

def stop {s : ℕ} (phase : Bool) : Fin ((s + 2) + (s + 2)) :=
  embed phase ((1 : Fin 2).natAdd s)

def mappedAction {t s : ℕ} (phase : Bool) (a : Action t s) :
    Action t ((s + 2) + (s + 2)) := ⟨code phase a.nextControl, a.write, a.move⟩

def jump {t s : ℕ} (state : Fin s) : Action t s :=
  ⟨state, fun _ => none, fun _ => .stay⟩

def enter {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) :
    Action (t + 1) ((s + 2) + (s + 2)) :=
  ⟨code phase (p phase).start, fun _ => none,
    Fin.addCases (fun _ : Fin t => .stay) (fun _ : Fin 1 => .right)⟩

def localRule {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) :
    Fin (s + 2) → (Fin (t + 1) → Bool) → Option (Action (t + 1) ((s + 2) + (s + 2))) :=
  Fin.addCases
    (fun state scanned => if (p phase).halted state then some (jump (test (!phase))) else
      ((TapeEmbedding.machine 1 (p phase)).rule state scanned).map (mappedAction phase))
    (fun state scanned => if state.val = 0 then
      some (if scanned ((0 : Fin 1).natAdd t) then enter p phase else jump (stop phase))
      else none)

def machine {t s : ℕ} (p : Bool → Machine t s) : Machine (t + 1) ((s + 2) + (s + 2)) where
  descriptionBits := 0
  start := test false
  halted := Fin.addCases
    (Fin.addCases (fun _ : Fin s => false) (fun i : Fin 2 => i.val == 1))
    (Fin.addCases (fun _ : Fin s => false) (fun i : Fin 2 => i.val == 1))
  rule := Fin.addCases (localRule p false) (localRule p true)

@[simp] theorem body_halted {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) (i : Fin s) :
    (machine p).halted (code phase i) = false := by
  cases phase <;> simp [machine, code, embed, -Fin.natAdd_eq_addNat]

@[simp] theorem test_halted {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) :
    (machine p).halted (test phase) = false := by
  cases phase <;> simp [machine, test, embed, -Fin.natAdd_eq_addNat]

@[simp] theorem stop_halted {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) :
    (machine p).halted (stop phase) = true := by
  cases phase <;> simp [machine, stop, embed, -Fin.natAdd_eq_addNat]

theorem body_rule {t s : ℕ} (p : Bool → Machine t s) (phase : Bool) (i : Fin s)
    (bits : Fin (t + 1) → Bool) :
    (machine p).rule (code phase i) bits =
      if (p phase).halted i then some (jump (test (!phase))) else
        ((TapeEmbedding.machine 1 (p phase)).rule i bits).map (mappedAction phase) := by
  cases phase <;> simp [machine, code, embed, localRule, -Fin.natAdd_eq_addNat]

theorem test_rule {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (bits : Fin (t + 1) → Bool) :
    (machine p).rule (test phase) bits =
      some (if bits ((0 : Fin 1).natAdd t) then enter p phase else jump (stop phase)) := by
  cases phase <;> simp [machine, test, embed, localRule, -Fin.natAdd_eq_addNat]

theorem body_step {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (c : Configuration (t + 1) s) (hn : (p phase).halted c.control = false) :
    step (machine p) (controlConfig (code phase) c) =
      (step (TapeEmbedding.machine 1 (p phase)) c).map (controlConfig (code phase)) := by
  change ((machine p).rule (code phase c.control) c.scanned).map _ = _
  rw [body_rule, hn]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map, step]
  rfl

def boundary {t s : ℕ} (phase : Bool) (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (position : ℕ) (driver : List Bool) : Configuration (t + 1) ((s + 2) + (s + 2)) :=
  ⟨test phase, Fin.addCases heads (fun _ : Fin 1 => position),
    Fin.addCases tapes (fun _ : Fin 1 => driver)⟩

@[simp] theorem boundary_cells {t s : ℕ} (phase : Bool) (heads : Fin t → ℕ)
    (tapes : Fin t → List Bool) (position : ℕ) (driver : List Bool) :
    (boundary (s := s) phase heads tapes position driver).tapeCells =
      (∑ i, (tapes i).length) + driver.length := by
  unfold boundary Configuration.tapeCells
  rw [Fin.sum_univ_add]
  simp

theorem enter_step {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (position : ℕ) (driver : List Bool)
    (hb : readTapeBit driver position = true) :
    step (machine p) (boundary phase heads tapes position driver) =
      some (controlConfig (code phase) (TapeEmbedding.config
        (fun _ : Fin 1 => position + 1) (fun _ : Fin 1 => driver)
        ⟨(p phase).start, heads, tapes⟩)) := by
  change ((machine p).rule (test phase) _).map _ = _
  rw [test_rule]
  simp only [Configuration.scanned, boundary, Fin.addCases_right, hb, ↓reduceIte, Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [applyAction, enter, controlConfig, TapeEmbedding.config, HeadMove.apply]
    · simp [applyAction, enter, controlConfig, TapeEmbedding.config, HeadMove.apply]
  · rfl

theorem return_step {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (c : Configuration t s) (position : ℕ) (driver : List Bool)
    (hh : (p phase).halted c.control = true) :
    step (machine p) (controlConfig (code phase) (TapeEmbedding.config
      (fun _ : Fin 1 => position) (fun _ : Fin 1 => driver) c)) =
      some (boundary (!phase) c.heads c.tapes position driver) := by
  change ((machine p).rule (code phase c.control) _).map _ = _
  rw [body_rule, hh]
  simp only [↓reduceIte, Option.map_some]
  rfl

theorem stop_step {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (position : ℕ) (driver : List Bool)
    (hb : readTapeBit driver position = false) :
    step (machine p) (boundary phase heads tapes position driver) =
      some { boundary (s := s) phase heads tapes position driver with control := stop phase } := by
  change ((machine p).rule (test phase) _).map _ = _
  rw [test_rule]
  simp only [Configuration.scanned, boundary, Fin.addCases_right, hb, Bool.false_eq_true,
    ↓reduceIte, Option.map_some]
  rfl

theorem body_prefix {t s : ℕ} (p : Bool → Machine t s) (phase : Bool)
    (c : Configuration t s) (fuel : ℕ) (r : ExecutionReceipt t s)
    (hr : runFrom (p phase) fuel c = some r) (position : ℕ) (driver : List Bool) :
    Prefix (machine p) (r.peakTapeCells + driver.length) r.steps
      (controlConfig (code phase) (TapeEmbedding.config
        (fun _ : Fin 1 => position) (fun _ : Fin 1 => driver) c))
      (controlConfig (code phase) (TapeEmbedding.config
        (fun _ : Fin 1 => position) (fun _ : Fin 1 => driver) r.final)) ∧
      (p phase).halted r.final.control = true := by
  have he := TapeEmbedding.run_embed (p phase) (fun _ : Fin 1 => position)
    (fun _ : Fin 1 => driver) fuel c r hr
  obtain ⟨hp, hh⟩ := prefix_of_run _ _ _ _ he
  have hm := hp.mapControl (code phase) (fun c _ => body_halted p phase c.control)
    (fun c d hn hs => by rw [body_step p phase c hn, hs]; rfl)
  refine ⟨?_, hh⟩
  simpa only [TapeEmbedding.receipt, TapeEmbedding.extraCells, Fin.sum_univ_one] using hm

end NearCubicWires.RepairOrdinary.UnaryController
