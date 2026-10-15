import Proof.Foundations.OrdinaryMachine

/-!
Sequential composition of actual local machines on the same tapes. The
handoff is one executed transition: only finite control changes, and all
tapes and heads are preserved. Each caller must supply its actual intermediate
configuration, including any needed paid rewind or framing conversion.
-/
namespace NearCubicWires.RepairOrdinary.Composition
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftConfig {t a : ℕ} (b : ℕ) (c : Configuration t a) : Configuration t (a + b) :=
  ⟨c.control.castAdd b, c.heads, c.tapes⟩

def rightConfig {t b : ℕ} (a : ℕ) (c : Configuration t b) : Configuration t (a + b) :=
  ⟨c.control.natAdd a, c.heads, c.tapes⟩

def restart {t a b : ℕ} (c : Configuration t a) (state : Fin b) : Configuration t b :=
  ⟨state, c.heads, c.tapes⟩

def leftAction {t a : ℕ} (b : ℕ) (x : Action t a) : Action t (a + b) :=
  ⟨x.nextControl.castAdd b, x.write, x.move⟩

def rightAction {t b : ℕ} (a : ℕ) (x : Action t b) : Action t (a + b) :=
  ⟨x.nextControl.natAdd a, x.write, x.move⟩

def bridge {t a b : ℕ} (state : Fin b) : Action t (a + b) :=
  ⟨state.natAdd a, fun _ => none, fun _ => .stay⟩

def machine {t a b : ℕ} (p : Machine t a) (q : Machine t b) : Machine t (a + b) where
  descriptionBits := 0
  start := p.start.castAdd b
  halted := Fin.addCases (fun _ => false) q.halted
  rule := Fin.addCases
    (fun state scanned => if p.halted state then some (bridge q.start)
      else (p.rule state scanned).map (leftAction b))
    (fun state scanned => (q.rule state scanned).map (rightAction a))

@[simp] theorem left_cells {t a : ℕ} (b : ℕ) (c : Configuration t a) :
    (leftConfig b c).tapeCells = c.tapeCells := rfl

@[simp] theorem right_cells {t b : ℕ} (a : ℕ) (c : Configuration t b) :
    (rightConfig a c).tapeCells = c.tapeCells := rfl

@[simp] theorem left_halted {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (c : Configuration t a) : (machine p q).halted (leftConfig b c).control = false := by
  simp [machine, leftConfig]

@[simp] theorem right_halted {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (c : Configuration t b) :
    (machine p q).halted (rightConfig a c).control = q.halted c.control := by
  simp [machine, rightConfig]

theorem left_apply {t a : ℕ} (b : ℕ) (c : Configuration t a) (x : Action t a) :
    applyAction (leftConfig b c) (leftAction b x) = leftConfig b (applyAction c x) := rfl

theorem right_apply {t b : ℕ} (a : ℕ) (c : Configuration t b) (x : Action t b) :
    applyAction (rightConfig a c) (rightAction a x) = rightConfig a (applyAction c x) := rfl

theorem left_step {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (c : Configuration t a) (h : p.halted c.control = false) :
    step (machine p q) (leftConfig b c) = (step p c).map (leftConfig b) := by
  simp [step, machine, leftConfig, h, Option.map_map,
    Function.comp_def, leftAction, applyAction]
  rfl

theorem right_step {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (c : Configuration t b) :
    step (machine p q) (rightConfig a c) = (step q c).map (rightConfig a) := by
  simp [step, machine, rightConfig, Option.map_map,
    Function.comp_def, rightAction, applyAction]
  rfl

theorem bridge_step {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (c : Configuration t a) (h : p.halted c.control = true) :
    step (machine p q) (leftConfig b c) = some (rightConfig a (restart c q.start)) := by
  simp [step, machine, leftConfig, h]
  rfl

def rightReceipt {t b : ℕ} (a : ℕ) (r : ExecutionReceipt t b) : ExecutionReceipt t (a + b) :=
  ⟨rightConfig a r.final, r.steps, r.peakTapeCells⟩

theorem right_run {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (fuel : ℕ) (c : Configuration t b) (r : ExecutionReceipt t b)
    (hrun : runFrom q fuel c = some r) :
    runFrom (machine p q) fuel (rightConfig a c) = some (rightReceipt a r) := by
  induction fuel generalizing c r with
  | zero =>
    simp only [runFrom] at hrun
    split at hrun
    · next h => cases hrun; simp [runFrom, right_halted, h, rightReceipt]
    · contradiction
  | succ fuel ih =>
    simp only [runFrom] at hrun
    split at hrun
    · next h => cases hrun; simp [runFrom, right_halted, h, rightReceipt]
    · next h =>
        split at hrun
        · contradiction
        · next next hs =>
            split at hrun
            · contradiction
            · next suffix htail =>
                cases hrun
                have hm := ih next suffix htail
                have hstep : step (machine p q) (rightConfig a c) = some (rightConfig a next) := by
                  rw [right_step, hs]
                  rfl
                simpa [rightReceipt] using runFrom_step (machine p q)
                  (rightConfig a c) (rightConfig a next) (rightReceipt a suffix)
                  (by simpa using h) hstep hm

def joinedReceipt {t a b : ℕ} (r : ExecutionReceipt t a)
    (s : ExecutionReceipt t b) : ExecutionReceipt t (a + b) :=
  ⟨rightConfig a s.final, r.steps + 1 + s.steps, max r.peakTapeCells s.peakTapeCells⟩

/-- The costs compose additively, with one real transition at the handoff. -/
theorem run_join {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (fp fq : ℕ) (c : Configuration t a)
    (r : ExecutionReceipt t a) (s : ExecutionReceipt t b)
    (hp : runFrom p fp c = some r)
    (hq : runFrom q fq (restart r.final q.start) = some s) :
    runFrom (machine p q) (fp + 1 + fq) (leftConfig b c) = some (joinedReceipt r s) := by
  induction fp generalizing c r with
  | zero =>
    simp only [runFrom] at hp
    split at hp
    · next h =>
        cases hp
        have hright := right_run p q fq _ s hq
        have hfirst := runFrom_step (machine p q) (leftConfig b c)
          (rightConfig a (restart c q.start)) (rightReceipt a s)
          (left_halted p q c) (bridge_step p q c h) hright
        simpa [joinedReceipt, rightReceipt, Nat.add_comm] using hfirst
    · contradiction
  | succ fp ih =>
    simp only [runFrom] at hp
    split at hp
    · next h =>
        cases hp
        have hright := right_run p q fq _ s hq
        have hfirst := runFrom_step (machine p q) (leftConfig b c)
          (rightConfig a (restart c q.start)) (rightReceipt a s)
          (left_halted p q c) (bridge_step p q c h) hright
        have hmore := runFrom_moreFuel (machine p q) (fq + 1) (fp + 1) _ _ hfirst
        simpa [joinedReceipt, rightReceipt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hmore
    · next h =>
        split at hp
        · contradiction
        · next next hs =>
            split at hp
            · contradiction
            · next suffix htail =>
                cases hp
                have htailJoin := ih next suffix htail hq
                have hstep : step (machine p q) (leftConfig b c) = some (leftConfig b next) := by
                  rw [left_step p q c (by simpa using h), hs]
                  rfl
                have hfirst := runFrom_step (machine p q) (leftConfig b c)
                  (leftConfig b next) _ (left_halted p q c) hstep htailJoin
                simpa [joinedReceipt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                  max_assoc] using hfirst

end NearCubicWires.RepairOrdinary.Composition
