import Proof.Amplification.RecoveryCursorCalls

/-!
# Williams Corollary 4.4: a finite prefix-lookup gate in front of a fixed machine

Williams (JACM 2014) Corollary 4.4 / C.2 is stated "For all sufficiently large N". The imported
`RepairRepresentation.WilliamsSource` asks for one machine that is correct for EVERY request. This
module supplies the generic machinery that closes that finite prefix; it knows nothing about matrices.

`Gate.combined` runs a gate program `Gate.machine` and then, only if the gate says so, a given machine
`L` (on the same `t ≥ 2` tapes). The gate

1. reads the first `B` cells of tapes 0 and 1 in parallel into finite control (`B` steps);
2. consults a fixed finite table `answer : (Fin B → Bool) → (Fin B → Bool) → Option (List Bool)`
   (one step);
3. if the table has an entry `w`, writes `w` on the output tape `o` (`|w|` steps) and stops;
4. otherwise moves heads 0 and 1 back to cell 0 (`B` steps) and halts with every tape untouched and
   every head at 0. The call controller then starts `L` exactly in `L`'s initial configuration.

`combined_small_run` and `combined_large_run` are the two outcomes. The controller is the repo's
proved `RecoveryCalls.machine` (`Proof/Amplification/RecoveryCallController.lean`) with
`RecoveryRootRound.call_receipt` / `stop_receipt` (`Proof/Amplification/RecoveryCursorCalls.lean`),
used exactly as in `WilliamsCall.total_run` (`Proof/MachineModel/OrdinaryWilliamsTotal.lean`).

Machine model: `Proof/Foundations/LocalBitMultitapeCore.lean` (finite control, one scanned Boolean
per tape, local writes, unit head moves, one step per transition).
-/

namespace NearCubicWires.Bindings.Williams14

open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

namespace Gate

/-- The gate's finite control. `read i a b`: `i` cells of tapes 0/1 read, recorded in `a`/`b`.
`write j a b`: `j` cells of the table entry written. `back i`: heads 0/1 at cell `i`. -/
inductive State (B W : ℕ) where
  | read (i : Fin (B + 1)) (a b : Fin B → Bool)
  | write (j : Fin (W + 1)) (a b : Fin B → Bool)
  | back (i : Fin (B + 1))
  | go
  | done
  deriving Fintype

/-- The finite control as `Fin`, as in `RecoveryCalls.controlCode`. -/
noncomputable def enc (B W : ℕ) : State B W ≃ Fin (Fintype.card (State B W)) :=
  Fintype.equivFin _

section Machine

variable {t : ℕ} (ht : 2 ≤ t) (o : Fin t) {B W : ℕ}
  (answer : (Fin B → Bool) → (Fin B → Bool) → Option (List Bool))

/-- Input tape 0. -/
def tape0 : Fin t := ⟨0, by omega⟩

/-- Input tape 1. -/
def tape1 : Fin t := ⟨1, by omega⟩

/-- Move heads 0 and 1, keep the others. -/
def inputMove (m : HeadMove) : Fin t → HeadMove := fun i => if i.val < 2 then m else .stay

/-- Move the output head right, keep the others. -/
def outputMove : Fin t → HeadMove := fun i => if i = o then .right else .stay

/-- A transition that only changes the control. -/
noncomputable def idle (q : State B W) : Action t (Fintype.card (State B W)) :=
  ⟨enc B W q, fun _ => none, fun _ => .stay⟩

/-- The gate's rule table. -/
noncomputable def transition :
    State B W → (Fin t → Bool) → Option (Action t (Fintype.card (State B W)))
  | .read i a b, bits =>
      if h : i.val < B then
        some ⟨enc B W (.read ⟨i.val + 1, by omega⟩
            (Function.update a ⟨i.val, h⟩ (bits (tape0 ht)))
            (Function.update b ⟨i.val, h⟩ (bits (tape1 ht)))),
          fun _ => none, inputMove .right⟩
      else
        match answer a b with
        | some _ => some (idle (.write ⟨0, Nat.succ_pos W⟩ a b))
        | none => some (idle (.back (Fin.last B)))
  | .write j a b, _ =>
      if h : j.val < ((answer a b).getD []).length ∧ j.val < W then
        some ⟨enc B W (.write ⟨j.val + 1, by omega⟩ a b),
          fun i => if i = o then some (((answer a b).getD []).getD j.val false) else none,
          outputMove o⟩
      else some (idle .done)
  | .back i, _ =>
      if h : 0 < i.val then
        some ⟨enc B W (.back ⟨i.val - 1, by omega⟩), fun _ => none, inputMove .left⟩
      else some (idle .go)
  | .go, _ => none
  | .done, _ => none

/-- The two halting states. -/
def isHalt : State B W → Bool
  | .go => true
  | .done => true
  | _ => false

/-- The gate program. -/
noncomputable def machine : Machine t (Fintype.card (State B W)) where
  descriptionBits := 0
  start := enc B W (.read ⟨0, Nat.succ_pos B⟩ (fun _ => false) (fun _ => false))
  halted := fun q => isHalt ((enc B W).symm q)
  rule := fun q bits => transition ht o answer ((enc B W).symm q) bits

/-- A gate configuration. -/
noncomputable def cfg (q : State B W) (heads : Fin t → ℕ) (tapes : Fin t → List Bool) :
    Configuration t (Fintype.card (State B W)) :=
  ⟨enc B W q, heads, tapes⟩

theorem step_cfg (q : State B W) (heads : Fin t → ℕ) (tapes : Fin t → List Bool) :
    step (machine (W := W) ht o answer) (cfg q heads tapes) =
      (transition ht o answer q (fun i => readTapeBit (tapes i) (heads i))).map
        (applyAction (cfg q heads tapes)) := by
  unfold step
  simp only [machine, cfg, Equiv.symm_apply_apply]
  rfl

theorem halted_cfg (q : State B W) (heads : Fin t → ℕ) (tapes : Fin t → List Bool) :
    (machine (W := W) ht o answer).halted (cfg q heads tapes).control = isHalt q := by
  simp only [machine, cfg, Equiv.symm_apply_apply]

/-- Heads 0 and 1 at cell `i`, the others at 0. -/
def readHeads (i : ℕ) : Fin t → ℕ := fun x => if x.val < 2 then i else 0

theorem readHeads_zero : (readHeads 0 : Fin t → ℕ) = fun _ => 0 := by
  funext x
  simp [readHeads]

/-- The first `i` cells of a tape, as the gate records them in a `B`-cell register. -/
def pad (T : List Bool) (i : ℕ) : Fin B → Bool :=
  fun j => if j.val < i then readTapeBit T j.val else false

/-- The first `B` cells of a tape (blank cells read `false`). -/
def window (B : ℕ) (T : List Bool) : Fin B → Bool := fun j => readTapeBit T j.val

theorem pad_B (T : List Bool) : (pad T B : Fin B → Bool) = window B T := by
  funext j
  simp [pad, window, j.isLt]

theorem pad_succ (T : List Bool) (i : ℕ) (h : i < B) :
    Function.update (pad T i : Fin B → Bool) ⟨i, h⟩ (readTapeBit T i) = pad T (i + 1) := by
  funext j
  by_cases hj : j = ⟨i, h⟩
  · subst hj
    simp [pad]
  · rw [Function.update_of_ne hj]
    have hv : j.val ≠ i := fun e => hj (Fin.ext e)
    simp only [pad]
    by_cases hlt : j.val < i
    · simp [hlt, show j.val < i + 1 by omega]
    · simp [hlt, show ¬ j.val < i + 1 by omega]

/-- Reading phase: after `i ≤ B` steps the first `i` cells of tapes 0 and 1 are in control. -/
theorem read_timed (tapes : Fin t → List Bool) : ∀ (i : ℕ) (hi : i ≤ B),
    Timed (machine (W := W) ht o answer) i
      (cfg (.read ⟨0, Nat.succ_pos B⟩ (fun _ => false) (fun _ => false)) (readHeads 0) tapes)
      (cfg (.read ⟨i, by omega⟩ (pad (tapes (tape0 ht)) i) (pad (tapes (tape1 ht)) i))
        (readHeads i) tapes)
  | 0, _ => by
      have h0 : ∀ T : List Bool, (pad T 0 : Fin B → Bool) = fun _ => false := by
        intro T
        funext j
        simp [pad]
      rw [h0, h0]
      exact Timed.refl _ _
  | i + 1, hi => by
      have ih := read_timed tapes i (by omega)
      refine ih.trans (Timed.single ?_ ?_)
      · rw [halted_cfg]
        rfl
      · rw [step_cfg]
        have hB : i < B := by omega
        simp only [transition, hB, dite_true, Option.map_some]
        congr 1
        refine configuration_ext ?_ ?_ ?_
        · change enc B W _ = enc B W _
          congr 1
          have h0 : readTapeBit (tapes (tape0 ht)) (readHeads i (tape0 ht)) =
              readTapeBit (tapes (tape0 ht)) i := by simp [readHeads, tape0]
          have h1 : readTapeBit (tapes (tape1 ht)) (readHeads i (tape1 ht)) =
              readTapeBit (tapes (tape1 ht)) i := by simp [readHeads, tape1]
          rw [h0, h1, pad_succ _ _ hB, pad_succ _ _ hB]
        · funext x
          simp only [applyAction, cfg, inputMove, readHeads]
          by_cases hx : x.val < 2 <;> simp [hx, HeadMove.apply]
        · rfl

/-- The table lookup step. -/
theorem decide_step (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (a b : Fin B → Bool) :
    step (machine (W := W) ht o answer) (cfg (.read (Fin.last B) a b) heads tapes) =
      some (cfg (match answer a b with
        | some _ => .write ⟨0, Nat.succ_pos W⟩ a b
        | none => .back (Fin.last B)) heads tapes) := by
  rw [step_cfg]
  simp only [transition, Fin.val_last, lt_irrefl, dite_false]
  cases answer a b <;> rfl

/-- Writing one cell just past the end of a tape appends it. -/
theorem write_end (l : List Bool) (v : Bool) : writeTapeBit l l.length v = l ++ [v] := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [writeTapeBit, ih]

section Write

variable {a b : Fin B → Bool} {w : List Bool}

/-- Writing phase: after `j ≤ |w|` steps the output tape holds the first `j` cells of `w`. -/
theorem write_timed (hw : answer a b = some w) (hW : w.length ≤ W)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (hh : heads o = 0) (hT : tapes o = []) :
    ∀ (j : ℕ) (hj : j ≤ w.length),
      Timed (machine (W := W) ht o answer) j (cfg (.write ⟨0, Nat.succ_pos W⟩ a b) heads tapes)
        (cfg (.write ⟨j, by omega⟩ a b) (Function.update heads o j)
          (Function.update tapes o (w.take j)))
  | 0, _ => by
      have e1 : Function.update heads o 0 = heads := by rw [← hh]; exact Function.update_eq_self o heads
      have e2 : Function.update tapes o (w.take 0) = tapes := by
        rw [List.take_zero, ← hT]; exact Function.update_eq_self o tapes
      rw [e1, e2]
      exact Timed.refl _ _
  | j + 1, hj => by
      have ih := write_timed hw hW heads tapes hh hT j (by omega)
      refine ih.trans (Timed.single ?_ ?_)
      · rw [halted_cfg]
        rfl
      · rw [step_cfg]
        have hc : j < ((answer a b).getD []).length ∧ j < W := by
          rw [hw]; simp only [Option.getD_some]; omega
        simp only [transition, hc, and_self, dite_true, Option.map_some]
        congr 1
        refine configuration_ext rfl ?_ ?_
        · funext x
          simp only [applyAction, cfg, outputMove]
          by_cases hx : x = o
          · subst hx; simp [HeadMove.apply]
          · simp [hx, HeadMove.apply]
        · funext x
          simp only [applyAction, cfg]
          by_cases hx : x = o
          · subst hx
            simp only [if_true, Function.update_self, hw, Option.getD_some]
            have hlen : (w.take j).length = j := by simp; omega
            have hwr : writeTapeBit (w.take j) j (w.getD j false) = w.take j ++ [w.getD j false] := by
              have e := write_end (w.take j) (w.getD j false)
              rwa [hlen] at e
            rw [hwr, List.take_add_one]
            congr 1
            rw [List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem (by omega)]
            rfl
          · simp [hx]

/-- The whole writing phase, ending in `done`. -/
theorem write_done (hw : answer a b = some w) (hW : w.length ≤ W)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (hh : heads o = 0) (hT : tapes o = []) :
    Timed (machine (W := W) ht o answer) (w.length + 1) (cfg (.write ⟨0, Nat.succ_pos W⟩ a b) heads tapes)
      (cfg .done (Function.update heads o w.length) (Function.update tapes o w)) := by
  have h := write_timed (W := W) ht o answer hw hW heads tapes hh hT w.length (le_refl _)
  rw [List.take_length] at h
  refine h.trans (Timed.single ?_ ?_)
  · rw [halted_cfg]
    rfl
  · rw [step_cfg]
    have hc : ¬ (w.length < ((answer a b).getD []).length ∧ w.length < W) := by
      rw [hw]; simp
    simp only [transition, hc, dite_false, Option.map_some]
    rfl

end Write

/-- Rewinding phase: after `i ≤ B` steps heads 0 and 1 are at cell `B - i`. -/
theorem back_timed (tapes : Fin t → List Bool) : ∀ (i : ℕ) (hi : i ≤ B),
    Timed (machine (W := W) ht o answer) i (cfg (.back (Fin.last B)) (readHeads B) tapes)
      (cfg (.back ⟨B - i, by omega⟩) (readHeads (B - i)) tapes)
  | 0, _ => by
      simp only [Nat.sub_zero]
      exact Timed.refl _ _
  | i + 1, hi => by
      have ih := back_timed tapes i (by omega)
      refine ih.trans (Timed.single ?_ ?_)
      · rw [halted_cfg]
        rfl
      · rw [step_cfg]
        have hpos : 0 < B - i := by omega
        simp only [transition, hpos, dite_true, Option.map_some]
        congr 1
        refine configuration_ext ?_ ?_ rfl
        · change enc B W _ = enc B W _
          congr 2
        · funext x
          simp only [applyAction, cfg, inputMove, readHeads]
          by_cases hx : x.val < 2
          · simp only [hx, if_true, HeadMove.apply]
            omega
          · simp [hx, HeadMove.apply]

/-- The whole rewinding phase, ending in `go` with every head at 0. -/
theorem back_go (tapes : Fin t → List Bool) :
    Timed (machine (W := W) ht o answer) (B + 1) (cfg (.back (Fin.last B)) (readHeads B) tapes)
      (cfg .go (fun _ => 0) tapes) := by
  have h := back_timed (W := W) ht o answer tapes B (le_refl _)
  refine h.trans (Timed.single ?_ ?_)
  · rw [halted_cfg]
    rfl
  · rw [step_cfg]
    simp only [transition, Nat.sub_self, lt_irrefl, dite_false, Option.map_some]
    congr 1
    refine configuration_ext rfl ?_ rfl
    funext x
    simp [applyAction, cfg, idle, readHeads, HeadMove.apply]

theorem initial_eq (tapes : Fin t → List Bool) :
    initialConfiguration (machine (W := W) ht o answer) tapes =
      cfg (.read ⟨0, Nat.succ_pos B⟩ (fun _ => false) (fun _ => false)) (readHeads 0) tapes := by
  rw [readHeads_zero]
  rfl

/-- Gate outcome 1: a table entry `w` is written on the output tape, and the gate halts in
`done` after `B + |w| + 2` steps. -/
theorem gate_small (tapes : Fin t → List Bool) (ho0 : o.val ≠ 0) (ho1 : o.val ≠ 1)
    (hT : tapes o = []) {w : List Bool}
    (hw : answer (window B (tapes (tape0 ht))) (window B (tapes (tape1 ht))) = some w)
    (hW : w.length ≤ W) :
    ∃ r, runFrom (machine (W := W) ht o answer) (B + 1 + (w.length + 1))
      (initialConfiguration (machine (W := W) ht o answer) tapes) = some r ∧
      r.final = cfg .done (Function.update (readHeads B) o w.length) (Function.update tapes o w) := by
  have hr := read_timed (W := W) ht o answer tapes B (le_refl _)
  rw [pad_B, pad_B] at hr
  have hd := decide_step (W := W) ht o answer (readHeads B) tapes (window B (tapes (tape0 ht)))
    (window B (tapes (tape1 ht)))
  rw [hw] at hd
  have hlast : (⟨B, by omega⟩ : Fin (B + 1)) = Fin.last B := Fin.ext rfl
  rw [hlast] at hr
  have hs := Timed.single (by rw [halted_cfg]; rfl) hd
  have hho : readHeads B o = 0 := by simp [readHeads]; omega
  have hwd := write_done (W := W) ht o answer hw hW (readHeads B) tapes hho hT
  have whole := (hr.trans hs).trans hwd
  rw [← initial_eq (W := W) ht o answer] at whole
  obtain ⟨r, hrun, hfin, _⟩ := whole.run (by rw [halted_cfg]; rfl)
  exact ⟨r, hrun, hfin⟩

/-- Gate outcome 2: no table entry. The gate halts in `go` after `2B + 2` steps, with every tape
untouched and every head at 0. -/
theorem gate_large (tapes : Fin t → List Bool)
    (hw : answer (window B (tapes (tape0 ht))) (window B (tapes (tape1 ht))) = none) :
    ∃ r, runFrom (machine (W := W) ht o answer) (B + 1 + (B + 1))
      (initialConfiguration (machine (W := W) ht o answer) tapes) = some r ∧
      r.final = cfg .go (fun _ => 0) tapes := by
  have hr := read_timed (W := W) ht o answer tapes B (le_refl _)
  rw [pad_B, pad_B] at hr
  have hd := decide_step (W := W) ht o answer (readHeads B) tapes (window B (tapes (tape0 ht)))
    (window B (tapes (tape1 ht)))
  rw [hw] at hd
  have hlast : (⟨B, by omega⟩ : Fin (B + 1)) = Fin.last B := Fin.ext rfl
  rw [hlast] at hr
  have hs := Timed.single (by rw [halted_cfg]; rfl) hd
  have hb := back_go (W := W) ht o answer tapes
  have whole := (hr.trans hs).trans hb
  rw [← initial_eq (W := W) ht o answer] at whole
  obtain ⟨r, hrun, hfin, _⟩ := whole.run (by rw [halted_cfg]; rfl)
  exact ⟨r, hrun, hfin⟩

/-! ## The gate in front of a fixed machine `L` -/

/-- Control sizes of the two programs. -/
def sizes (B W sL : ℕ) : Fin 2 → ℕ := ![Fintype.card (State B W), sL]

/-- Program 0 is the gate, program 1 is `L`. -/
noncomputable def programs {sL : ℕ} (L : Machine t sL) :
    (j : Fin 2) → Machine t (sizes B W sL j) := by
  intro j
  refine Fin.cases (motive := fun j => Machine t (sizes B W sL j)) (machine (W := W) ht o answer) ?_ j
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact L

/-- After the gate: call `L` exactly when the gate halted in `go`; stop otherwise. -/
noncomputable def next (B W sL : ℕ) :
    (j : Fin 2) → Fin (sizes B W sL j) → (Fin t → Bool) → Option (Fin 2) :=
  fun j q _ => if j.val = 0 ∧ q.val = (enc B W .go).val then some 1 else none

/-- The gate followed, when needed, by `L`. -/
noncomputable def combined {sL : ℕ} (L : Machine t sL) :
    Machine t (Fintype.card (RecoveryCalls.Control (sizes B W sL))) :=
  RecoveryCalls.machine (sizes B W sL) (programs (W := W) ht o answer L) 0 (next B W sL)

/-- The gate halts in `done` without calling `L`. -/
theorem next_done (sL : ℕ) (bits : Fin t → Bool) :
    next (t := t) B W sL 0 (enc B W .done) bits = none := by
  have hne : (enc B W .done).val ≠ (enc B W .go).val := by
    intro h
    have := (enc B W).injective (Fin.ext h)
    cases this
  simp only [next]
  rw [if_neg]
  rintro ⟨_, h⟩
  exact hne h

/-- **Outcome 1 of the combined machine**: a table entry `w` ends on the output tape, within
`B + W + 3` steps. -/
theorem combined_small_run {sL : ℕ} (L : Machine t sL) (tapes : Fin t → List Bool)
    (ho0 : o.val ≠ 0) (ho1 : o.val ≠ 1) (hT : tapes o = []) {w : List Bool}
    (hw : answer (window B (tapes (tape0 ht))) (window B (tapes (tape1 ht))) = some w)
    (hW : w.length ≤ W) :
    ∃ r, run (combined (W := W) ht o answer L) (B + W + 3) tapes = some r ∧ r.final.tapes o = w := by
  obtain ⟨g, hg, hgf⟩ := gate_small (W := W) ht o answer tapes ho0 ho1 hT hw hW
  have hg' : runFrom (programs (W := W) ht o answer L 0) (B + 1 + (w.length + 1))
      (initialConfiguration (programs (W := W) ht o answer L 0) tapes) = some g := hg
  have hn : next (t := t) B W sL 0 g.final.control g.final.scanned = none := by
    rw [hgf]
    exact next_done (t := t) (B := B) (W := W) sL _
  obtain ⟨n, hnle, hpath⟩ := stop_receipt (sizes B W sL) (programs (W := W) ht o answer L) 0
    (next B W sL) 0 _ _ g hg' hn
  have hin : controlConfig (RecoveryCalls.code (sizes B W sL) 0)
      (initialConfiguration (programs (W := W) ht o answer L 0) tapes) =
        initialConfiguration (combined (W := W) ht o answer L) tapes := rfl
  rw [hin] at hpath
  obtain ⟨actual, ha, hf, _⟩ := hpath.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
  have hbound : n ≤ B + W + 3 := by omega
  have hm := run_moreFuel (combined (W := W) ht o answer L) n (B + W + 3 - n) tapes actual ha
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨actual, hm, ?_⟩
  rw [hf]
  change g.final.tapes o = w
  rw [hgf]
  simp [cfg]

/-- **Outcome 2 of the combined machine**: no table entry, and `L` halts from its own initial
configuration within `fuel`. The combined machine then ends with `L`'s final tapes, within
`fuel + 2B + 4` steps. -/
theorem combined_large_run {sL : ℕ} (L : Machine t sL) (tapes : Fin t → List Bool)
    (hw : answer (window B (tapes (tape0 ht))) (window B (tapes (tape1 ht))) = none)
    (fuel : ℕ) (rL : ExecutionReceipt t sL) (hL : run L fuel tapes = some rL) :
    ∃ r, run (combined (W := W) ht o answer L) (fuel + 2 * B + 4) tapes = some r ∧
      r.final.tapes = rL.final.tapes := by
  obtain ⟨g, hg, hgf⟩ := gate_large (W := W) ht o answer tapes hw
  have hg' : runFrom (programs (W := W) ht o answer L 0) (B + 1 + (B + 1))
      (initialConfiguration (programs (W := W) ht o answer L 0) tapes) = some g := hg
  have hn : next (t := t) B W sL 0 g.final.control g.final.scanned = some 1 := by
    rw [hgf]
    simp [next, cfg]
  obtain ⟨ng, hng, gatePath⟩ := call_receipt (sizes B W sL) (programs (W := W) ht o answer L) 0
    (next B W sL) 0 1 _ _ g hg' hn
  have hi : RecoveryCalls.restarted (programs (W := W) ht o answer L 1) g.final.heads g.final.tapes =
      initialConfiguration (programs (W := W) ht o answer L 1) tapes := by
    rw [hgf]
    rfl
  have hin : controlConfig (RecoveryCalls.code (sizes B W sL) 0)
      (initialConfiguration (programs (W := W) ht o answer L 0) tapes) =
        initialConfiguration (combined (W := W) ht o answer L) tapes := rfl
  rw [hi, hin] at gatePath
  have hL' : runFrom (programs (W := W) ht o answer L 1) fuel
      (initialConfiguration (programs (W := W) ht o answer L 1) tapes) = some rL := hL
  obtain ⟨nl, hnl, lPath⟩ := stop_receipt (sizes B W sL) (programs (W := W) ht o answer L) 0
    (next B W sL) 1 fuel _ rL hL' (by simp [next])
  have whole := gatePath.trans lPath
  obtain ⟨actual, ha, hf, _⟩ := whole.run (by simp [RecoveryCalls.machine, RecoveryCalls.stopped])
  have hbound : ng + nl ≤ fuel + 2 * B + 4 := by omega
  have hm := run_moreFuel (combined (W := W) ht o answer L) (ng + nl) (fuel + 2 * B + 4 - (ng + nl)) tapes
    actual ha
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨actual, hm, ?_⟩
  rw [hf]
  rfl

end Machine

end Gate

end NearCubicWires.Bindings.Williams14
