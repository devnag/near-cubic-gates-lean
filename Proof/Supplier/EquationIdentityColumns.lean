import Proof.MachineModel.Runs
import Proof.MachineModel.OrdinaryStreamController
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.PCP.ProjectionNormalizationForwardRules

namespace NearCubicWires.RepairOrdinary.EquationIdentityColumns
open LocalBitMultitape SignedSortKey NearCubicWires.ExtDecompositionBatch RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## The word -/

/-- The identity columns: `frame (binary d (2^j))` for `j < d`. -/
def word (d : ℕ) : List Bool := (List.range d).flatMap (fun j => frame (binary d (2 ^ j)))

/-- The output before pass `j`: `out`, then the columns `0, …, j-1`. -/
def outj (out : List Bool) (d j : ℕ) : List Bool := out ++ (List.range j).flatMap (fun i => frame (binary d (2 ^ i)))

/-! ## Three base tapes: 0 the count, 1 the output, 2 the column -/

/-- One action on the base tapes; the count tape is never written. -/
def act {s : ℕ} (next : Fin s) (wO wH : Option Bool) (mC mO mH : HeadMove) : Action 3 s :=
  ⟨next, ![none, wO, wH], ![mC, mO, mH]⟩

def cfg {s : ℕ} (q : Fin s) (C O H : List Bool) (hc ho hh : ℕ) : Configuration 3 s :=
  ⟨q, ![hc, ho, hh], ![C, O, H]⟩

namespace First

/-- The first column from the count. States `0`/`2` read the next count cell (for the first item / a
later item), `1`/`3` write that item's bit (`true` for the first item, `false` after it), `4` halts.
It writes `frame (binary d 1)` on `H`; `C` and `H` only move right. -/
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then act 1 none (some true) .stay .stay .right else act 4 none (some false) .stay .stay .stay)
    else if q.val = 1 then some (act 2 none (some true) .right .stay .right)
    else if q.val = 2 then
      some (if sc 0 then act 3 none (some true) .stay .stay .right else act 4 none (some false) .stay .stay .stay)
    else if q.val = 3 then some (act 2 none (some false) .right .stay .right)
    else none

end First

namespace Emit

/-- One pass over the column. States `0`/`1` read a marker of `H` carrying `false`/`true`; `2`/`3` read a
bit of `H` and write the carry back in its place; `4` halts. Every scanned cell of `H` is appended to `O`.
So `O` gains `frame w` and `H` becomes `frame` of `w` shifted up by one bit. -/
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 2 then act 2 (some true) none .stay .right .right else act 4 (some false) none .stay .right .stay)
    else if q.val = 1 then
      some (if sc 2 then act 3 (some true) none .stay .right .right else act 4 (some false) none .stay .right .stay)
    else if q.val = 2 then
      some (if sc 2 then act 1 (some true) (some false) .stay .right .right
        else act 0 (some false) (some false) .stay .right .right)
    else if q.val = 3 then
      some (if sc 2 then act 1 (some true) (some true) .stay .right .right
        else act 0 (some false) (some true) .stay .right .right)
    else none

end Emit

namespace Erase

/-- Clear the column in place. State `0` reads a marker of `H` (a `true` marker is cleared), `1` clears a
bit, `2` halts. -/
def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 2 then act 1 none (some false) .stay .stay .right else act 2 none none .stay .stay .stay)
    else if q.val = 1 then some (act 0 none (some false) .stay .stay .right)
    else none

end Erase

/-- Step the count tape's head to the next cell. -/
def nudge : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some (act 1 none none .right .stay .stay) else none

/-! ## Assembly -/

/-- Restore one head (`CursorRestore`): the new last tape logs exactly the target's right moves. -/
abbrev restore {t s : ℕ} (p : Machine t s) (target : Fin t) : Machine (t + 1) (s + 2) :=
  RepairSource.ProjectionNormalization.CursorRestore.machine p target

/-- The count tape inside the four-tape stages. -/
def C4 : Fin (3 + 1) := (0 : Fin 3).castAdd 1

def initM := restore (restore First.machine 2) C4
def passM := Composition.machine (restore Emit.machine 2) (TapeEmbedding.machine 1 nudge)
def loopM := StreamController.machine passM C4
def loopR := restore loopM C4
def eraseM := TapeEmbedding.machine 1 (restore Erase.machine 2)

/-- **The identity-columns writer.** Tapes: count, output, column, the column's log, the count's log. -/
def machine : Machine 5 27 := Composition.machine (Composition.machine initM loopR) eraseM

def budget (d : ℕ) : ℕ := 64 * (d + 1) ^ 2

/-! ## Tape facts -/

theorem outj_zero (out : List Bool) (d : ℕ) : outj out d 0 = out := by simp [outj]

theorem outj_succ (out : List Bool) (d j : ℕ) : outj out d (j + 1) = outj out d j ++ frame (binary d (2 ^ j)) := by
  simp [outj, List.range_succ, List.flatMap_append]

theorem outj_word (out : List Bool) (d : ℕ) : outj out d d = out ++ word d := rfl

theorem write_mid (pre tail : List Bool) (old v : Bool) :
    writeTapeBit (pre ++ old :: tail) pre.length v = pre ++ v :: tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa [writeTapeBit] using congrArg (List.cons b) ih

theorem read_count (d i : ℕ) : readTapeBit (List.replicate d true) i = decide (i < d) := by
  by_cases h : i < d
  · have e : List.replicate d true = List.replicate i true ++ true :: List.replicate (d - i - 1) true := by
      rw [← List.replicate_succ, ← List.replicate_add]; congr 1; omega
    rw [e, decide_eq_true h]
    simpa using Streaming.read_append (List.replicate i true) (List.replicate (d - i - 1) true) true
  · rw [decide_eq_false h]
    unfold readTapeBit
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

/-- Write an optional bit at a head. -/
def wr (tape : List Bool) (head : ℕ) : Option Bool → List Bool
  | none => tape
  | some b => writeTapeBit tape head b

theorem step_cfg {s : ℕ} (p : Machine 3 s) (q next : Fin s) (C O H : List Bool) (hc ho hh : ℕ)
    (wO wH : Option Bool) (mC mO mH : HeadMove)
    (hr : p.rule q ![readTapeBit C hc, readTapeBit O ho, readTapeBit H hh] = some (act next wO wH mC mO mH)) :
    step p (cfg q C O H hc ho hh) =
      some (cfg next C (wr O ho wO) (wr H hh wH) (mC.apply hc) (mO.apply ho) (mH.apply hh)) := by
  have hs : (cfg q C O H hc ho hh).scanned = ![readTapeBit C hc, readTapeBit O ho, readTapeBit H hh] := by
    funext i; fin_cases i <;> rfl
  unfold step
  rw [hs]
  change (p.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · rfl
    · cases wO <;> rfl
    · cases wH <;> rfl

/-- The cursor-restoration premise (`CursorRestore.NoLeft`): tape `i` never moves left. -/
abbrev NoLeft {t s : ℕ} (p : Machine t s) (i : Fin t) : Prop :=
  RepairSource.ProjectionNormalization.CursorRestore.NoLeft p i

/-! ## The first column -/

namespace First

def item (f : Bool) : Fin 5 := if f then 0 else 2
def bit (f : Bool) : Fin 5 := if f then 1 else 3

/-- The bits written from a count suffix of length `k`: `f` first, then `false`s. -/
def bits : Bool → ℕ → List Bool
  | _, 0 => []
  | f, k + 1 => f :: bits false k

theorem bits_false (k : ℕ) : bits false k = binary k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bits, ih]; rfl

theorem bits_one (d : ℕ) : bits true d = binary d 1 := by
  cases d with
  | zero => rfl
  | succ d => simp only [bits, bits_false]; rfl

theorem item_step (f : Bool) (C O H : List Bool) (hc ho : ℕ) (hr : readTapeBit C hc = true) :
    step machine (cfg (item f) C O H hc ho H.length) = some (cfg (bit f) C O (H ++ [true]) hc ho (H.length + 1)) := by
  cases f
  · show step machine (cfg 2 C O H hc ho H.length) = some (cfg 3 C O (H ++ [true]) hc ho (H.length + 1))
    rw [step_cfg machine 2 3 C O H hc ho H.length none (some true) .stay .stay .right (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 0 C O H hc ho H.length) = some (cfg 1 C O (H ++ [true]) hc ho (H.length + 1))
    rw [step_cfg machine 0 1 C O H hc ho H.length none (some true) .stay .stay .right (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem bit_step (f : Bool) (C O H : List Bool) (hc ho : ℕ) :
    step machine (cfg (bit f) C O H hc ho H.length) = some (cfg (item false) C O (H ++ [f]) (hc + 1) ho (H.length + 1)) := by
  cases f
  · show step machine (cfg 3 C O H hc ho H.length) = some (cfg 2 C O (H ++ [false]) (hc + 1) ho (H.length + 1))
    rw [step_cfg machine 3 2 C O H hc ho H.length none (some false) .right .stay .right (by simp [machine])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 1 C O H hc ho H.length) = some (cfg 2 C O (H ++ [true]) (hc + 1) ho (H.length + 1))
    rw [step_cfg machine 1 2 C O H hc ho H.length none (some true) .right .stay .right (by simp [machine])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem halt_step (f : Bool) (C O H : List Bool) (hc ho : ℕ) (hr : readTapeBit C hc = false) :
    step machine (cfg (item f) C O H hc ho H.length) = some (cfg 4 C O (H ++ [false]) hc ho H.length) := by
  cases f
  · show step machine (cfg 2 C O H hc ho H.length) = some (cfg 4 C O (H ++ [false]) hc ho H.length)
    rw [step_cfg machine 2 4 C O H hc ho H.length none (some false) .stay .stay .stay (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 0 C O H hc ho H.length) = some (cfg 4 C O (H ++ [false]) hc ho H.length)
    rw [step_cfg machine 0 4 C O H hc ho H.length none (some false) .stay .stay .stay (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem timed (d ho : ℕ) (O : List Bool) (k : ℕ) : ∀ (i : ℕ) (H : List Bool) (f : Bool), i + k = d →
    Timed machine (2 * k + 1) (cfg (item f) (List.replicate d true) O H i ho H.length)
      (cfg 4 (List.replicate d true) O (H ++ frame (bits f k)) d ho (H.length + 2 * k)) := by
  induction k with
  | zero =>
    intro i H f hi
    have hid : i = d := by omega
    subst hid
    have hs := halt_step f (List.replicate i true) O H i ho (by rw [read_count]; simp)
    simpa [bits, frame] using Timed.single (p := machine) (by cases f <;> rfl) hs
  | succ k ih =>
    intro i H f hi
    have hs1 := item_step f (List.replicate d true) O H i ho (by rw [read_count]; simp; omega)
    have hs2 := bit_step f (List.replicate d true) O (H ++ [true]) i ho
    have t1 := Timed.single (p := machine) (by cases f <;> rfl) hs1
    have e1 : (H ++ [true]).length = H.length + 1 := by simp
    rw [e1] at hs2
    have t2 := Timed.single (p := machine) (by cases f <;> rfl) hs2
    have tail := ih (i + 1) (H ++ [true] ++ [f]) false (by omega)
    have e2 : (H ++ [true] ++ [f]).length = H.length + 1 + 1 := by simp
    have e3 : H ++ [true] ++ [f] ++ frame (bits false k) = H ++ frame (bits f (k + 1)) := by simp [bits, frame]
    have e4 : H.length + 1 + 1 + 2 * k = H.length + 2 * (k + 1) := by omega
    rw [e2, e3, e4] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * k + 1) = 2 * (k + 1) + 1 by omega] at this

theorem run (d ho : ℕ) (O : List Bool) :
    Step machine (2 * d + 1) ![0, ho, 0] ![List.replicate d true, O, []]
      ![d, ho, 2 * d] ![List.replicate d true, O, frame (binary d 1)] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed d ho O d 0 [] true (by omega)).run (by rfl)
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg, bits_one]

theorem forward (i : Fin 3) : NoLeft machine i := by
  intro q bs a ha
  simp only [machine] at ha
  split_ifs at ha <;> cases ha <;> fin_cases i <;> simp [act]

end First

/-! ## One pass: emit the column, shift it in place -/

namespace Emit

def mark (c : Bool) : Fin 5 := if c then 1 else 0
def bitS (c : Bool) : Fin 5 := if c then 3 else 2

/-- `w` shifted up by one bit with carry-in `c` (the top bit drops). -/
def shift : Bool → List Bool → List Bool
  | _, [] => []
  | c, a :: w => c :: shift a w

theorem shift_binary (d m : ℕ) (c : Bool) : shift c (binary d m) = binary d (2 * m + c.toNat) := by
  induction d generalizing m c with
  | zero => rfl
  | succ d ih =>
    have e1 : binary (d + 1) m = (m % 2 == 1) :: binary d (m / 2) := rfl
    have e2 : binary (d + 1) (2 * m + c.toNat) =
        ((2 * m + c.toNat) % 2 == 1) :: binary d ((2 * m + c.toNat) / 2) := rfl
    rw [e1, e2]
    simp only [shift]
    rw [ih (m / 2) (m % 2 == 1)]
    congr 1
    · cases c <;> simp
    · congr 1
      cases c <;> cases h : m % 2 == 1 <;> simp_all [Bool.toNat] <;> omega

theorem mark_step (c : Bool) (C O H : List Bool) (hc hh : ℕ) (hr : readTapeBit H hh = true) :
    step machine (cfg (mark c) C O H hc O.length hh) =
      some (cfg (bitS c) C (O ++ [true]) H hc (O.length + 1) (hh + 1)) := by
  cases c
  · show step machine (cfg 0 C O H hc O.length hh) = some (cfg 2 C (O ++ [true]) H hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 0 2 C O H hc O.length hh (some true) none .stay .right .right (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 1 C O H hc O.length hh) = some (cfg 3 C (O ++ [true]) H hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 1 3 C O H hc O.length hh (some true) none .stay .right .right (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem bit_step (c a : Bool) (C O H : List Bool) (hc hh : ℕ) (hr : readTapeBit H hh = a) :
    step machine (cfg (bitS c) C O H hc O.length hh) =
      some (cfg (mark a) C (O ++ [a]) (writeTapeBit H hh c) hc (O.length + 1) (hh + 1)) := by
  cases c <;> cases a
  · show step machine (cfg 2 C O H hc O.length hh) =
      some (cfg 0 C (O ++ [false]) (writeTapeBit H hh false) hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 2 0 C O H hc O.length hh (some false) (some false) .stay .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 2 C O H hc O.length hh) =
      some (cfg 1 C (O ++ [true]) (writeTapeBit H hh false) hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 2 1 C O H hc O.length hh (some true) (some false) .stay .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 3 C O H hc O.length hh) =
      some (cfg 0 C (O ++ [false]) (writeTapeBit H hh true) hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 3 0 C O H hc O.length hh (some false) (some true) .stay .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 3 C O H hc O.length hh) =
      some (cfg 1 C (O ++ [true]) (writeTapeBit H hh true) hc (O.length + 1) (hh + 1))
    rw [step_cfg machine 3 1 C O H hc O.length hh (some true) (some true) .stay .right .right
      (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem end_step (c : Bool) (C O H : List Bool) (hc hh : ℕ) (hr : readTapeBit H hh = false) :
    step machine (cfg (mark c) C O H hc O.length hh) = some (cfg 4 C (O ++ [false]) H hc (O.length + 1) hh) := by
  cases c
  · show step machine (cfg 0 C O H hc O.length hh) = some (cfg 4 C (O ++ [false]) H hc (O.length + 1) hh)
    rw [step_cfg machine 0 4 C O H hc O.length hh (some false) none .stay .right .stay (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]
  · show step machine (cfg 1 C O H hc O.length hh) = some (cfg 4 C (O ++ [false]) H hc (O.length + 1) hh)
    rw [step_cfg machine 1 4 C O H hc O.length hh (some false) none .stay .right .stay (by simp [machine, hr])]
    simp [wr, HeadMove.apply, Streaming.write_append]

theorem timed (C : List Bool) (hc : ℕ) (w : List Bool) : ∀ (pre O : List Bool) (c : Bool),
    Timed machine (2 * w.length + 1) (cfg (mark c) C O (pre ++ frame w) hc O.length pre.length)
      (cfg 4 C (O ++ frame w) (pre ++ frame (shift c w)) hc (O.length + (2 * w.length + 1))
        (pre.length + 2 * w.length)) := by
  induction w with
  | nil =>
    intro pre O c
    have hs := end_step c C O (pre ++ frame []) hc pre.length
      (by simpa [frame] using Streaming.read_append pre [] false)
    simpa [frame, shift] using Timed.single (p := machine) (by cases c <;> rfl) hs
  | cons a w ih =>
    intro pre O c
    have hr1 : readTapeBit (pre ++ frame (a :: w)) pre.length = true := by
      simpa [frame] using Streaming.read_append pre (a :: frame w) true
    have hr2 : readTapeBit (pre ++ frame (a :: w)) (pre.length + 1) = a := by
      simpa [frame] using Streaming.read_append (pre ++ [true]) (frame w) a
    have hs1 := mark_step c C O (pre ++ frame (a :: w)) hc pre.length hr1
    have hs2 := bit_step c a C (O ++ [true]) (pre ++ frame (a :: w)) hc (pre.length + 1) hr2
    have hw : writeTapeBit (pre ++ frame (a :: w)) (pre.length + 1) c = pre ++ [true, c] ++ frame w := by
      simpa [frame] using write_mid (pre ++ [true]) (frame w) a c
    have e1 : (O ++ [true]).length = O.length + 1 := by simp
    rw [hw, e1] at hs2
    have t1 := Timed.single (p := machine) (by cases c <;> rfl) hs1
    have t2 := Timed.single (p := machine) (by cases a <;> cases c <;> rfl) hs2
    have tail := ih (pre ++ [true, c]) (O ++ [true] ++ [a]) a
    have e2 : (O ++ [true] ++ [a]).length = O.length + 1 + 1 := by simp
    have e3 : (pre ++ [true, c]).length = pre.length + 1 + 1 := by simp
    have e4 : O ++ [true] ++ [a] ++ frame w = O ++ frame (a :: w) := by simp [frame]
    have e5 : pre ++ [true, c] ++ frame (shift a w) = pre ++ frame (shift c (a :: w)) := by simp [frame, shift]
    have e6 : O.length + 1 + 1 + (2 * w.length + 1) = O.length + (2 * (a :: w).length + 1) := by simp; omega
    have e7 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (a :: w).length := by simp; omega
    rw [e2, e3, e4, e5, e6, e7] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

theorem run (d m hc : ℕ) (C O : List Bool) :
    Step machine (2 * d + 1) ![hc, O.length, 0] ![C, O, frame (binary d m)]
      ![hc, (O ++ frame (binary d m)).length, 2 * d] ![C, O ++ frame (binary d m), frame (binary d (2 * m))] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed C hc (binary d m) [] O false).run (by rfl)
  rw [binary_length] at hr hs
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg, shift_binary]

theorem forward (i : Fin 3) : NoLeft machine i := by
  intro q bs a ha
  simp only [machine] at ha
  split_ifs at ha <;> cases ha <;> fin_cases i <;> simp [act]

end Emit

/-! ## Clearing the column -/

namespace Erase

theorem mark_step (C O H : List Bool) (hc ho hh : ℕ) (hr : readTapeBit H hh = true) :
    step machine (cfg 0 C O H hc ho hh) = some (cfg 1 C O (writeTapeBit H hh false) hc ho (hh + 1)) := by
  rw [step_cfg machine 0 1 C O H hc ho hh none (some false) .stay .stay .right (by simp [machine, hr])]
  simp [wr, HeadMove.apply]

theorem bit_step (C O H : List Bool) (hc ho hh : ℕ) :
    step machine (cfg 1 C O H hc ho hh) = some (cfg 0 C O (writeTapeBit H hh false) hc ho (hh + 1)) := by
  rw [step_cfg machine 1 0 C O H hc ho hh none (some false) .stay .stay .right (by simp [machine])]
  simp [wr, HeadMove.apply]

theorem end_step (C O H : List Bool) (hc ho hh : ℕ) (hr : readTapeBit H hh = false) :
    step machine (cfg 0 C O H hc ho hh) = some (cfg 2 C O H hc ho hh) := by
  rw [step_cfg machine 0 2 C O H hc ho hh none none .stay .stay .stay (by simp [machine, hr])]
  simp [wr, HeadMove.apply]

theorem timed (C O : List Bool) (hc ho : ℕ) (w : List Bool) : ∀ pre : List Bool,
    Timed machine (2 * w.length + 1) (cfg 0 C O (pre ++ frame w) hc ho pre.length)
      (cfg 2 C O (pre ++ List.replicate (2 * w.length + 1) false) hc ho (pre.length + 2 * w.length)) := by
  induction w with
  | nil =>
    intro pre
    have hs := end_step C O (pre ++ frame []) hc ho pre.length
      (by simpa [frame] using Streaming.read_append pre [] false)
    simpa [frame] using Timed.single (p := machine) rfl hs
  | cons a w ih =>
    intro pre
    have hr1 : readTapeBit (pre ++ frame (a :: w)) pre.length = true := by
      simpa [frame] using Streaming.read_append pre (a :: frame w) true
    have hs1 := mark_step C O (pre ++ frame (a :: w)) hc ho pre.length hr1
    have hw1 : writeTapeBit (pre ++ frame (a :: w)) pre.length false = pre ++ [false] ++ a :: frame w := by
      simpa [frame] using write_mid pre (a :: frame w) true false
    rw [hw1] at hs1
    have hs2 := bit_step C O (pre ++ [false] ++ a :: frame w) hc ho (pre.length + 1)
    have hw2 : writeTapeBit (pre ++ [false] ++ a :: frame w) (pre.length + 1) false = pre ++ [false, false] ++ frame w := by
      simpa using write_mid (pre ++ [false]) (frame w) a false
    rw [hw2] at hs2
    have t1 := Timed.single (p := machine) rfl hs1
    have t2 := Timed.single (p := machine) rfl hs2
    have tail := ih (pre ++ [false, false])
    have e3 : (pre ++ [false, false]).length = pre.length + 1 + 1 := by simp
    have e5 : pre ++ [false, false] ++ List.replicate (2 * w.length + 1) false =
        pre ++ List.replicate (2 * (a :: w).length + 1) false := by
      rw [List.append_assoc, show 2 * (a :: w).length + 1 = 2 + (2 * w.length + 1) by simp; omega,
        List.replicate_add 2 (2 * w.length + 1) false]
      rfl
    have e7 : pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (a :: w).length := by simp; omega
    rw [e3, e5, e7] at tail
    have := (t1.trans t2).trans tail
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (a :: w).length + 1 by simp; omega] at this

theorem run (w C O : List Bool) (hc ho : ℕ) :
    Step machine (2 * w.length + 1) ![hc, ho, 0] ![C, O, frame w]
      ![hc, ho, 2 * w.length] ![C, O, List.replicate (2 * w.length + 1) false] := by
  obtain ⟨r, hr, hf, hs⟩ := (timed C O hc ho w []).run (by rfl)
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; simp [cfg]
  · rw [hf]; simp [cfg]

theorem forward (i : Fin 3) : NoLeft machine i := by
  intro q bs a ha
  simp only [machine] at ha
  split_ifs at ha <;> cases ha <;> fin_cases i <;> simp [act]

end Erase

theorem nudge_run (C O H : List Bool) (hc ho hh : ℕ) :
    Step nudge 1 ![hc, ho, hh] ![C, O, H] ![hc + 1, ho, hh] ![C, O, H] := by
  have hs : step nudge (cfg 0 C O H hc ho hh) = some (cfg 1 C O H (hc + 1) ho hh) := by
    rw [step_cfg nudge 0 1 C O H hc ho hh none none .right .stay .stay (by simp [nudge])]
    rfl
  obtain ⟨r, hr, hf, hs'⟩ := (Timed.single (p := nudge) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

theorem nudge_forward (i : Fin 3) : NoLeft nudge i := by
  intro q bs a ha
  simp only [nudge] at ha
  split_ifs at ha
  cases ha
  fin_cases i <;> simp [act]

/-! ## Motion facts for the combinators (the output head only moves right) -/

theorem restore_other {t s : ℕ} (p : Machine t s) (target i : Fin t) (hi : i ≠ target) (hp : NoLeft p i) :
    NoLeft (restore p target) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q = true
    · simp [restore, RepairSource.ProjectionNormalization.CursorRestore.machine, hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j => bits (j.castAdd 1)) with
      | none => simp [restore, RepairSource.ProjectionNormalization.CursorRestore.machine, hh, hr] at ha
      | some b =>
        simp [restore, RepairSource.ProjectionNormalization.CursorRestore.machine, hh, hr] at ha
        subst a
        simpa only [RepairSource.ProjectionNormalization.CursorRestore.recordAction, Fin.addCases_left] using
          hp q (fun j => bits (j.castAdd 1)) b hr
  · simp only [restore, RepairSource.ProjectionNormalization.CursorRestore.machine, Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha
        simp [MaskedReset.rewindAction, hi]
      · cases ha
        simp [Rewind.finishAction]
    · contradiction

theorem stream_forward {t s : ℕ} (p : Machine t s) (driver i : Fin t) (hp : NoLeft p i) :
    NoLeft (StreamController.machine p driver) i := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · by_cases hh : p.halted q = true
    · simp [StreamController.machine, hh] at ha
      subst a; simp [StreamController.jump]
    · cases hr : p.rule q bits with
      | none => simp [StreamController.machine, hh, hr] at ha
      | some b =>
        simp [StreamController.machine, hh, hr] at ha
        subst a
        exact hp q bits b hr
  · simp only [StreamController.machine, Fin.addCases_right] at ha
    split at ha
    · split at ha <;> cases ha <;> simp [StreamController.jump]
    · contradiction

theorem embed_forward {t s : ℕ} (extra : ℕ) (p : Machine t s) (i : Fin t) (hp : NoLeft p i) :
    NoLeft (TapeEmbedding.machine extra p) (i.castAdd extra) := by
  intro q bs a ha
  obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp ha
  subst a
  simpa only [TapeEmbedding.action, Fin.addCases_left] using hp q (fun j => bs (j.castAdd extra)) b hb

/-! ## A restored stage as one `Step`

`CursorRestore` runs the stage, logging each right move of the target on a new last tape, then rewinds
the target by exactly that many moves while erasing the log. So the log ends all-false with length `δ`,
the target's net advance, if it started blank (`k = 0`) or all-false of that same length (`k = δ`). -/

theorem restore_step {t s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (target : Fin t) (hp : NoLeft p target) (h : Step p n hin tin hout tout) (δ : ℕ)
    (hδ : hout target = hin target + δ) (k : ℕ) (hk : k = 0 ∨ k = δ) :
    Step (restore p target) (2 * n + 2)
      (Fin.addCases hin (fun _ : Fin 1 => 0)) (Fin.addCases tin (fun _ : Fin 1 => List.replicate k false))
      (Fin.addCases (fun i => if i = target then hin i else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate δ false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨hpre, hhalt⟩ := prefix_of_run p n _ r hr
  obtain ⟨delta, hdelta, hhead, htimed⟩ :=
    RepairSource.ProjectionNormalization.CursorRestore.recording_timed hpre target hp 0
  simp only [Nat.zero_add] at htimed
  have hmove : hout target = hin target + delta := by rw [← hh]; exact hhead
  have reset := RepairSource.ProjectionNormalization.CursorRestore.rewind_timed p target
    r.final.heads r.final.tapes delta 0
  have bridge := Timed.step
    (by simp [RepairSource.ProjectionNormalization.CursorRestore.machine, Rewind.machine, Rewind.recording,
      Rewind.config])
    (RepairSource.ProjectionNormalization.CursorRestore.bridge_step p target r.final delta hhalt) reset
  obtain ⟨r2, hrun, hf, hs2⟩ := (htimed.trans bridge).run
    (by simp [RepairSource.ProjectionNormalization.CursorRestore.machine, Rewind.machine,
      SelectiveReset.finished, Rewind.config])
  have hmore := runFrom_moreFuel (restore p target) _ (2 * n + 2 - (r.steps + (delta + 1 + 1))) _ r2 hrun
  rw [Nat.add_sub_of_le (by omega)] at hmore
  have base : Step (restore p target) (2 * n + 2)
      (Fin.addCases hin (fun _ : Fin 1 => 0)) (Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases (fun i => if i = target then hin i else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate delta false)) := by
    refine ⟨r2, hmore, ?_, ?_, by omega⟩
    · rw [hf]
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left]
        by_cases hj : j = target
        · subst hj; simp [hh, hmove]
        · simp [hj, hh]
      · simp [SelectiveReset.finished, Rewind.config]
    · rw [hf]
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [SelectiveReset.finished, Rewind.config, ht]
      · simp [SelectiveReset.finished, Rewind.config]
  have hpad := base.pad (Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => k))
  refine (hpad.congr_in rfl ?_).congr rfl ?_
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp [ZeroPadding.pad]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp only [Fin.addCases_right, ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
      congr 1
      omega

/-! ## The stream loop -/

open RecordController (code test stop)

/-- A stream loop: `bound` passes of one body, from bank `j` to bank `j+1`, while the scanned bit is set. -/
structure Loop (t s : ℕ) where
  body : Machine t s
  tape : Fin t
  bound : ℕ
  H : ℕ → Fin t → ℕ
  A : ℕ → Fin t → List Bool
  cost : ℕ
  step : ∀ j, j < bound → Step body cost (H j) (A j) (H (j + 1)) (A (j + 1))
  cont : ∀ j, j < bound → readTapeBit (A j tape) (H j tape) = true
  halt : readTapeBit (A bound tape) (H bound tape) = false

namespace Loop
variable {t s : ℕ}

theorem timed_from (W : Loop t s) (j : ℕ) (hj : j ≤ W.bound) :
    ∃ n, n ≤ (W.bound - j) * (W.cost + 2) + 1 ∧
      Timed (StreamController.machine W.body W.tape) n ⟨test s, W.H j, W.A j⟩ ⟨stop s, W.H W.bound, W.A W.bound⟩ := by
  induction h : W.bound - j generalizing j with
  | zero =>
    have hjb : j = W.bound := by omega
    subst hjb
    refine ⟨1, by omega, ?_⟩
    have hs := StreamController.stop_step W.body W.tape ⟨W.body.start, W.H W.bound, W.A W.bound⟩ W.halt
    exact Timed.single (StreamController.test_halted W.body W.tape) hs
  | succ n ih =>
    have hjb : j < W.bound := by omega
    obtain ⟨r, hr, hh, ht, hs⟩ := W.step j hjb
    have henter := StreamController.enter_step W.body W.tape ⟨W.body.start, W.H j, W.A j⟩ (W.cont j hjb)
    obtain ⟨hp, hhalt⟩ := StreamController.body_prefix W.body W.tape _ _ r hr
    have hret := StreamController.return_step W.body W.tape r.final hhalt
    have t1 := Timed.single (StreamController.test_halted W.body W.tape) henter
    have t2 : Timed (StreamController.machine W.body W.tape) r.steps
        (controlConfig code ⟨W.body.start, W.H j, W.A j⟩) (controlConfig code r.final) := ⟨_, hp⟩
    have t3 := Timed.single (StreamController.body_halted W.body W.tape r.final.control) hret
    have e3 : controlConfig (fun _ => test s) r.final = ⟨test s, W.H (j + 1), W.A (j + 1)⟩ := by
      apply configuration_ext
      · rfl
      · exact hh
      · exact ht
    rw [e3] at t3
    obtain ⟨m, hm, tail⟩ := ih (j + 1) (by omega) (by omega)
    refine ⟨1 + r.steps + 1 + m, ?_, ((t1.trans t2).trans t3).trans tail⟩
    rw [Nat.add_mul, Nat.one_mul]
    generalize n * (W.cost + 2) = X at hm ⊢
    omega

/-- **The whole stream loop as one `Step`.** -/
theorem run (W : Loop t s) :
    Step (StreamController.machine W.body W.tape) (W.bound * (W.cost + 2) + 1)
      (W.H 0) (W.A 0) (W.H W.bound) (W.A W.bound) := by
  obtain ⟨n, hn, htimed⟩ := W.timed_from 0 (Nat.zero_le _)
  obtain ⟨r, hr, hf, hs⟩ := htimed.run (StreamController.stop_halted W.body W.tape)
  simp only [Nat.sub_zero] at hn
  have more := runFrom_moreFuel (StreamController.machine W.body W.tape) n
    (W.bound * (W.cost + 2) + 1 - n) _ r hr
  rw [Nat.add_sub_of_le hn] at more
  refine ⟨r, more, ?_, ?_, by omega⟩
  · rw [hf]
  · rw [hf]

end Loop

/-! ## The passes -/

def passCost (d : ℕ) : ℕ := 2 * (2 * d + 1) + 2 + 1 + 1

/-- Before pass `j`: the count head at `j`, the output `outj out d j`, the column `2^j`, its log. -/
def passH (d j : ℕ) (out : List Bool) : Fin (3 + 1) → ℕ :=
  Fin.addCases ![j, (outj out d j).length, 0] (fun _ : Fin 1 => 0)
def passA (d j : ℕ) (out : List Bool) : Fin (3 + 1) → List Bool :=
  Fin.addCases ![List.replicate d true, outj out d j, frame (binary d (2 ^ j))]
    (fun _ : Fin 1 => List.replicate (2 * d) false)

theorem passH_C4 (d j : ℕ) (out : List Bool) : passH d j out C4 = j := rfl
theorem passA_C4 (d j : ℕ) (out : List Bool) : passA d j out C4 = List.replicate d true := rfl

theorem passH_zero (d : ℕ) (out : List Bool) :
    passH d 0 out = Fin.addCases ![0, out.length, 0] (fun _ : Fin 1 => 0) := by
  unfold passH; rw [outj_zero]
theorem passA_zero (d : ℕ) (out : List Bool) :
    passA d 0 out = Fin.addCases ![List.replicate d true, out, frame (binary d 1)]
      (fun _ : Fin 1 => List.replicate (2 * d) false) := by
  unfold passA; rw [outj_zero, pow_zero]

theorem pass_step (d j : ℕ) (out : List Bool) :
    Step passM (passCost d) (passH d j out) (passA d j out) (passH d (j + 1) out) (passA d (j + 1) out) := by
  have he := restore_step (2 : Fin 3) (Emit.forward 2)
    (Emit.run d (2 ^ j) j (List.replicate d true) (outj out d j)) (2 * d) (by show 2 * d = 0 + 2 * d; omega)
    (2 * d) (Or.inr rfl)
  have hm : Step (restore Emit.machine 2) (2 * (2 * d + 1) + 2) (passH d j out) (passA d j out)
      (Fin.addCases ![j, (outj out d (j + 1)).length, 0] (fun _ : Fin 1 => 0))
      (Fin.addCases ![List.replicate d true, outj out d (j + 1), frame (binary d (2 ^ (j + 1)))]
        (fun _ : Fin 1 => List.replicate (2 * d) false)) := by
    refine he.congr ?_ ?_
    · funext i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right]
      fin_cases k <;> simp [outj_succ]
    · funext i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right]
      fin_cases k <;> simp [outj_succ, pow_succ, Nat.mul_comm]
  have hn := (nudge_run (List.replicate d true) (outj out d (j + 1)) (frame (binary d (2 ^ (j + 1)))) j
    (outj out d (j + 1)).length 0).embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2 * d) false)
  exact hm.seq hn

theorem pass_forward (i : Fin 3) (hi : i ≠ 2) : NoLeft passM (i.castAdd 1) :=
  RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _
    (restore_other Emit.machine 2 i hi (Emit.forward i)) (embed_forward 1 nudge i (nudge_forward i))

theorem loop_forward (i : Fin 3) (hi : i ≠ 2) : NoLeft loopM (i.castAdd 1) :=
  stream_forward passM C4 (i.castAdd 1) (pass_forward i hi)

/-- The loop over the count tape's `d` cells. -/
def loop (d : ℕ) (out : List Bool) : Loop (3 + 1) (5 + 2 + 2) where
  body := passM
  tape := C4
  bound := d
  H := fun j => passH d j out
  A := fun j => passA d j out
  cost := passCost d
  step := fun j _ => pass_step d j out
  cont := fun j hj => by
    show readTapeBit (passA d j out C4) (passH d j out C4) = true
    rw [passA_C4, passH_C4, read_count]
    simpa using hj
  halt := by
    show readTapeBit (passA d d out C4) (passH d d out C4) = false
    rw [passA_C4, passH_C4, read_count]
    simp

def loopCost (d : ℕ) : ℕ := d * (passCost d + 2) + 1

theorem loop_step (d : ℕ) (out : List Bool) :
    Step loopM (loopCost d) (passH d 0 out) (passA d 0 out) (passH d d out) (passA d d out) :=
  (loop d out).run

/-- The loop, then the count head's paid return. -/
theorem loopR_step (d : ℕ) (out : List Bool) :
    Step loopR (2 * loopCost d + 2)
      (Fin.addCases (passH d 0 out) (fun _ : Fin 1 => 0))
      (Fin.addCases (passA d 0 out) (fun _ : Fin 1 => List.replicate d false))
      (Fin.addCases (Fin.addCases ![0, (out ++ word d).length, 0] (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0))
      (Fin.addCases (Fin.addCases ![List.replicate d true, out ++ word d, frame (binary d (2 ^ d))]
        (fun _ : Fin 1 => List.replicate (2 * d) false)) (fun _ : Fin 1 => List.replicate d false)) := by
  have h := restore_step C4 (loop_forward 0 (by decide)) (loop_step d out) d
    (by show d = 0 + d; omega) d (Or.inr rfl)
  refine h.congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-! ## The start and the end -/

def initCost (d : ℕ) : ℕ := 2 * (2 * (2 * d + 1) + 2) + 2

theorem init_step (d : ℕ) (out : List Bool) :
    Step initM (initCost d)
      (Fin.addCases (Fin.addCases ![0, out.length, 0] (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0))
      (Fin.addCases (Fin.addCases ![List.replicate d true, out, []] (fun _ : Fin 1 => ([] : List Bool)))
        (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases (passH d 0 out) (fun _ : Fin 1 => 0))
      (Fin.addCases (passA d 0 out) (fun _ : Fin 1 => List.replicate d false)) := by
  have h1 := restore_step (2 : Fin 3) (First.forward 2) (First.run d out.length out) (2 * d)
    (by show 2 * d = 0 + 2 * d; omega) 0 (Or.inl rfl)
  have h1' : Step (restore First.machine 2) (2 * (2 * d + 1) + 2)
      (Fin.addCases ![0, out.length, 0] (fun _ : Fin 1 => 0))
      (Fin.addCases ![List.replicate d true, out, []] (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases ![d, out.length, 0] (fun _ : Fin 1 => 0))
      (Fin.addCases ![List.replicate d true, out, frame (binary d 1)] (fun _ : Fin 1 => List.replicate (2 * d) false)) := by
    refine h1.congr ?_ rfl
    funext i; fin_cases i <;> rfl
  have h2 := restore_step C4 (restore_other First.machine 2 0 (by decide) (First.forward 0)) h1' d
    (by show d = 0 + d; omega) 0 (Or.inl rfl)
  rw [passH_zero, passA_zero]
  refine h2.congr ?_ rfl
  funext i; fin_cases i <;> rfl

def eraseCost (d : ℕ) : ℕ := 2 * (2 * d + 1) + 2

theorem erase_step (d : ℕ) (O : List Bool) :
    Step eraseM (eraseCost d)
      (Fin.addCases (Fin.addCases ![0, O.length, 0] (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0))
      (Fin.addCases (Fin.addCases ![List.replicate d true, O, frame (binary d (2 ^ d))]
        (fun _ : Fin 1 => List.replicate (2 * d) false)) (fun _ : Fin 1 => List.replicate d false))
      (Fin.addCases (Fin.addCases ![0, O.length, 0] (fun _ : Fin 1 => 0)) (fun _ : Fin 1 => 0))
      (Fin.addCases (Fin.addCases ![List.replicate d true, O, List.replicate (2 * d + 1) false]
        (fun _ : Fin 1 => List.replicate (2 * d) false)) (fun _ : Fin 1 => List.replicate d false)) := by
  have h := Erase.run (binary d (2 ^ d)) (List.replicate d true) O 0 O.length
  rw [binary_length] at h
  have h1 := restore_step (2 : Fin 3) (Erase.forward 2) h (2 * d) (by show 2 * d = 0 + 2 * d; omega)
    (2 * d) (Or.inr rfl)
  have h2 := h1.embed (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate d false)
  refine h2.congr ?_ rfl
  funext i; fin_cases i <;> rfl

/-! ## The writer -/

theorem cost_le (d : ℕ) : initCost d + 1 + (2 * loopCost d + 2) + 1 + eraseCost d ≤ budget d := by
  unfold initCost loopCost passCost eraseCost budget
  nlinarith

/-- **`write_run`.** From the count tape `List.replicate d true` (head 0), the output `out` (head at its
end) and three blank work tapes, the writer appends the identity columns `word d`. The count tape and its
head end as they started. The column tape and the two rewind logs end all-false with lengths `2d+1`,
`2d` and `d`, heads at cell 0. At most `budget d = 64 (d+1)²` steps. -/
theorem write_run (d : ℕ) (out : List Bool) :
    Step machine (budget d)
      ![0, out.length, 0, 0, 0]
      ![List.replicate d true, out, [], [], []]
      ![0, (out ++ word d).length, 0, 0, 0]
      ![List.replicate d true, out ++ word d, List.replicate (2 * d + 1) false,
        List.replicate (2 * d) false, List.replicate d false] := by
  have h := ((init_step d out).seq (loopR_step d out)).seq (erase_step d (out ++ word d))
  refine ((h.enlarge (cost_le d)).congr_in ?_ ?_).congr ?_ ?_
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- **The output head never moves left** (`CursorRestore.NoLeft`), for `AppendOutputFrame`. -/
theorem out_forward : RepairSource.ProjectionNormalization.CursorRestore.NoLeft machine 1 := by
  have h : NoLeft machine (((1 : Fin 3).castAdd 1).castAdd 1) :=
    RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _
      (RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _
        (restore_other _ C4 _ (by decide) (restore_other First.machine 2 1 (by decide) (First.forward 1)))
        (restore_other loopM C4 _ (by decide) (loop_forward 1 (by decide))))
      (embed_forward 1 (restore Erase.machine 2) _ (restore_other Erase.machine 2 1 (by decide) (Erase.forward 1)))
  exact h

end NearCubicWires.RepairOrdinary.EquationIdentityColumns
