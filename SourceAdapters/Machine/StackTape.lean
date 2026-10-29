import NineInputs
import Mathlib.Tactic

/-!
# One ordinary tape as two stacks

`app:short-pcp-proof`, "The exact Lean interface": "A fixed multitape implementation can be simulated by finitely many stacks in polynomial time". This
module is the per-tape half of that sentence: the ordinary one-sided tape of `LocalBitMultitape`
(`L/Statement.lean:322–458`; cells are a materialized `List Bool`, reads beyond it are `false`, writes beyond it pad
with `false`) is represented by two stacks of `Option Bool` cells.

* The left stack holds the cells left of the head, nearest first; its length is the head position.
* The right stack holds the scanned cell and the cells to its right.
* A `none` cell is a blank that was never materialized. `decode` drops trailing `none` cells and reads every
  other `none` as `false`. This is what makes a write far beyond the materialized end a constant-time operation:
  the gap stays `none` and decodes to the `false` padding of `writeTapeBit`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Machine

open NearCubicWires NearCubicWires.LocalBitMultitape

/-- One decoded cell in front of a decoded suffix: a blank `none` in front of nothing materialized vanishes. -/
def consCell : Option Bool → List Bool → List Bool
  | none, [] => []
  | none, b :: d => false :: b :: d
  | some v, d => v :: d

/-- The materialized tape denoted by a cell list. -/
def decode : List (Option Bool) → List Bool
  | [] => []
  | x :: xs => consCell x (decode xs)

@[simp] theorem decode_nil : decode [] = [] := rfl

@[simp] theorem decode_cons (x : Option Bool) (xs : List (Option Bool)) :
    decode (x :: xs) = consCell x (decode xs) := rfl

@[simp] theorem consCell_some (v : Bool) (d : List Bool) : consCell (some v) d = v :: d := rfl

theorem decode_map_some (l : List Bool) : decode (l.map some) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem decode_append_none (l : List (Option Bool)) : decode (l ++ [none]) = decode l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Reading a decoded tape. -/
theorem getD_decode (l : List (Option Bool)) (i : ℕ) :
    (decode l).getD i false = (l.getD i none).getD false := by
  simp only [List.getD_eq_getElem?_getD]
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    rw [decode_cons]
    rcases x with _ | v
    · rcases hd : decode xs with _ | ⟨b, d⟩
      · cases i with
        | zero => simp [consCell]
        | succ j => have := ih j; rw [hd] at this; simpa [consCell] using this
      · cases i with
        | zero => simp [consCell]
        | succ j => have := ih j; rw [hd] at this; simpa [consCell] using this
    · cases i with
      | zero => simp
      | succ j => simpa using ih j

/-- The bit under the head: the top of the right stack. -/
def topBit : List (Option Bool) → Bool
  | [] => false
  | x :: _ => x.getD false

theorem readTapeBit_decode (L R : List (Option Bool)) :
    readTapeBit (decode (L.reverse ++ R)) L.length = topBit R := by
  unfold readTapeBit
  rw [getD_decode]
  have : (L.reverse ++ R).getD L.length none = R.getD 0 none := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp
  rw [this]
  cases R <;> simp [topBit]

theorem writeTapeBit_ne_nil (t : List Bool) (n : ℕ) (v : Bool) : writeTapeBit t n v ≠ [] := by
  cases t <;> cases n <;> simp [writeTapeBit]

/-- The write of one cell, on the right stack. -/
def writeCells : Option Bool → List (Option Bool) → List (Option Bool)
  | none, R => R
  | some v, R => some v :: R.tail

theorem writeTapeBit_decode (A R : List (Option Bool)) (v : Bool) :
    writeTapeBit (decode (A ++ R)) A.length v = decode (A ++ some v :: R.tail) := by
  induction A with
  | nil =>
    rcases R with _ | ⟨x, R'⟩
    · simp [writeTapeBit]
    · simp only [List.nil_append, decode_cons, List.length_nil, List.tail_cons, consCell_some]
      rcases x with _ | u
      · rcases hd : decode R' with _ | ⟨b, d⟩ <;> simp [consCell, writeTapeBit]
      · simp [writeTapeBit]
  | cons a A ih =>
    simp only [List.cons_append, decode_cons, List.length_cons]
    rw [← ih]
    rcases a with _ | u
    · rcases hd : decode (A ++ R) with _ | ⟨b, d⟩
      · rcases hw : writeTapeBit [] A.length v with _ | ⟨c, e⟩
        · exact absurd hw (writeTapeBit_ne_nil _ _ _)
        · simp [consCell, writeTapeBit, hw]
      · rcases hw : writeTapeBit (b :: d) A.length v with _ | ⟨c, e⟩
        · exact absurd hw (writeTapeBit_ne_nil _ _ _)
        · simp [consCell, writeTapeBit, hw]
    · simp [writeTapeBit]

/-- A head move, on the pair (left stack, right stack). -/
def moveCells : HeadMove → List (Option Bool) × List (Option Bool) → List (Option Bool) × List (Option Bool)
  | .left, ([], R) => ([], R)
  | .left, (x :: L, R) => (L, x :: R)
  | .stay, p => p
  | .right, (L, []) => (none :: L, [])
  | .right, (L, x :: R) => (x :: L, R)

/-- The whole per-tape update of one ordinary step: write, then move. -/
def tapeUpdate (w : Option Bool) (m : HeadMove) (p : List (Option Bool) × List (Option Bool)) :
    List (Option Bool) × List (Option Bool) :=
  moveCells m (p.1, writeCells w p.2)

/-- The representation of one tape with its head. -/
def TapeRep (p : List (Option Bool) × List (Option Bool)) (t : List Bool) (h : ℕ) : Prop :=
  decode (p.1.reverse ++ p.2) = t ∧ p.1.length = h

theorem tapeRep_move (m : HeadMove) (p : List (Option Bool) × List (Option Bool)) (t : List Bool) (h : ℕ)
    (hp : TapeRep p t h) : TapeRep (moveCells m p) t (m.apply h) := by
  obtain ⟨L, R⟩ := p
  obtain ⟨hd, hl⟩ := hp
  simp only at hd hl
  subst hl
  cases m with
  | left =>
    rcases L with _ | ⟨x, L⟩
    · exact ⟨hd, rfl⟩
    · refine ⟨?_, ?_⟩
      · simpa [moveCells] using hd
      · simp [moveCells, HeadMove.apply]
  | stay => exact ⟨hd, rfl⟩
  | right =>
    rcases R with _ | ⟨x, R⟩
    · refine ⟨?_, ?_⟩
      · simp only [moveCells, List.reverse_cons, List.append_nil]
        rw [decode_append_none]; simpa using hd
      · simp [moveCells, HeadMove.apply]
    · refine ⟨?_, ?_⟩
      · simpa [moveCells] using hd
      · simp [moveCells, HeadMove.apply]

theorem tapeRep_update (w : Option Bool) (m : HeadMove) (p : List (Option Bool) × List (Option Bool))
    (t : List Bool) (h : ℕ) (hp : TapeRep p t h) :
    TapeRep (tapeUpdate w m p) (match w with
      | none => t
      | some v => writeTapeBit t h v) (m.apply h) := by
  unfold tapeUpdate
  apply tapeRep_move
  obtain ⟨L, R⟩ := p
  obtain ⟨hd, hl⟩ := hp
  simp only at hd hl
  cases w with
  | none => exact ⟨hd, hl⟩
  | some v =>
    refine ⟨?_, hl⟩
    simp only [writeCells]
    rw [← hd, ← hl, ← List.length_reverse, writeTapeBit_decode]

theorem tapeUpdate_size (w : Option Bool) (m : HeadMove) (p : List (Option Bool) × List (Option Bool)) :
    (tapeUpdate w m p).1.length + (tapeUpdate w m p).2.length ≤ p.1.length + p.2.length + 2 := by
  obtain ⟨L, R⟩ := p
  have hw : (writeCells w R).length ≤ R.length + 1 := by
    cases w <;> simp [writeCells]
  unfold tapeUpdate
  generalize writeCells w R = R' at hw
  cases m <;> rcases L with _ | ⟨x, L⟩ <;> rcases R' with _ | ⟨y, R'⟩ <;>
    simp [moveCells] at hw ⊢ <;> omega

/-! ## Emitting a decoded tape onto a stack -/

theorem foldl_consCell_reverse (l : List (Option Bool)) :
    (l.reverse.foldl (fun d c => consCell c d) []) = decode l := by
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

end NearCubicGates.Adapters.Machine
