import Proof.Packets.PacketsScan
import Proof.MachineModel.OrdinaryWilliamsInputHeader
import Proof.MachineModel.Runs

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsGlue.NatSum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue

/-! ## The machine -/

def nw : Fin 5 → Option Bool := fun _ => none

def act (q : Fin 21) (w : Fin 5 → Option Bool) (m : Fin 5 → HeadMove) : Option (Action 5 21) :=
  some ⟨q, w, m⟩

def machine : Machine 5 21 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 20
  rule := fun q b =>
    if q.val = 0 then act 1 nw ![.right, .stay, .stay, .stay, .stay]
    else if q.val = 1 then (if b 0 then act 0 ![none, none, none, none, some true] ![.right, .stay, .stay, .stay, .right]
      else act 2 nw ![.right, .stay, .stay, .stay, .left])
    else if q.val = 2 then (if b 4 then act 3 ![none, none, none, none, some false] ![.right, .stay, .stay, .stay, .left]
      else act 5 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 3 then act 2 nw ![.right, .stay, .stay, .stay, .stay]
    else if q.val = 5 then (if b 0 then act 6 nw ![.right, .stay, .stay, .stay, .stay]
      else act 20 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 6 then (if b 0 then act 7 ![none, none, none, none, some true] ![.right, .stay, .stay, .stay, .right]
      else act 9 nw ![.right, .stay, .right, .stay, .left])
    else if q.val = 7 then act 6 nw ![.right, .stay, .stay, .stay, .stay]
    else if q.val = 9 then act 10 ![none, none, some true, none, none] ![.stay, .stay, .stay, .stay, .stay]
    else if q.val = 10 then (if b 4 then act 11 ![none, none, none, none, some false] ![.right, .stay, .stay, .stay, .left]
      else act 18 nw ![.stay, .stay, .stay, .stay, .stay])
    else if q.val = 11 then (if b 0 then act 12 nw ![.right, .stay, .stay, .stay, .stay]
      else act 14 nw ![.right, .stay, .stay, .stay, .stay])
    else if q.val = 12 then (if b 2 then act 12 ![none, some true, none, none, none] ![.stay, .right, .right, .stay, .stay]
      else act 13 nw ![.stay, .stay, .left, .stay, .stay])
    else if q.val = 13 then (if b 2 then act 13 nw ![.stay, .stay, .left, .stay, .stay]
      else act 14 nw ![.stay, .stay, .right, .stay, .stay])
    else if q.val = 14 then act 15 ![none, none, none, some false, none] ![.stay, .stay, .stay, .right, .stay]
    else if q.val = 15 then (if b 2 then act 15 ![none, none, none, some true, none] ![.stay, .stay, .right, .right, .stay]
      else act 16 nw ![.stay, .stay, .stay, .left, .stay])
    else if q.val = 16 then (if b 3 then act 16 ![none, none, some true, some false, none] ![.stay, .stay, .right, .left, .stay]
      else act 17 nw ![.stay, .stay, .left, .stay, .stay])
    else if q.val = 17 then (if b 2 then act 17 nw ![.stay, .stay, .left, .stay, .stay]
      else act 10 nw ![.stay, .stay, .right, .stay, .stay])
    else if q.val = 18 then (if b 2 then act 18 nw ![.stay, .stay, .right, .stay, .stay]
      else act 19 nw ![.stay, .stay, .left, .stay, .stay])
    else if q.val = 19 then (if b 2 then act 19 ![none, none, some false, none, none] ![.stay, .stay, .left, .stay, .stay]
      else act 5 nw ![.stay, .stay, .stay, .stay, .stay])
    else none

/-- Tapes: source, accumulator `1^o` (head at its end), weight, copy, marks. -/
def cfg (q : Fin 21) (src : List Bool) (sh o : ℕ) (W : List Bool) (wh : ℕ) (W2 : List Bool) (w2h : ℕ)
    (L : List Bool) (lh : ℕ) : Configuration 5 21 :=
  ⟨q, ![sh, o, wh, w2h, lh], ![src, List.replicate o true, W, W2, L]⟩

/-! ## Tape shapes -/

/-- `m` marks then `k` blanks. -/
def marks (m k : ℕ) : List Bool := List.replicate m true ++ List.replicate k false
/-- A sentinel blank, `m` ones, then `k` blanks. -/
def sent (m k : ℕ) : List Bool := false :: (List.replicate m true ++ List.replicate k false)

theorem read_marks (m k i : ℕ) : readTapeBit (marks m k) i = decide (i < m) := by
  unfold marks readTapeBit
  by_cases h : i < m
  · have hl : i < (List.replicate m true).length := by simpa using h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    simp [h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp [h]

theorem read_sent (m k i : ℕ) : readTapeBit (sent m k) i = decide (1 ≤ i ∧ i ≤ m) := by
  cases i with
  | zero => rfl
  | succ i =>
    have h := read_marks m k i
    unfold marks at h
    unfold sent readTapeBit
    simp only [List.getD_cons_succ]
    unfold readTapeBit at h
    rw [h]
    simp

theorem read_blank (k i : ℕ) : readTapeBit (List.replicate k false) i = false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < k
  · simp [h]
  · simp [h]

theorem write_tail (l : List Bool) (k : ℕ) (b : Bool) :
    writeTapeBit (l ++ List.replicate k false) l.length b = l ++ b :: List.replicate (k - 1) false := by
  induction l with
  | nil =>
    cases k with
    | zero => rfl
    | succ k => simp [writeTapeBit, List.replicate_succ]
  | cons x l ih => simp [writeTapeBit, ih]

theorem write_mid (l : List Bool) (c : Bool) (k : ℕ) (b : Bool) :
    writeTapeBit (l ++ c :: List.replicate k false) l.length b = l ++ b :: List.replicate k false := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [writeTapeBit, ih]

theorem marks_mark (m k : ℕ) : writeTapeBit (marks m k) m true = marks (m+1) (k-1) := by
  have h := write_tail (List.replicate m true) k true
  simp only [List.length_replicate] at h
  unfold marks
  rw [h, List.replicate_succ', List.append_assoc]
  rfl

theorem marks_erase (m k : ℕ) : writeTapeBit (marks (m+1) k) m false = marks m (k+1) := by
  have h := write_mid (List.replicate m true) true k false
  simp only [List.length_replicate] at h
  unfold marks
  rw [List.replicate_succ', List.append_assoc]
  rw [show List.replicate m true ++ ([true] ++ List.replicate k false) =
    List.replicate m true ++ true :: List.replicate k false from rfl, h]
  rfl

theorem sent_add (m k : ℕ) : writeTapeBit (sent m k) (m+1) true = sent (m+1) (k-1) := by
  have h := marks_mark m k
  unfold sent
  unfold marks at h
  simp only [writeTapeBit, h]

theorem sent_erase (m k : ℕ) : writeTapeBit (sent (m+1) k) (m+1) false = sent m (k+1) := by
  have h := marks_erase m k
  unfold sent
  unfold marks at h
  simp only [writeTapeBit, h]

theorem blank_first (k : ℕ) : writeTapeBit (List.replicate k false) 1 true = sent 1 (k-2) := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · simp [writeTapeBit, sent, List.replicate_succ]

theorem sent_zero (k : ℕ) : sent 0 k = List.replicate (k+1) false := by
  simp [sent, List.replicate_succ]

/-! ## The source: a frame read two cells per logical bit -/

theorem read_marker (u : List Bool) (i : ℕ) (h : i < u.length) :
    readTapeBit (frame u) (2 * i) = true := by
  induction u generalizing i with
  | nil => simp at h
  | cons b u ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < u.length := by simpa using h
      rw [frame_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      exact ih i h'

theorem read_payload (u : List Bool) (i : ℕ) (h : i < u.length) :
    readTapeBit (frame u) (2 * i + 1) = u[i] := by
  induction u generalizing i with
  | nil => simp at h
  | cons b u ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have h' : i < u.length := by simpa using h
      rw [frame_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega]
      exact ih i h'

theorem read_end (u : List Bool) : readTapeBit (frame u) (2 * u.length) = false := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    rw [frame_cons, List.length_cons, show 2 * (u.length + 1) = 2 * u.length + 1 + 1 by omega]
    exact ih

theorem blank_zero (k : ℕ) : writeTapeBit (List.replicate k false) 0 false = sent 0 (k-1) := by
  rcases k with _ | k
  · rfl
  · simp [writeTapeBit, sent, List.replicate_succ]

/-! ## One transition each -/

section Steps
variable (src : List Bool) (sh o : ℕ) (W : List Bool) (wh : ℕ) (W2 : List Bool) (w2h : ℕ)
  (L : List Bool) (lh : ℕ)

theorem s0 : step machine (cfg 0 src sh o W wh W2 w2h L lh) =
    some (cfg 1 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s1t (h : readTapeBit src sh = true) : step machine (cfg 1 src sh o W wh W2 w2h L lh) =
    some (cfg 0 src (sh+1) o W wh W2 w2h (writeTapeBit L lh true) (lh+1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s1f (h : readTapeBit src sh = false) : step machine (cfg 1 src sh o W wh W2 w2h L lh) =
    some (cfg 2 src (sh+1) o W wh W2 w2h L (lh-1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s2t (h : readTapeBit L lh = true) : step machine (cfg 2 src sh o W wh W2 w2h L lh) =
    some (cfg 3 src (sh+1) o W wh W2 w2h (writeTapeBit L lh false) (lh-1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s2f (h : readTapeBit L lh = false) : step machine (cfg 2 src sh o W wh W2 w2h L lh) =
    some (cfg 5 src sh o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s3 : step machine (cfg 3 src sh o W wh W2 w2h L lh) =
    some (cfg 2 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5t (h : readTapeBit src sh = true) : step machine (cfg 5 src sh o W wh W2 w2h L lh) =
    some (cfg 6 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s5f (h : readTapeBit src sh = false) : step machine (cfg 5 src sh o W wh W2 w2h L lh) =
    some (cfg 20 src sh o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s6t (h : readTapeBit src sh = true) : step machine (cfg 6 src sh o W wh W2 w2h L lh) =
    some (cfg 7 src (sh+1) o W wh W2 w2h (writeTapeBit L lh true) (lh+1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s6f (h : readTapeBit src sh = false) : step machine (cfg 6 src sh o W wh W2 w2h L lh) =
    some (cfg 9 src (sh+1) o W (wh+1) W2 w2h L (lh-1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s7 : step machine (cfg 7 src sh o W wh W2 w2h L lh) =
    some (cfg 6 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s9 : step machine (cfg 9 src sh o W wh W2 w2h L lh) =
    some (cfg 10 src sh o (writeTapeBit W wh true) wh W2 w2h L lh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s10t (h : readTapeBit L lh = true) : step machine (cfg 10 src sh o W wh W2 w2h L lh) =
    some (cfg 11 src (sh+1) o W wh W2 w2h (writeTapeBit L lh false) (lh-1)) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s10f (h : readTapeBit L lh = false) : step machine (cfg 10 src sh o W wh W2 w2h L lh) =
    some (cfg 18 src sh o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s11t (h : readTapeBit src sh = true) : step machine (cfg 11 src sh o W wh W2 w2h L lh) =
    some (cfg 12 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s11f (h : readTapeBit src sh = false) : step machine (cfg 11 src sh o W wh W2 w2h L lh) =
    some (cfg 14 src (sh+1) o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s12t (h : readTapeBit W wh = true) : step machine (cfg 12 src sh o W wh W2 w2h L lh) =
    some (cfg 12 src sh (o+1) W (wh+1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, write_end_replicate]

theorem s12f (h : readTapeBit W wh = false) : step machine (cfg 12 src sh o W wh W2 w2h L lh) =
    some (cfg 13 src sh o W (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s13t (h : readTapeBit W wh = true) : step machine (cfg 13 src sh o W wh W2 w2h L lh) =
    some (cfg 13 src sh o W (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s13f (h : readTapeBit W wh = false) : step machine (cfg 13 src sh o W wh W2 w2h L lh) =
    some (cfg 14 src sh o W (wh+1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s14 : step machine (cfg 14 src sh o W wh W2 w2h L lh) =
    some (cfg 15 src sh o W wh (writeTapeBit W2 w2h false) (w2h+1) L lh) := by
  simp [step, machine, cfg, act]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s15t (h : readTapeBit W wh = true) : step machine (cfg 15 src sh o W wh W2 w2h L lh) =
    some (cfg 15 src sh o W (wh+1) (writeTapeBit W2 w2h true) (w2h+1) L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s15f (h : readTapeBit W wh = false) : step machine (cfg 15 src sh o W wh W2 w2h L lh) =
    some (cfg 16 src sh o W wh W2 (w2h-1) L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s16t (h : readTapeBit W2 w2h = true) : step machine (cfg 16 src sh o W wh W2 w2h L lh) =
    some (cfg 16 src sh o (writeTapeBit W wh true) (wh+1) (writeTapeBit W2 w2h false) (w2h-1) L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s16f (h : readTapeBit W2 w2h = false) : step machine (cfg 16 src sh o W wh W2 w2h L lh) =
    some (cfg 17 src sh o W (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s17t (h : readTapeBit W wh = true) : step machine (cfg 17 src sh o W wh W2 w2h L lh) =
    some (cfg 17 src sh o W (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s17f (h : readTapeBit W wh = false) : step machine (cfg 17 src sh o W wh W2 w2h L lh) =
    some (cfg 10 src sh o W (wh+1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s18t (h : readTapeBit W wh = true) : step machine (cfg 18 src sh o W wh W2 w2h L lh) =
    some (cfg 18 src sh o W (wh+1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s18f (h : readTapeBit W wh = false) : step machine (cfg 18 src sh o W wh W2 w2h L lh) =
    some (cfg 19 src sh o W (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

theorem s19t (h : readTapeBit W wh = true) : step machine (cfg 19 src sh o W wh W2 w2h L lh) =
    some (cfg 19 src sh o (writeTapeBit W wh false) (wh-1) W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem s19f (h : readTapeBit W wh = false) : step machine (cfg 19 src sh o W wh W2 w2h L lh) =
    some (cfg 5 src sh o W wh W2 w2h L lh) := by
  simp [step, machine, cfg, act, Configuration.scanned, h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, nw]

end Steps

/-! ## The loops -/

theorem timed_congr {n n' : ℕ} {c c' d d' : Configuration 5 21} (h : Timed machine n c d)
    (hn : n = n') (hc : c = c') (hd : d = d') : Timed machine n' c' d' := by
  subst hn hc hd
  exact h

section Loops
variable (u : List Bool)

theorem head_ones (o : ℕ) (W : List Bool) (wh : ℕ) (W2 : List Bool) (w2h : ℕ) :
    ∀ r i m k : ℕ, (∀ j, j < r → ∃ h : i + j < u.length, u[i + j] = true) →
    Timed machine (2 * r) (cfg 0 (frame u) (2 * i) o W wh W2 w2h (marks m k) m)
      (cfg 0 (frame u) (2 * (i + r)) o W wh W2 w2h (marks (m + r) (k - r)) (m + r)) := by
  intro r
  induction r with
  | zero => intro i m k _; simpa using Timed.refl machine (cfg 0 (frame u) (2 * i) o W wh W2 w2h (marks m k) m)
  | succ r ih =>
    intro i m k hr
    obtain ⟨hlt, hv⟩ := hr 0 (by omega)
    simp only [Nat.add_zero] at hlt hv
    have h1 : readTapeBit (frame u) (2 * i + 1) = true := by rw [read_payload u i hlt, hv]
    have t1 := Timed.single (p := machine) (by rfl) (s0 (frame u) (2 * i) o W wh W2 w2h (marks m k) m)
    have t2 := Timed.single (p := machine) (by rfl)
      (s1t (frame u) (2 * i + 1) o W wh W2 w2h (marks m k) m h1)
    rw [marks_mark] at t2
    have t3 := ih (i + 1) (m + 1) (k - 1) (fun j hj => by
      obtain ⟨h, e⟩ := hr (j + 1) (by omega)
      exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using e⟩)
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] at t2
    have tt := (t1.trans t2).trans t3
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem head_skip (o : ℕ) (W : List Bool) (wh : ℕ) (W2 : List Bool) (w2h : ℕ) :
    ∀ r i k : ℕ, Timed machine (2 * r + 1) (cfg 2 (frame u) (2 * i) o W wh W2 w2h (marks r k) (r - 1))
      (cfg 5 (frame u) (2 * (i + r)) o W wh W2 w2h (marks 0 (k + r)) 0) := by
  intro r
  induction r with
  | zero =>
    intro i k
    have h : readTapeBit (marks 0 k) (0 - 1) = false := by rw [read_marks]; simp
    simpa using Timed.single (p := machine) (by rfl) (s2f (frame u) (2 * i) o W wh W2 w2h (marks 0 k) (0 - 1) h)
  | succ r ih =>
    intro i k
    have h : readTapeBit (marks (r + 1) k) (r + 1 - 1) = true := by rw [read_marks]; simp
    have t1 := Timed.single (p := machine) (by rfl) (s2t (frame u) (2 * i) o W wh W2 w2h (marks (r + 1) k) (r + 1 - 1) h)
    rw [show r + 1 - 1 = r by omega, marks_erase] at t1
    have t2 := Timed.single (p := machine) (by rfl) (s3 (frame u) (2 * i + 1) o W wh W2 w2h (marks r (k + 1)) (r - 1))
    have t3 := ih (i + 1) (k + 1)
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] at t2
    have tt := (t1.trans t2).trans t3
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem item_ones (o : ℕ) (W : List Bool) (wh : ℕ) (W2 : List Bool) (w2h : ℕ) :
    ∀ r i m k : ℕ, (∀ j, j < r → ∃ h : i + j < u.length, u[i + j] = true) →
    Timed machine (2 * r) (cfg 6 (frame u) (2 * i + 1) o W wh W2 w2h (marks m k) m)
      (cfg 6 (frame u) (2 * (i + r) + 1) o W wh W2 w2h (marks (m + r) (k - r)) (m + r)) := by
  intro r
  induction r with
  | zero => intro i m k _; simpa using Timed.refl machine (cfg 6 (frame u) (2 * i + 1) o W wh W2 w2h (marks m k) m)
  | succ r ih =>
    intro i m k hr
    obtain ⟨hlt, hv⟩ := hr 0 (by omega)
    simp only [Nat.add_zero] at hlt hv
    have h1 : readTapeBit (frame u) (2 * i + 1) = true := by rw [read_payload u i hlt, hv]
    have t1 := Timed.single (p := machine) (by rfl) (s6t (frame u) (2 * i + 1) o W wh W2 w2h (marks m k) m h1)
    rw [marks_mark] at t1
    have t2 := Timed.single (p := machine) (by rfl) (s7 (frame u) (2 * i + 1 + 1) o W wh W2 w2h (marks (m + 1) (k - 1)) (m + 1))
    have t3 := ih (i + 1) (m + 1) (k - 1) (fun j hj => by
      obtain ⟨h, e⟩ := hr (j + 1) (by omega)
      exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using e⟩)
    rw [show 2 * i + 1 + 1 + 1 = 2 * (i + 1) + 1 by omega] at t2
    have tt := (t1.trans t2).trans t3
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

end Loops

section WLoops
variable (src : List Bool) (sh : ℕ) (L : List Bool) (lh : ℕ)

theorem add_loop (W2 : List Bool) (w2h w g : ℕ) : ∀ j t o : ℕ, t + j ≤ w →
    Timed machine j (cfg 12 src sh o (sent w g) (1 + t) W2 w2h L lh)
      (cfg 12 src sh (o + j) (sent w g) (1 + t + j) W2 w2h L lh) := by
  intro j
  induction j with
  | zero => intro t o _; simpa using Timed.refl machine (cfg 12 src sh o (sent w g) (1 + t) W2 w2h L lh)
  | succ j ih =>
    intro t o hj
    have h : readTapeBit (sent w g) (1 + t) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s12t src sh o (sent w g) (1 + t) W2 w2h L lh h)
    have t2 := ih (t + 1) (o + 1) (by omega)
    rw [show 1 + (t + 1) = 1 + t + 1 by omega] at t2
    have tt := t1.trans t2
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem rewind13 (o : ℕ) (W2 : List Bool) (w2h w g : ℕ) : ∀ p : ℕ, p ≤ w →
    Timed machine (p + 1) (cfg 13 src sh o (sent w g) p W2 w2h L lh)
      (cfg 14 src sh o (sent w g) 1 W2 w2h L lh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sent w g) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s13f src sh o (sent w g) 0 W2 w2h L lh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sent w g) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s13t src sh o (sent w g) (p + 1) W2 w2h L lh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem rewind17 (o : ℕ) (W2 : List Bool) (w2h w g : ℕ) : ∀ p : ℕ, p ≤ w →
    Timed machine (p + 1) (cfg 17 src sh o (sent w g) p W2 w2h L lh)
      (cfg 10 src sh o (sent w g) 1 W2 w2h L lh) := by
  intro p
  induction p with
  | zero =>
    intro _
    have h : readTapeBit (sent w g) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s17f src sh o (sent w g) 0 W2 w2h L lh h)
  | succ p ih =>
    intro hp
    have h : readTapeBit (sent w g) (p + 1) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s17t src sh o (sent w g) (p + 1) W2 w2h L lh h)
    rw [show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (by omega))
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem copy_loop (o w gw : ℕ) : ∀ j t g2 : ℕ, t + j ≤ w →
    Timed machine j (cfg 15 src sh o (sent w gw) (1 + t) (sent t g2) (1 + t) L lh)
      (cfg 15 src sh o (sent w gw) (1 + t + j) (sent (t + j) (g2 - j)) (1 + t + j) L lh) := by
  intro j
  induction j with
  | zero => intro t g2 _; simpa using Timed.refl machine (cfg 15 src sh o (sent w gw) (1 + t) (sent t g2) (1 + t) L lh)
  | succ j ih =>
    intro t g2 hj
    have h : readTapeBit (sent w gw) (1 + t) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s15t src sh o (sent w gw) (1 + t) (sent t g2) (1 + t) L lh h)
    rw [show 1 + t = t + 1 by omega, sent_add] at t1
    have t2 := ih (t + 1) (g2 - 1) (by omega)
    rw [show 1 + (t + 1) = t + 1 + 1 by omega] at t2
    have tt := t1.trans t2
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem append_loop (o : ℕ) : ∀ b a gw g2 : ℕ,
    Timed machine b (cfg 16 src sh o (sent a gw) (a + 1) (sent b g2) b L lh)
      (cfg 16 src sh o (sent (a + b) (gw - b)) (a + b + 1) (sent 0 (g2 + b)) 0 L lh) := by
  intro b
  induction b with
  | zero => intro a gw g2; simpa using Timed.refl machine (cfg 16 src sh o (sent a gw) (a + 1) (sent 0 g2) 0 L lh)
  | succ b ih =>
    intro a gw g2
    have h : readTapeBit (sent (b + 1) g2) (b + 1) = true := by rw [read_sent]; simp
    have t1 := Timed.single (p := machine) (by rfl)
      (s16t src sh o (sent a gw) (a + 1) (sent (b + 1) g2) (b + 1) L lh h)
    rw [sent_add, sent_erase, show b + 1 - 1 = b by omega] at t1
    have t2 := ih (a + 1) (gw - 1) (g2 + 1)
    have tt := t1.trans t2
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem walk18 (o : ℕ) (W2 : List Bool) (w2h w g : ℕ) : ∀ j t : ℕ, t + j ≤ w →
    Timed machine j (cfg 18 src sh o (sent w g) (1 + t) W2 w2h L lh)
      (cfg 18 src sh o (sent w g) (1 + t + j) W2 w2h L lh) := by
  intro j
  induction j with
  | zero => intro t _; simpa using Timed.refl machine (cfg 18 src sh o (sent w g) (1 + t) W2 w2h L lh)
  | succ j ih =>
    intro t hj
    have h : readTapeBit (sent w g) (1 + t) = true := by rw [read_sent]; simp; omega
    have t1 := Timed.single (p := machine) (by rfl) (s18t src sh o (sent w g) (1 + t) W2 w2h L lh h)
    have t2 := ih (t + 1) (by omega)
    rw [show 1 + (t + 1) = 1 + t + 1 by omega] at t2
    have tt := t1.trans t2
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

theorem erase19 (o : ℕ) (W2 : List Bool) (w2h : ℕ) : ∀ p g : ℕ,
    Timed machine (p + 1) (cfg 19 src sh o (sent p g) p W2 w2h L lh)
      (cfg 5 src sh o (sent 0 (g + p)) 0 W2 w2h L lh) := by
  intro p
  induction p with
  | zero =>
    intro g
    have h : readTapeBit (sent 0 g) 0 = false := rfl
    simpa using Timed.single (p := machine) (by rfl) (s19f src sh o (sent 0 g) 0 W2 w2h L lh h)
  | succ p ih =>
    intro g
    have h : readTapeBit (sent (p + 1) g) (p + 1) = true := by rw [read_sent]; simp
    have t1 := Timed.single (p := machine) (by rfl) (s19t src sh o (sent (p + 1) g) (p + 1) W2 w2h L lh h)
    rw [sent_erase, show p + 1 - 1 = p by omega] at t1
    have tt := t1.trans (ih (g + 1))
    exact timed_congr tt (by omega) (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))
      (by congr 1 <;> first | rfl | omega | (congr 1 <;> omega))

end WLoops

/-! ## One bit, then all bits -/

theorem tr {n m : ℕ} {c d d' e : Configuration 5 21} (h1 : Timed machine n c d) (h2 : Timed machine m d' e)
    (h : d = d') : Timed machine (n + m) c e := by
  subst h
  exact h1.trans h2

macro "cfg_eq" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (congr 1 <;> omega)))

theorem bit_step (u : List Bool) (i : ℕ) (hi : i < u.length) (o w gw k2 r kL : ℕ) :
    ∃ k2' : ℕ, Timed machine (4 * w + 6 + (if u[i] then 2 * w + 2 else 0))
      (cfg 10 (frame u) (2 * i) o (sent w gw) 1 (List.replicate k2 false) 0 (marks (r + 1) kL) r)
      (cfg 10 (frame u) (2 * (i + 1)) (o + (u[i]).toNat * w) (sent (2 * w) (gw - w)) 1
        (List.replicate k2' false) 0 (marks r (kL + 1)) (r - 1)) := by
  set src := frame u
  have h10 : readTapeBit (marks (r + 1) kL) r = true := by rw [read_marks]; simp
  have t1 := Timed.single (p := machine) (by rfl)
    (s10t src (2 * i) o (sent w gw) 1 (List.replicate k2 false) 0 (marks (r + 1) kL) r h10)
  rw [marks_erase] at t1
  have hp : readTapeBit src (2 * i + 1) = u[i] := read_payload u i hi
  -- the doubling phase, from state 14
  have dbl : ∀ o' : ℕ, Timed machine (1 + w + 1 + w + 1 + (w + w + 1))
      (cfg 14 src (2 * i + 1 + 1) o' (sent w gw) 1 (List.replicate k2 false) 0 (marks r (kL + 1)) (r - 1))
      (cfg 10 src (2 * i + 1 + 1) o' (sent (w + w) (gw - w)) 1 (List.replicate (k2 - 1 - w + w + 1) false) 0
        (marks r (kL + 1)) (r - 1)) := by
    intro o'
    have d0 := Timed.single (p := machine) (by rfl)
      (s14 src (2 * i + 1 + 1) o' (sent w gw) 1 (List.replicate k2 false) 0 (marks r (kL + 1)) (r - 1))
    rw [blank_zero] at d0
    have d1 := copy_loop src (2 * i + 1 + 1) (marks r (kL + 1)) (r - 1) o' w gw w 0 (k2 - 1) (by omega)
    have hf1 : readTapeBit (sent w gw) (1 + 0 + w) = false := by rw [read_sent]; simp
    have d2 := Timed.single (p := machine) (by rfl)
      (s15f src (2 * i + 1 + 1) o' (sent w gw) (1 + 0 + w) (sent (0 + w) (k2 - 1 - w)) (1 + 0 + w)
        (marks r (kL + 1)) (r - 1) hf1)
    have d3 := append_loop src (2 * i + 1 + 1) (marks r (kL + 1)) (r - 1) o' w w gw (k2 - 1 - w)
    have hf2 : readTapeBit (sent 0 (k2 - 1 - w + w)) 0 = false := rfl
    have d4 := Timed.single (p := machine) (by rfl)
      (s16f src (2 * i + 1 + 1) o' (sent (w + w) (gw - w)) (w + w + 1) (sent 0 (k2 - 1 - w + w)) 0
        (marks r (kL + 1)) (r - 1) hf2)
    have d5 := rewind17 src (2 * i + 1 + 1) (marks r (kL + 1)) (r - 1) o' (sent 0 (k2 - 1 - w + w)) 0
      (w + w) (gw - w) (w + w) (le_refl _)
    have e1 := tr d0 d1 (by cfg_eq)
    have e2 := tr e1 d2 (by cfg_eq)
    have e3 := tr e2 d3 (by cfg_eq)
    have e4 := tr e3 d4 (by cfg_eq)
    have e5 := tr e4 d5 (by cfg_eq)
    rw [sent_zero] at e5
    exact e5
  by_cases hb : u[i] = true
  · have t2 := Timed.single (p := machine) (by rfl)
      (s11t src (2 * i + 1) o (sent w gw) 1 (List.replicate k2 false) 0 (marks r (kL + 1)) (r - 1)
        (by rw [hp, hb]))
    have t3 := add_loop src (2 * i + 1 + 1) (marks r (kL + 1)) (r - 1) (List.replicate k2 false) 0 w gw w 0 o
      (by omega)
    have hf : readTapeBit (sent w gw) (1 + 0 + w) = false := by rw [read_sent]; simp
    have t4 := Timed.single (p := machine) (by rfl)
      (s12f src (2 * i + 1 + 1) (o + w) (sent w gw) (1 + 0 + w) (List.replicate k2 false) 0
        (marks r (kL + 1)) (r - 1) hf)
    have t5 := rewind13 src (2 * i + 1 + 1) (marks r (kL + 1)) (r - 1) (o + w) (List.replicate k2 false) 0
      w gw w (le_refl _)
    have e1 := tr t1 t2 (by cfg_eq)
    have e2 := tr e1 t3 (by cfg_eq)
    have e3 := tr e2 t4 (by cfg_eq)
    have e4 := tr e3 t5 (by cfg_eq)
    have e5 := tr e4 (dbl (o + w)) (by cfg_eq)
    refine ⟨k2 - 1 - w + w + 1, timed_congr e5 (by simp [hb]; omega) rfl ?_⟩
    simp only [hb, Bool.toNat_true, one_mul]
    cfg_eq
  · have hb' : u[i] = false := by simpa using hb
    have t2 := Timed.single (p := machine) (by rfl)
      (s11f src (2 * i + 1) o (sent w gw) 1 (List.replicate k2 false) 0 (marks r (kL + 1)) (r - 1)
        (by rw [hp, hb']))
    have e1 := tr t1 t2 (by cfg_eq)
    have e2 := tr e1 (dbl o) (by cfg_eq)
    refine ⟨k2 - 1 - w + w + 1, timed_congr e2 (by simp [hb']; omega) rfl ?_⟩
    simp only [hb', Bool.toNat_false, zero_mul, Nat.add_zero]
    cfg_eq

theorem bits_loop (u : List Bool) : ∀ (bs : List Bool) (i o w gw k2 kL : ℕ),
    (∀ j (hj : j < bs.length), ∃ h : i + j < u.length, u[i + j] = bs[j]) →
    ∃ T gw' k2' : ℕ, Timed machine T
      (cfg 10 (frame u) (2 * i) o (sent w gw) 1 (List.replicate k2 false) 0 (marks bs.length kL)
        (bs.length - 1))
      (cfg 10 (frame u) (2 * (i + bs.length)) (o + w * RadixSemantics.value bs)
        (sent (w * 2 ^ bs.length) gw') 1 (List.replicate k2' false) 0 (marks 0 (kL + bs.length)) 0) ∧
      T + 6 * w ≤ 6 * (w * 2 ^ bs.length) + 8 * bs.length := by
  intro bs
  induction bs with
  | nil =>
    intro i o w gw k2 kL _
    refine ⟨0, gw, k2, ?_, by simp⟩
    simpa [RadixSemantics.value] using
      Timed.refl machine (cfg 10 (frame u) (2 * i) o (sent w gw) 1 (List.replicate k2 false) 0 (marks 0 kL) 0)
  | cons b bs ih =>
    intro i o w gw k2 kL hbs
    obtain ⟨hi, hb⟩ := hbs 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hi hb
    obtain ⟨k2', t1⟩ := bit_step u i hi o w gw k2 bs.length kL
    obtain ⟨T, gw', k2'', t2, hT⟩ := ih (i + 1) (o + (u[i]).toNat * w) (2 * w) (gw - w) k2' (kL + 1)
      (fun j hj => by
        obtain ⟨h, e⟩ := hbs (j + 1) (by simp; omega)
        exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using e⟩)
    have tt := tr t1 t2 (by cfg_eq)
    have hw : 2 * w * 2 ^ bs.length = w * 2 ^ (bs.length + 1) := by ring
    rw [hw] at hT
    refine ⟨_, gw', k2'', timed_congr tt rfl (by simp only [List.length_cons]; cfg_eq) ?_, ?_⟩
    · simp only [List.length_cons, hb]
      congr 1
      · omega
      · simp only [RadixSemantics.value]; ring
      · congr 1 <;> ring
      · congr 1 <;> omega
    · simp only [List.length_cons]
      split_ifs <;> omega

/-! ## One natWord, then the list -/

theorem mid_get (pre w post : List Bool) (j : ℕ) (hj : j < w.length) :
    ∃ h : pre.length + j < (pre ++ w ++ post).length, (pre ++ w ++ post)[pre.length + j] = w[j] := by
  refine ⟨by simp; omega, ?_⟩
  simp [hj]

theorem natWord_get_one (n j : ℕ) (hj : j < natBitLength n) :
    ∃ h : j < (RepairRepresentation.natWord n).length, (RepairRepresentation.natWord n)[j] = true := by
  have e := WilliamsInputHeader.natWord_eq n
  have hl : j < (RepairRepresentation.natWord n).length := by rw [e]; simp; omega
  refine ⟨hl, ?_⟩
  have key : ∀ (w : List Bool), w = List.replicate (natBitLength n) true ++
      false :: SignedSortKey.binary (natBitLength n) n → ∀ h : j < w.length, w[j] = true := by
    intro w hw h
    subst hw
    rw [List.getElem_append_left (by simpa using hj)]
    simp
  exact key _ e hl

theorem natWord_get_zero (n : ℕ) :
    ∃ h : natBitLength n < (RepairRepresentation.natWord n).length,
      (RepairRepresentation.natWord n)[natBitLength n] = false := by
  have e := WilliamsInputHeader.natWord_eq n
  have hl : natBitLength n < (RepairRepresentation.natWord n).length := by rw [e]; simp
  refine ⟨hl, ?_⟩
  have key : ∀ (w : List Bool), w = List.replicate (natBitLength n) true ++
      false :: SignedSortKey.binary (natBitLength n) n → ∀ h : natBitLength n < w.length,
      w[natBitLength n] = false := by
    intro w hw h
    subst hw
    rw [List.getElem_append_right (by simp)]
    simp
  exact key _ e hl

theorem natWord_get_bit (n k : ℕ) (hk : k < natBitLength n) :
    ∃ h : natBitLength n + 1 + k < (RepairRepresentation.natWord n).length,
      (RepairRepresentation.natWord n)[natBitLength n + 1 + k] =
        (SignedSortKey.binary (natBitLength n) n)[k]'(by simpa using hk) := by
  have e := WilliamsInputHeader.natWord_eq n
  have hl : natBitLength n + 1 + k < (RepairRepresentation.natWord n).length := by rw [e]; simp; omega
  refine ⟨hl, ?_⟩
  have key : ∀ (w : List Bool), w = List.replicate (natBitLength n) true ++
      false :: SignedSortKey.binary (natBitLength n) n → ∀ h : natBitLength n + 1 + k < w.length,
      w[natBitLength n + 1 + k] = (SignedSortKey.binary (natBitLength n) n)[k]'(by simpa using hk) := by
    intro w hw h
    subst hw
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate]
    have e2 : natBitLength n + 1 + k - natBitLength n = k + 1 := by omega
    simp only [e2, List.getElem_cons_succ]
  exact key _ e hl

theorem natWord_length (n : ℕ) :
    (RepairRepresentation.natWord n).length = natBitLength n + 1 + natBitLength n := by
  rw [WilliamsInputHeader.natWord_eq]
  simp
  omega

theorem natWord_value (n : ℕ) :
    RadixSemantics.value (SignedSortKey.binary (natBitLength n) n) = n :=
  SignedSortKey.binary_value _ _ (by unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) n)

/-- **One item.** From the item start (state 5) back to state 5 past the natWord, the accumulator
grows by exactly `n`; the three scratch tapes return to blanks at head 0. -/
theorem item (pre post : List Bool) (n o kW k2 kL : ℕ) :
    ∃ T kW' k2' kL' : ℕ, Timed machine T
      (cfg 5 (frame (pre ++ RepairRepresentation.natWord n ++ post)) (2 * pre.length) o
        (List.replicate kW false) 0 (List.replicate k2 false) 0 (List.replicate kL false) 0)
      (cfg 5 (frame (pre ++ RepairRepresentation.natWord n ++ post))
        (2 * (pre.length + (RepairRepresentation.natWord n).length)) (o + n)
        (List.replicate kW' false) 0 (List.replicate k2' false) 0 (List.replicate kL' false) 0) ∧
      T ≤ 8 * 2 ^ natBitLength n + 10 * natBitLength n + 6 := by
  set u := pre ++ RepairRepresentation.natWord n ++ post with hu
  set ℓ := natBitLength n with hℓ
  set i := pre.length with hi
  have hlen := natWord_length n
  have hget : ∀ j (hj : j < (RepairRepresentation.natWord n).length),
      ∃ h : i + j < u.length, u[i + j] = (RepairRepresentation.natWord n)[j] :=
    fun j hj => mid_get pre _ post j hj
  -- marker of the first logical bit
  obtain ⟨h0, _⟩ := hget 0 (by omega)
  have hm : readTapeBit (frame u) (2 * i) = true := by
    simpa using read_marker u i (by simpa using h0)
  have t1 := Timed.single (p := machine) (by rfl)
    (s5t (frame u) (2 * i) o (List.replicate kW false) 0 (List.replicate k2 false) 0 (List.replicate kL false) 0 hm)
  -- the unary length prefix
  have t2 := item_ones u o (List.replicate kW false) 0 (List.replicate k2 false) 0 ℓ i 0 kL (fun j hj => by
    obtain ⟨h, e⟩ := hget j (by omega)
    obtain ⟨_, e1⟩ := natWord_get_one n j hj
    exact ⟨h, e.trans e1⟩)
  -- the zero
  obtain ⟨hz, ez⟩ := hget ℓ (by omega)
  obtain ⟨_, ez1⟩ := natWord_get_zero n
  have hzr : readTapeBit (frame u) (2 * (i + ℓ) + 1) = false := by
    rw [read_payload u (i + ℓ) hz, ez, ez1]
  have t3 := Timed.single (p := machine) (by rfl)
    (s6f (frame u) (2 * (i + ℓ) + 1) o (List.replicate kW false) 0 (List.replicate k2 false) 0
      (marks (0 + ℓ) (kL - ℓ)) (0 + ℓ) hzr)
  have t4 := Timed.single (p := machine) (by rfl)
    (s9 (frame u) (2 * (i + ℓ) + 1 + 1) o (List.replicate kW false) (0 + 1) (List.replicate k2 false) 0
      (marks (0 + ℓ) (kL - ℓ)) (0 + ℓ - 1))
  rw [show (0 : ℕ) + 1 = 1 from rfl, blank_first] at t4
  -- the bits
  obtain ⟨T, gw', k2', t5, hT⟩ := bits_loop u (SignedSortKey.binary ℓ n) (i + ℓ + 1) o 1 (kW - 2) k2 (kL - ℓ)
    (fun j hj => by
      simp only [SignedSortKey.binary_length] at hj
      obtain ⟨h, e⟩ := hget (ℓ + 1 + j) (by omega)
      obtain ⟨_, e1⟩ := natWord_get_bit n j hj
      refine ⟨by omega, ?_⟩
      simp only [show i + ℓ + 1 + j = i + (ℓ + 1 + j) by omega]
      exact e.trans e1)
  have hv : RadixSemantics.value (SignedSortKey.binary ℓ n) = n := natWord_value n
  simp only [SignedSortKey.binary_length, one_mul] at t5 hT
  rw [hv] at t5
  have hLf : readTapeBit (marks 0 (kL - ℓ + ℓ)) 0 = false := by rw [read_marks]; simp
  have t6 := Timed.single (p := machine) (by rfl)
    (s10f (frame u) (2 * (i + ℓ + 1 + ℓ)) (o + n) (sent (2 ^ ℓ) gw') 1 (List.replicate k2' false) 0
      (marks 0 (kL - ℓ + ℓ)) 0 hLf)
  have t7 := walk18 (frame u) (2 * (i + ℓ + 1 + ℓ)) (marks 0 (kL - ℓ + ℓ)) 0 (o + n) (List.replicate k2' false) 0
    (2 ^ ℓ) gw' (2 ^ ℓ) 0 (by omega)
  have hf8 : readTapeBit (sent (2 ^ ℓ) gw') (1 + 0 + 2 ^ ℓ) = false := by rw [read_sent]; simp
  have t8 := Timed.single (p := machine) (by rfl)
    (s18f (frame u) (2 * (i + ℓ + 1 + ℓ)) (o + n) (sent (2 ^ ℓ) gw') (1 + 0 + 2 ^ ℓ) (List.replicate k2' false) 0
      (marks 0 (kL - ℓ + ℓ)) 0 hf8)
  have t9 := erase19 (frame u) (2 * (i + ℓ + 1 + ℓ)) (marks 0 (kL - ℓ + ℓ)) 0 (o + n) (List.replicate k2' false) 0
    (2 ^ ℓ) gw'
  have e1 := tr t1 t2 (by cfg_eq)
  have e2 := tr e1 t3 (by cfg_eq)
  have e3 := tr e2 t4 (by cfg_eq)
  have e4 := tr e3 t5 (by cfg_eq)
  have e5 := tr e4 t6 (by cfg_eq)
  have e6 := tr e5 t7 (by cfg_eq)
  have e7 := tr e6 t8 (by cfg_eq)
  have e8 := tr e7 t9 (by cfg_eq)
  rw [sent_zero] at e8
  have hend : cfg 5 (frame u) (2 * (i + ℓ) + 1 + 1 + 2 * ℓ + (1 + 0 + 2 ^ ℓ - 1 - 2 ^ ℓ)) (o + n)
      (List.replicate (gw' + 2 ^ ℓ + 1) false) 0 (List.replicate k2' false) 0 (marks 0 (kL - ℓ + ℓ)) 0 =
      cfg 5 (frame u) (2 * (i + (RepairRepresentation.natWord n).length)) (o + n)
      (List.replicate (gw' + 2 ^ ℓ + 1) false) 0 (List.replicate k2' false) 0 (List.replicate (kL - ℓ + ℓ) false) 0 := by
    unfold marks
    simp only [List.replicate_zero, List.nil_append]
    cfg_eq
  refine ⟨_, gw' + 2 ^ ℓ + 1, k2', kL - ℓ + ℓ, timed_congr e8 rfl (by cfg_eq) (by cfg_eq), ?_⟩
  rw [hℓ] at hT ⊢
  omega

/-- **The items.** Starting at state 5 at the first item, every natWord of `xs` adds its value. -/
theorem items (post : List Bool) : ∀ (xs : List ℕ) (pre : List Bool) (o kW k2 kL : ℕ),
    ∃ T kW' k2' kL' : ℕ, Timed machine T
      (cfg 5 (frame (pre ++ xs.flatMap RepairRepresentation.natWord ++ post)) (2 * pre.length) o
        (List.replicate kW false) 0 (List.replicate k2 false) 0 (List.replicate kL false) 0)
      (cfg 5 (frame (pre ++ xs.flatMap RepairRepresentation.natWord ++ post))
        (2 * (pre.length + (xs.flatMap RepairRepresentation.natWord).length)) (o + xs.sum)
        (List.replicate kW' false) 0 (List.replicate k2' false) 0 (List.replicate kL' false) 0) ∧
      T ≤ (xs.map (fun x => 8 * 2 ^ natBitLength x + 10 * natBitLength x + 6)).sum := by
  intro xs
  induction xs with
  | nil =>
    intro pre o kW k2 kL
    refine ⟨0, kW, k2, kL, ?_, by simp⟩
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, List.sum_nil]
    exact Timed.refl _ _
  | cons x xs ih =>
    intro pre o kW k2 kL
    have hw : pre ++ (x :: xs).flatMap RepairRepresentation.natWord ++ post =
        pre ++ RepairRepresentation.natWord x ++ (xs.flatMap RepairRepresentation.natWord ++ post) := by
      simp [List.append_assoc]
    have hw2 : pre ++ (x :: xs).flatMap RepairRepresentation.natWord ++ post =
        (pre ++ RepairRepresentation.natWord x) ++ xs.flatMap RepairRepresentation.natWord ++ post := by
      simp [List.append_assoc]
    obtain ⟨T1, kW1, k21, kL1, t1, h1⟩ := item pre (xs.flatMap RepairRepresentation.natWord ++ post) x o kW k2 kL
    rw [← hw] at t1
    obtain ⟨T2, kW2, k22, kL2, t2, h2⟩ := ih (pre ++ RepairRepresentation.natWord x) (o + x) kW1 k21 kL1
    rw [← hw2] at t2
    have tt := tr t1 t2 (by first | rfl | cfg_eq | (simp only [List.length_append]))
    have hend : cfg 5 (frame (pre ++ (x :: xs).flatMap RepairRepresentation.natWord ++ post))
        (2 * ((pre ++ RepairRepresentation.natWord x).length + (xs.flatMap RepairRepresentation.natWord).length))
        (o + x + xs.sum) (List.replicate kW2 false) 0 (List.replicate k22 false) 0 (List.replicate kL2 false) 0 =
        cfg 5 (frame (pre ++ (x :: xs).flatMap RepairRepresentation.natWord ++ post))
        (2 * (pre.length + ((x :: xs).flatMap RepairRepresentation.natWord).length))
        (o + (x :: xs).sum) (List.replicate kW2 false) 0 (List.replicate k22 false) 0 (List.replicate kL2 false) 0 := by
      simp only [List.length_append, List.flatMap_cons, List.sum_cons]
      cfg_eq
    refine ⟨_, kW2, k22, kL2, timed_congr tt rfl rfl hend, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## The whole run -/

theorem two_pow_bitLength (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    omega

theorem items_bound (xs : List ℕ) :
    (xs.map (fun x => 8 * 2 ^ natBitLength x + 10 * natBitLength x + 6)).sum ≤
      16 * xs.sum + 40 * (xs.flatMap RepairRepresentation.natWord).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, natWord_length]
    have := two_pow_bitLength x
    omega

theorem get_prefix (w b c : List Bool) (j : ℕ) (hj : j < w.length) :
    ∃ h : j < (w ++ b ++ c).length, (w ++ b ++ c)[j] = w[j] := by
  refine ⟨by simp; omega, ?_⟩
  simp [List.getElem_append_left, hj]

/-- **The sum.** One fixed machine: from the framed natWord list on tape 0 (all else empty, heads 0)
to `replicate xs.sum true` on tape 1, in at most `16·Σxs + 40·|natListWord xs| + 12` steps. -/
theorem run (xs : List ℕ) : ∃ (n : ℕ) (H1 : Fin 5 → ℕ) (A1 : Fin 5 → List Bool),
    Step machine n (fun _ => 0) (fun k => if k.val = 0 then frame (RepairRepresentation.natListWord xs) else [])
      H1 A1 ∧ A1 1 = List.replicate xs.sum true ∧
      n ≤ 16 * xs.sum + 40 * (RepairRepresentation.natListWord xs).length + 12 := by
  set u := RepairRepresentation.natWord xs.length ++ xs.flatMap RepairRepresentation.natWord ++ [] with hu
  have hnl : RepairRepresentation.natListWord xs = u := by simp [hu, RepairRepresentation.natListWord]
  set ℓ := natBitLength xs.length with hℓ
  have hlen := natWord_length xs.length
  have hget : ∀ j (hj : j < (RepairRepresentation.natWord xs.length).length),
      ∃ h : 0 + j < u.length, u[0 + j] = (RepairRepresentation.natWord xs.length)[j] := by
    intro j hj
    simp only [Nat.zero_add]
    exact get_prefix _ _ _ j hj
  have t1 := head_ones u 0 [] 0 [] 0 ℓ 0 0 0 (fun j hj => by
    obtain ⟨h, e⟩ := hget j (by omega)
    obtain ⟨_, e1⟩ := natWord_get_one xs.length j hj
    exact ⟨h, e.trans e1⟩)
  have t2 := Timed.single (p := machine) (by rfl)
    (s0 (frame u) (2 * (0 + ℓ)) 0 [] 0 [] 0 (marks (0 + ℓ) (0 - ℓ)) (0 + ℓ))
  obtain ⟨hz, ez⟩ := hget ℓ (by omega)
  obtain ⟨_, ez1⟩ := natWord_get_zero xs.length
  have hzr : readTapeBit (frame u) (2 * (0 + ℓ) + 1) = false := by
    rw [read_payload u (0 + ℓ) hz, ez, ez1]
  have t3 := Timed.single (p := machine) (by rfl)
    (s1f (frame u) (2 * (0 + ℓ) + 1) 0 [] 0 [] 0 (marks (0 + ℓ) (0 - ℓ)) (0 + ℓ) hzr)
  have t4 := head_skip u 0 [] 0 [] 0 ℓ (ℓ + 1) (0 - ℓ)
  obtain ⟨T5, kW, k2, kL, t5, h5⟩ := items [] xs (RepairRepresentation.natWord xs.length) 0 0 0 (0 - ℓ + ℓ)
  have hend : readTapeBit (frame u) (2 * u.length) = false := read_end u
  have hfin : 2 * ((RepairRepresentation.natWord xs.length).length +
      (xs.flatMap RepairRepresentation.natWord).length) = 2 * u.length := by
    rw [hu]; simp
  rw [hfin] at t5
  have t6 := Timed.single (p := machine) (by rfl)
    (s5f (frame u) (2 * u.length) (0 + xs.sum) (List.replicate kW false) 0 (List.replicate k2 false) 0
      (List.replicate kL false) 0 hend)
  have e1 := tr t1 t2 (by cfg_eq)
  have e2 := tr e1 t3 (by cfg_eq)
  have e3 := tr e2 t4 (by cfg_eq)
  have e4 := tr e3 t5 (by unfold marks; simp only [List.replicate_zero, List.nil_append]; cfg_eq)
  have e5 := tr e4 t6 rfl
  obtain ⟨r, hr, hf, hs⟩ := e5.run rfl
  have hc : (⟨machine.start, fun _ => 0, fun k : Fin 5 =>
      if k.val = 0 then frame (RepairRepresentation.natListWord xs) else []⟩ :
      Configuration 5 21) = cfg 0 (frame u) (2 * 0) 0 [] 0 [] 0 (marks 0 0) 0 := by
    apply configuration_ext
    · rfl
    · funext k; fin_cases k <;> rfl
    · funext k; fin_cases k
      · simp [cfg, hnl]
      all_goals rfl
  rw [← hc] at hr
  refine ⟨_, r.final.heads, r.final.tapes, ⟨r, hr, rfl, rfl, le_of_eq hs⟩, ?_, ?_⟩
  · rw [hf]
    simp [cfg]
  · have hb := items_bound xs
    have hl : u.length = ℓ + 1 + ℓ + (xs.flatMap RepairRepresentation.natWord).length := by
      rw [hu]; simp [hlen, hℓ]
    rw [hnl]
    omega

end NearCubicWires.PacketsGlue.NatSum

