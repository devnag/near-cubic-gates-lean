import Proof.MachineModel.ClockJoin
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Amplification.RecoveryTimedExecution

namespace NearCubicWires.RepairOrdinary.MatrixScorePhi
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

/-- Blank scratch of capacity `c`. Defined here, not imported from the matrix-score weight layout,
so that this module stays outside the printer's Request cone; it is the same list as
`MatrixScoreWeight.zeros c` (both `List.replicate c false`), so callers bridge by `rfl`. -/
def zeros (c : ℕ) : List Bool := List.replicate c false

/-- The paper's center-bit vector: XOR of the columns whose index bit is set in `n`. -/
def value (cols : List ℕ) (n : ℕ) : ℕ :=
  cols.zipIdx.foldl (fun acc cj => if n.testBit cj.2 then acc ^^^ cj.1 else acc) 0

/-- The columns as one tape: each column a framed `width`-bit word. -/
def columnsWord (width : ℕ) (cols : List ℕ) : List Bool :=
  cols.flatMap (fun x => frame (binary width x))

/-- Steps per call: polynomial in the column count and the width. -/
def budget (d width _m _c : ℕ) : ℕ := d * (8 * width + 4) + 4 * width + 3

/-- Control states. -/
def START : Fin 18 := 0
def CLRD : Fin 18 := 1
def CLRM : Fin 18 := 2
def RWOA : Fin 18 := 3
def RWEA : Fin 18 := 4
def COL : Fin 18 := 5
def SEL : Fin 18 := 6
def XD : Fin 18 := 7
def XM : Fin 18 := 8
def SD : Fin 18 := 9
def SM : Fin 18 := 10
def FIN : Fin 18 := 11
def FIN2 : Fin 18 := 12
def RO : Fin 18 := 13
def RE : Fin 18 := 14
def RWOB : Fin 18 := 15
def RWEB : Fin 18 := 16
def HALT : Fin 18 := 17

/-- An action writing `w` and moving by `m`, tape by tape. -/
def act (q : Fin 18) (w : Fin 4 → Option Bool) (m : Fin 4 → HeadMove) : Action 4 18 :=
  ⟨q, w, m⟩

def keep : Fin 4 → Option Bool := fun _ => none
def only (i : Fin 4) (b : Bool) : Fin 4 → Option Bool := fun k => if k = i then some b else none
def moves (a b c d : HeadMove) : Fin 4 → HeadMove := ![a, b, c, d]

def machine : Machine 4 18 where
  descriptionBits := 0
  start := START
  halted := fun q => decide (q = HALT)
  rule := fun q bits =>
    if q = START then
      if bits 2 then some (act CLRD (only 2 false) (moves .stay .stay .right .stay))
      else some (act HALT keep (moves .stay .stay .stay .stay))
    else if q = CLRD then some (act CLRM (only 2 false) (moves .stay .stay .right .stay))
    else if q = CLRM then
      if bits 2 then some (act CLRD keep (moves .stay .stay .right .stay))
      else some (act RWOA keep (moves .stay .stay .left .stay))
    else if q = RWOA then some (act RWEA keep (moves .stay .stay .left .stay))
    else if q = RWEA then
      if bits 2 then some (act RWOA keep (moves .stay .stay .left .stay))
      else some (act COL keep (moves .stay .stay .stay .stay))
    else if q = COL then
      if bits 1 then some (act SEL (only 3 true) (moves .right .stay .stay .right))
      else some (act FIN keep (moves .stay .stay .stay .left))
    else if q = SEL then
      if bits 0 then some (act XD keep (moves .right .right .right .stay))
      else some (act SD keep (moves .right .right .stay .stay))
    else if q = XD then some (act XM (only 2 (xor (bits 2) (bits 1))) (moves .stay .right .right .stay))
    else if q = XM then
      if bits 1 then some (act XD keep (moves .stay .right .right .stay))
      else some (act RWOA keep (moves .stay .right .left .stay))
    else if q = SD then some (act SM keep (moves .stay .right .stay .stay))
    else if q = SM then
      if bits 1 then some (act SD keep (moves .stay .right .stay .stay))
      else some (act COL keep (moves .stay .right .stay .stay))
    else if q = FIN then
      if bits 3 then some (act FIN2 (only 3 false) (moves .left .left .stay .left))
      else some (act HALT (only 2 true) (moves .stay .stay .stay .stay))
    else if q = FIN2 then some (act RO keep (moves .left .left .right .stay))
    else if q = RO then some (act RE keep (moves .stay .left .right .stay))
    else if q = RE then
      if bits 2 then some (act RO keep (moves .stay .left .right .stay))
      else some (act RWOB keep (moves .stay .stay .left .stay))
    else if q = RWOB then some (act RWEB keep (moves .stay .stay .left .stay))
    else if q = RWEB then
      if bits 2 then some (act RWOB keep (moves .stay .stay .left .stay))
      else some (act FIN keep (moves .stay .stay .stay .stay))
    else none

/-! ### Tape words -/

theorem read_eq (l : List Bool) (p : ℕ) : readTapeBit l p = l.getD p false := rfl

theorem write_eq_set (l : List Bool) (p : ℕ) (b : Bool) (hp : p < l.length) :
    writeTapeBit l p b = l.set p b := by
  induction l generalizing p with
  | nil => simp at hp
  | cons x xs ih =>
    cases p with
    | zero => rfl
    | succ p => simp [writeTapeBit, ih p (by simpa using hp)]

/-- A `w`-bit word given by its bit function. -/
def word (w : ℕ) (F : ℕ → Bool) : List Bool := (List.range w).map F

@[simp] theorem word_length (w : ℕ) (F : ℕ → Bool) : (word w F).length = w := by simp [word]

theorem word_getD (w : ℕ) (F : ℕ → Bool) (i : ℕ) :
    (word w F).getD i false = if i < w then F i else false := by
  unfold word
  by_cases hi : i < w
  · simp [hi, List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]

theorem word_set (w : ℕ) (F : ℕ → Bool) (i : ℕ) (b : Bool) :
    (word w F).set i b = word w (fun k => if k = i then b else F k) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [word, List.getElem_set, List.getElem_map, List.getElem_range]
    by_cases hk : i = k
    · subst hk; simp
    · simp [hk, Ne.symm hk]

theorem word_congr (w : ℕ) (F G : ℕ → Bool) (h : ∀ k, k < w → F k = G k) : word w F = word w G := by
  unfold word
  apply List.map_congr_left
  intro k hk
  exact h k (by simpa using hk)

theorem binary_eq_word (w a : ℕ) : binary w a = word w a.testBit := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    rw [binary, ih, word, word, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [Nat.testBit_zero, h]
    · apply List.map_congr_left; intro k _; simp [Nat.testBit_succ]

theorem binary_getD (w a j : ℕ) (hj : j < w) : (binary w a).getD j false = a.testBit j := by
  rw [binary_eq_word, word_getD, if_pos hj]

/-! ### Frames and the sentinel frame -/

@[simp] theorem frame_length (bs : List Bool) : (frame bs).length = 2 * bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [frame, ih]; omega

theorem frame_odd (bs : List Bool) (i : ℕ) : (frame bs).getD (2 * i + 1) false = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [frame]
  | cons b bs ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega]
      simpa [frame] using ih i

theorem frame_even (bs : List Bool) (i : ℕ) : (frame bs).getD (2 * i) false = decide (i < bs.length) := by
  induction bs generalizing i with
  | nil => cases i <;> simp [frame]
  | cons b bs ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      rw [show 2 * (i + 1) = 2 * i + 2 by omega]
      simpa [frame] using ih i

theorem frame_set (bs : List Bool) (i : ℕ) (b : Bool) (hi : i < bs.length) :
    (frame bs).set (2 * i + 1) b = frame (bs.set i b) := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons x bs ih =>
    cases i with
    | zero => simp [frame]
    | succ i =>
      rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega]
      simp [frame, ih i (by simpa using hi)]

/-- A frame whose first marker is the `false` sentinel: cell 0 becomes visible. -/
def sframe (bs : List Bool) : List Bool := (frame bs).set 0 false

@[simp] theorem sframe_length (bs : List Bool) : (sframe bs).length = 2 * bs.length + 1 := by
  simp [sframe]

theorem sframe_zero (bs : List Bool) : (sframe bs).getD 0 false = false := by
  cases bs <;> simp [sframe, frame]

theorem sframe_pos (bs : List Bool) (p : ℕ) (hp : p ≠ 0) :
    (sframe bs).getD p false = (frame bs).getD p false := by
  simp [sframe, List.getD_eq_getElem?_getD, Ne.symm hp]

theorem sframe_set (bs : List Bool) (i : ℕ) (b : Bool) (hi : i < bs.length) :
    (sframe bs).set (2 * i + 1) b = sframe (bs.set i b) := by
  unfold sframe
  rw [List.set_comm _ _ (by omega), frame_set _ _ _ hi]

theorem sframe_restore (bs : List Bool) (hne : bs ≠ []) : (sframe bs).set 0 true = frame bs := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp [sframe, frame]

theorem frame_install (bs : List Bool) : (frame bs).set 0 false = sframe bs := rfl

/-! ### Reading the tapes of a run -/

theorem sword_odd (w : ℕ) (F : ℕ → Bool) (i : ℕ) (hi : i < w) :
    readTapeBit (sframe (word w F)) (2 * i + 1) = F i := by
  rw [read_eq, sframe_pos _ _ (by omega), frame_odd, word_getD, if_pos hi]

theorem sword_even (w : ℕ) (F : ℕ → Bool) (i : ℕ) :
    readTapeBit (sframe (word w F)) (2 * i + 2) = decide (i + 1 < w) := by
  rw [read_eq, sframe_pos _ _ (by omega), show 2 * i + 2 = 2 * (i + 1) by omega, frame_even, word_length]

theorem sword_zero (w : ℕ) (F : ℕ → Bool) : readTapeBit (sframe (word w F)) 0 = false := by
  rw [read_eq, sframe_zero]

theorem sword_write (w : ℕ) (F : ℕ → Bool) (i : ℕ) (b : Bool) (hi : i < w) :
    writeTapeBit (sframe (word w F)) (2 * i + 1) b = sframe (word w (fun k => if k = i then b else F k)) := by
  rw [write_eq_set _ _ _ (by simp; omega), sframe_set _ _ _ (by simpa using hi), word_set]

/-! ### The columns tape -/

theorem columnsWord_cons (w x : ℕ) (xs : List ℕ) :
    columnsWord w (x :: xs) = frame (binary w x) ++ columnsWord w xs := by
  simp [columnsWord]

theorem columnsWord_append (w : ℕ) (xs ys : List ℕ) :
    columnsWord w (xs ++ ys) = columnsWord w xs ++ columnsWord w ys := by
  simp [columnsWord]

@[simp] theorem columnsWord_length (w : ℕ) (xs : List ℕ) :
    (columnsWord w xs).length = xs.length * (2 * w + 1) := by
  induction xs with
  | nil => simp [columnsWord]
  | cons x xs ih => rw [columnsWord_cons, List.length_append, ih, frame_length, binary_length]; simp; ring

theorem column_read (w x : ℕ) (done rest : List ℕ) (r : ℕ) (hr : r < 2 * w + 1) :
    readTapeBit (columnsWord w (done ++ x :: rest)) ((columnsWord w done).length + r) =
      (frame (binary w x)).getD r false := by
  rw [read_eq, columnsWord_append, columnsWord_cons,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simp; omega)]

theorem columns_end (w : ℕ) (cols : List ℕ) :
    readTapeBit (columnsWord w cols) (columnsWord w cols).length = false := by
  rw [read_eq]; simp [List.getD_eq_getElem?_getD]

/-! ### Configurations and single steps -/

def cfg (q : Fin 18) (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) : Configuration 4 18 :=
  ⟨q, ![h0, h1, h2, h3], ![t0, t1, t2, t3]⟩

def wr (t : List Bool) (h : ℕ) : Option Bool → List Bool
  | none => t
  | some b => writeTapeBit t h b

theorem step_cfg (q : Fin 18) (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (q' : Fin 18)
    (w : Fin 4 → Option Bool) (m : Fin 4 → HeadMove)
    (hr : machine.rule q ![readTapeBit t0 h0, readTapeBit t1 h1, readTapeBit t2 h2, readTapeBit t3 h3] =
      some (act q' w m)) :
    step machine (cfg q h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg q' ((m 0).apply h0) ((m 1).apply h1) ((m 2).apply h2) ((m 3).apply h3)
        (wr t0 h0 (w 0)) (wr t1 h1 (w 1)) (wr t2 h2 (w 2)) (wr t3 h3 (w 3))) := by
  have hs : (cfg q h0 h1 h2 h3 t0 t1 t2 t3).scanned =
      ![readTapeBit t0 h0, readTapeBit t1 h1, readTapeBit t2 h2, readTapeBit t3 h3] := by
    funext i; fin_cases i <;> rfl
  simp only [step, hs]
  rw [show (cfg q h0 h1 h2 h3 t0 t1 t2 t3).control = q from rfl, hr, Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [applyAction, cfg, act, wr] <;> split <;> simp_all

/-! ### The transitions, one lemma each -/

macro "phi_rule" : tactic => `(tactic| simp [machine, START, CLRD, CLRM, RWOA, RWEA, COL, SEL, XD, XM, SD, SM, FIN, FIN2, RO, RE, RWOB, RWEB, HALT, *])

theorem st_start (h0 h1 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 0 = true) :
    step machine (cfg START h0 h1 0 h3 t0 t1 t2 t3) =
      some (cfg CLRD h0 h1 1 h3 t0 t1 (writeTapeBit t2 0 false) t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ CLRD (only 2 false) (moves .stay .stay .right .stay) (by phi_rule)]
  rfl

theorem st_start0 (h0 h1 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 0 = false) :
    step machine (cfg START h0 h1 0 h3 t0 t1 t2 t3) =
      some (cfg HALT h0 h1 0 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ HALT keep (moves .stay .stay .stay .stay) (by phi_rule)]
  rfl

theorem st_clrd (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg CLRD h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg CLRM h0 h1 (h2 + 1) h3 t0 t1 (writeTapeBit t2 h2 false) t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ CLRM (only 2 false) (moves .stay .stay .right .stay) (by phi_rule)]
  rfl

theorem st_clrm_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = true) :
    step machine (cfg CLRM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg CLRD h0 h1 (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ CLRD keep (moves .stay .stay .right .stay) (by phi_rule)]
  rfl

theorem st_clrm_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = false) :
    step machine (cfg CLRM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWOA h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWOA keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rwoa (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg RWOA h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWEA h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWEA keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rwea_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = true) :
    step machine (cfg RWEA h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWOA h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWOA keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rwea_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = false) :
    step machine (cfg RWEA h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg COL h0 h1 h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ COL keep (moves .stay .stay .stay .stay) (by phi_rule)]
  rfl

theorem st_col_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = true) :
    step machine (cfg COL h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg SEL (h0 + 1) h1 h2 (h3 + 1) t0 t1 t2 (writeTapeBit t3 h3 true)) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ SEL (only 3 true) (moves .right .stay .stay .right) (by phi_rule)]
  rfl

theorem st_col_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = false) :
    step machine (cfg COL h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg FIN h0 h1 h2 (h3 - 1) t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ FIN keep (moves .stay .stay .stay .left) (by phi_rule)]
  rfl

theorem st_sel_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t0 h0 = true) :
    step machine (cfg SEL h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg XD (h0 + 1) (h1 + 1) (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ XD keep (moves .right .right .right .stay) (by phi_rule)]
  rfl

theorem st_sel_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t0 h0 = false) :
    step machine (cfg SEL h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg SD (h0 + 1) (h1 + 1) h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ SD keep (moves .right .right .stay .stay) (by phi_rule)]
  rfl

theorem st_xd (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg XD h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg XM h0 (h1 + 1) (h2 + 1) h3 t0 t1 (writeTapeBit t2 h2 (xor (readTapeBit t2 h2) (readTapeBit t1 h1))) t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ XM (only 2 (xor (readTapeBit t2 h2) (readTapeBit t1 h1))) (moves .stay .right .right .stay) (by phi_rule)]
  rfl

theorem st_xm_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = true) :
    step machine (cfg XM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg XD h0 (h1 + 1) (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ XD keep (moves .stay .right .right .stay) (by phi_rule)]
  rfl

theorem st_xm_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = false) :
    step machine (cfg XM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWOA h0 (h1 + 1) (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWOA keep (moves .stay .right .left .stay) (by phi_rule)]
  rfl

theorem st_sd (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg SD h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg SM h0 (h1 + 1) h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ SM keep (moves .stay .right .stay .stay) (by phi_rule)]
  rfl

theorem st_sm_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = true) :
    step machine (cfg SM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg SD h0 (h1 + 1) h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ SD keep (moves .stay .right .stay .stay) (by phi_rule)]
  rfl

theorem st_sm_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t1 h1 = false) :
    step machine (cfg SM h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg COL h0 (h1 + 1) h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ COL keep (moves .stay .right .stay .stay) (by phi_rule)]
  rfl

theorem st_fin_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t3 h3 = true) :
    step machine (cfg FIN h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg FIN2 (h0 - 1) (h1 - 1) h2 (h3 - 1) t0 t1 t2 (writeTapeBit t3 h3 false)) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ FIN2 (only 3 false) (moves .left .left .stay .left) (by phi_rule)]
  rfl

theorem st_fin_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t3 h3 = false) :
    step machine (cfg FIN h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg HALT h0 h1 h2 h3 t0 t1 (writeTapeBit t2 h2 true) t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ HALT (only 2 true) (moves .stay .stay .stay .stay) (by phi_rule)]
  rfl

theorem st_fin2 (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg FIN2 h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RO (h0 - 1) (h1 - 1) (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RO keep (moves .left .left .right .stay) (by phi_rule)]
  rfl

theorem st_ro (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg RO h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RE h0 (h1 - 1) (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RE keep (moves .stay .left .right .stay) (by phi_rule)]
  rfl

theorem st_re_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = true) :
    step machine (cfg RE h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RO h0 (h1 - 1) (h2 + 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RO keep (moves .stay .left .right .stay) (by phi_rule)]
  rfl

theorem st_re_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = false) :
    step machine (cfg RE h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWOB h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWOB keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rwob (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool)  :
    step machine (cfg RWOB h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWEB h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWEB keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rweb_t (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = true) :
    step machine (cfg RWEB h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg RWOB h0 h1 (h2 - 1) h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ RWOB keep (moves .stay .stay .left .stay) (by phi_rule)]
  rfl

theorem st_rweb_f (h0 h1 h2 h3 : ℕ) (t0 t1 t2 t3 : List Bool) (hb : readTapeBit t2 h2 = false) :
    step machine (cfg RWEB h0 h1 h2 h3 t0 t1 t2 t3) =
      some (cfg FIN h0 h1 h2 h3 t0 t1 t2 t3) := by
  rw [step_cfg _ _ _ _ _ _ _ _ _ FIN keep (moves .stay .stay .stay .stay) (by phi_rule)]
  rfl

/-! ### Segments -/

open RecoveryExecution in
theorem timed_cast {c d : Configuration 4 18} {n k : ℕ} (h : Timed machine n c d) (e : n = k) :
    Timed machine k c d := e ▸ h

open RecoveryExecution in
theorem one {q : Fin 18} {h0 h1 h2 h3 : ℕ} {t0 t1 t2 t3 : List Bool} {d : Configuration 4 18}
    (hn : q ≠ HALT) (h : step machine (cfg q h0 h1 h2 h3 t0 t1 t2 t3) = some d) :
    Timed machine 1 (cfg q h0 h1 h2 h3 t0 t1 t2 t3) d :=
  Timed.single (by simpa [machine, cfg] using hn) h

open RecoveryExecution in
/-- Rewind tape 2 onto its sentinel, then continue the column loop. -/
theorem rewind_a (w : ℕ) (F : ℕ → Bool) (h0 h1 h3 : ℕ) (t0 t1 t3 : List Bool) (i : ℕ) (hi : i < w) :
    Timed machine (2 * i + 2) (cfg RWOA h0 h1 (2 * i + 1) h3 t0 t1 (sframe (word w F)) t3)
      (cfg COL h0 h1 0 h3 t0 t1 (sframe (word w F)) t3) := by
  induction i with
  | zero =>
    have a := one (by decide) (st_rwoa h0 h1 1 h3 t0 t1 (sframe (word w F)) t3)
    have b := one (by decide) (st_rwea_f h0 h1 0 h3 t0 t1 (sframe (word w F)) t3 (sword_zero w F))
    exact a.trans b
  | succ i ih =>
    have a := one (by decide) (st_rwoa h0 h1 (2 * (i + 1) + 1) h3 t0 t1 (sframe (word w F)) t3)
    rw [show 2 * (i + 1) + 1 - 1 = 2 * i + 2 by omega] at a
    have hb := sword_even w F i
    rw [decide_eq_true (by omega : i + 1 < w)] at hb
    have b := one (by decide) (st_rwea_t h0 h1 (2 * i + 2) h3 t0 t1 (sframe (word w F)) t3 hb)
    rw [show 2 * i + 2 - 1 = 2 * i + 1 by omega] at b
    exact timed_cast ((a.trans b).trans (ih (by omega))) (by omega)

open RecoveryExecution in
/-- Rewind tape 2 onto its sentinel, then continue the final unmarking loop. -/
theorem rewind_b (w : ℕ) (F : ℕ → Bool) (h0 h1 h3 : ℕ) (t0 t1 t3 : List Bool) (i : ℕ) (hi : i < w) :
    Timed machine (2 * i + 2) (cfg RWOB h0 h1 (2 * i + 1) h3 t0 t1 (sframe (word w F)) t3)
      (cfg FIN h0 h1 0 h3 t0 t1 (sframe (word w F)) t3) := by
  induction i with
  | zero =>
    have a := one (by decide) (st_rwob h0 h1 1 h3 t0 t1 (sframe (word w F)) t3)
    have b := one (by decide) (st_rweb_f h0 h1 0 h3 t0 t1 (sframe (word w F)) t3 (sword_zero w F))
    exact a.trans b
  | succ i ih =>
    have a := one (by decide) (st_rwob h0 h1 (2 * (i + 1) + 1) h3 t0 t1 (sframe (word w F)) t3)
    rw [show 2 * (i + 1) + 1 - 1 = 2 * i + 2 by omega] at a
    have hb := sword_even w F i
    rw [decide_eq_true (by omega : i + 1 < w)] at hb
    have b := one (by decide) (st_rweb_t h0 h1 (2 * i + 2) h3 t0 t1 (sframe (word w F)) t3 hb)
    rw [show 2 * i + 2 - 1 = 2 * i + 1 by omega] at b
    exact timed_cast ((a.trans b).trans (ih (by omega))) (by omega)

open RecoveryExecution in
/-- Clear the data bits of tape 2 from bit `i` on. -/
theorem clear_loop (w : ℕ) (h0 h1 h3 : ℕ) (t0 t1 t3 : List Bool) :
    ∀ (k i : ℕ) (G : ℕ → Bool), i + k = w → 1 ≤ k → (∀ j, j < i → G j = false) →
    Timed machine (2 * k) (cfg CLRD h0 h1 (2 * i + 1) h3 t0 t1 (sframe (word w G)) t3)
      (cfg RWOA h0 h1 (2 * w - 1) h3 t0 t1 (sframe (word w (fun _ => false))) t3) := by
  intro k
  induction k with
  | zero => intro i G _ hk; omega
  | succ k ih =>
    intro i G hik _ hG
    have a := one (by decide) (st_clrd h0 h1 (2 * i + 1) h3 t0 t1 (sframe (word w G)) t3)
    rw [sword_write w G i false (by omega), show 2 * i + 1 + 1 = 2 * i + 2 by omega] at a
    have hG' : ∀ j, j < i + 1 → (fun j => if j = i then false else G j) j = false := by
      intro j hj; by_cases e : j = i
      · simp [e]
      · simp [e, hG j (by omega)]
    by_cases hlast : k = 0
    · subst hlast
      have hb := sword_even w (fun j => if j = i then false else G j) i
      rw [decide_eq_false (by omega : ¬ i + 1 < w)] at hb
      have b := one (by decide) (st_clrm_f h0 h1 (2 * i + 2) h3 t0 t1 _ t3 hb)
      rw [show 2 * i + 2 - 1 = 2 * w - 1 by omega] at b
      rw [← word_congr w _ (fun _ => false) (fun j hj => hG' j (by omega))]
      exact a.trans b
    · have hb := sword_even w (fun j => if j = i then false else G j) i
      rw [decide_eq_true (by omega : i + 1 < w)] at hb
      have b := one (by decide) (st_clrm_t h0 h1 (2 * i + 2) h3 t0 t1 _ t3 hb)
      rw [show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by omega] at b
      exact timed_cast ((a.trans b).trans (ih (i + 1) _ (by omega) (by omega) hG')) (by omega)

open RecoveryExecution in
/-- Install the sentinel, clear the assignment, rewind: `4 w + 1` steps to the column loop. -/
theorem prelude (w a : ℕ) (hw : 1 ≤ w) (h0 h1 h3 : ℕ) (t0 t1 t3 : List Bool) :
    Timed machine (4 * w + 1) (cfg START h0 h1 0 h3 t0 t1 (frame (binary w a)) t3)
      (cfg COL h0 h1 0 h3 t0 t1 (sframe (binary w 0)) t3) := by
  have hb : readTapeBit (frame (binary w a)) 0 = true := by
    rw [read_eq, show (0 : ℕ) = 2 * 0 by rfl, frame_even]; simp; omega
  have a1 := one (by decide) (st_start h0 h1 h3 t0 t1 _ t3 hb)
  rw [write_eq_set _ _ _ (by simp), frame_install,
    show sframe (binary w a) = sframe (word w a.testBit) by rw [binary_eq_word]] at a1
  have a2 := clear_loop w h0 h1 h3 t0 t1 t3 w 0 a.testBit (by omega) hw (fun j hj => absurd hj (Nat.not_lt_zero j))
  simp only [Nat.mul_zero, Nat.zero_add] at a2
  have a3 := rewind_a w (fun _ => false) h0 h1 h3 t0 t1 t3 (w - 1) (by omega)
  rw [show 2 * (w - 1) + 1 = 2 * w - 1 by omega] at a3
  have e : sframe (binary w 0) = sframe (word w (fun _ => false)) := by
    rw [binary_eq_word]; congr 1; apply word_congr; intro k _; simp
  rw [e]
  exact timed_cast ((a1.trans a2).trans a3) (by omega)

/-! ### The scratch counter -/

/-- Scratch with `j` unary marks. -/
def marks (c j : ℕ) : List Bool := List.replicate j true ++ List.replicate (c - j) false

theorem marks_zero (c : ℕ) : marks c 0 = zeros c := by simp [marks, zeros]

theorem marks_mark (c j : ℕ) (hj : j < c) : writeTapeBit (marks c j) j true = marks c (j + 1) := by
  induction j generalizing c with
  | zero =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hj
    simp [marks, List.replicate_succ, writeTapeBit]
  | succ j ih =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ c by omega)
    have e : ∀ k, k ≤ c → marks (1 + c) (k + 1) = true :: marks c k := by
      intro k _; simp [marks, List.replicate_succ, show 1 + c - (k + 1) = c - k by omega]
    rw [e j (by omega), e (j + 1) (by omega)]
    simp [writeTapeBit, ih c (by omega)]

theorem marks_erase (c k : ℕ) (hk : k < c) : writeTapeBit (marks c (k + 1)) k false = marks c k := by
  induction k generalizing c with
  | zero =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hk
    simp [marks, List.replicate_succ, writeTapeBit]
  | succ k ih =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ c by omega)
    have e : ∀ j, j ≤ c → marks (1 + c) (j + 1) = true :: marks c j := by
      intro j _; simp [marks, List.replicate_succ, show 1 + c - (j + 1) = c - j by omega]
    rw [e (k + 1) (by omega), e k (by omega)]
    simp [writeTapeBit, ih c (by omega)]

theorem marks_read (c k : ℕ) : readTapeBit (marks c (k + 1)) k = true := by
  rw [read_eq, marks, List.getD_append _ _ _ _ (by simp)]; simp

theorem marks_read_zero (c : ℕ) : readTapeBit (marks c 0) 0 = false := by
  rw [read_eq]; cases c <;> simp [marks]

/-! ### One column -/

theorem frame_read_odd (w x i : ℕ) (hi : i < w) :
    (frame (binary w x)).getD (2 * i + 1) false = x.testBit i := by
  rw [frame_odd, binary_getD _ _ _ hi]

theorem frame_read_even (w x i : ℕ) :
    (frame (binary w x)).getD (2 * i + 2) false = decide (i + 1 < w) := by
  rw [show 2 * i + 2 = 2 * (i + 1) by omega, frame_even, binary_length]

/-- Partial XOR: bits below `i` already hold `acc ^^^ x`. -/
def xorPrefix (acc x i : ℕ) : ℕ → Bool := fun j => if j < i then (acc ^^^ x).testBit j else acc.testBit j

open RecoveryExecution in
theorem xor_loop (w acc x h0 h3 P : ℕ) (t0 t1 t3 : List Bool)
    (hread : ∀ r, r < 2 * w + 1 → readTapeBit t1 (P + r) = (frame (binary w x)).getD r false) :
    ∀ k i, i + k = w → 1 ≤ k →
    Timed machine (2 * k)
      (cfg XD h0 (P + (2 * i + 1)) (2 * i + 1) h3 t0 t1 (sframe (word w (xorPrefix acc x i))) t3)
      (cfg RWOA h0 (P + (2 * w + 1)) (2 * w - 1) h3 t0 t1 (sframe (word w (acc ^^^ x).testBit)) t3) := by
  intro k
  induction k with
  | zero => intro i _ hk; omega
  | succ k ih =>
    intro i hik _
    have r1 := hread (2 * i + 1) (by omega)
    rw [frame_read_odd w x i (by omega)] at r1
    have a := one (by decide) (st_xd h0 (P + (2 * i + 1)) (2 * i + 1) h3 t0 t1 (sframe (word w (xorPrefix acc x i))) t3)
    rw [sword_odd w _ i (by omega), r1, sword_write w _ i _ (by omega),
      show P + (2 * i + 1) + 1 = P + (2 * i + 2) by omega, show 2 * i + 1 + 1 = 2 * i + 2 by omega] at a
    have e : word w (fun j => if j = i then (xorPrefix acc x i i ^^ x.testBit i) else xorPrefix acc x i j) =
        word w (xorPrefix acc x (i + 1)) := by
      apply word_congr; intro j _
      unfold xorPrefix
      by_cases hj : j = i
      · subst hj; simp [Nat.testBit_xor]
      · have h1 : (j < i + 1) ↔ (j < i) := by omega
        simp [hj, h1]
    rw [e] at a
    have r2 := hread (2 * i + 2) (by omega)
    rw [frame_read_even] at r2
    by_cases hlast : k = 0
    · subst hlast
      rw [decide_eq_false (by omega : ¬ i + 1 < w)] at r2
      have b := one (by decide) (st_xm_f h0 (P + (2 * i + 2)) (2 * i + 2) h3 t0 t1 (sframe (word w (xorPrefix acc x (i + 1)))) t3 r2)
      rw [show P + (2 * i + 2) + 1 = P + (2 * w + 1) by omega, show 2 * i + 2 - 1 = 2 * w - 1 by omega] at b
      have e2 : word w (xorPrefix acc x (i + 1)) = word w (acc ^^^ x).testBit := by
        apply word_congr; intro j hj; simp [xorPrefix, show j < i + 1 by omega]
      rw [← e2]
      exact a.trans b
    · rw [decide_eq_true (by omega : i + 1 < w)] at r2
      have b := one (by decide) (st_xm_t h0 (P + (2 * i + 2)) (2 * i + 2) h3 t0 t1 (sframe (word w (xorPrefix acc x (i + 1)))) t3 r2)
      rw [show P + (2 * i + 2) + 1 = P + (2 * (i + 1) + 1) by omega,
        show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by omega] at b
      exact timed_cast ((a.trans b).trans (ih (i + 1) (by omega) (by omega))) (by omega)

open RecoveryExecution in
theorem skip_loop (w x h0 h2 h3 P : ℕ) (t0 t1 t2 t3 : List Bool)
    (hread : ∀ r, r < 2 * w + 1 → readTapeBit t1 (P + r) = (frame (binary w x)).getD r false) :
    ∀ k i, i + k = w → 1 ≤ k →
    Timed machine (2 * k) (cfg SD h0 (P + (2 * i + 1)) h2 h3 t0 t1 t2 t3)
      (cfg COL h0 (P + (2 * w + 1)) h2 h3 t0 t1 t2 t3) := by
  intro k
  induction k with
  | zero => intro i _ hk; omega
  | succ k ih =>
    intro i hik _
    have a := one (by decide) (st_sd h0 (P + (2 * i + 1)) h2 h3 t0 t1 t2 t3)
    rw [show P + (2 * i + 1) + 1 = P + (2 * i + 2) by omega] at a
    have r2 := hread (2 * i + 2) (by omega)
    rw [frame_read_even] at r2
    by_cases hlast : k = 0
    · subst hlast
      rw [decide_eq_false (by omega : ¬ i + 1 < w)] at r2
      have b := one (by decide) (st_sm_f h0 (P + (2 * i + 2)) h2 h3 t0 t1 t2 t3 r2)
      rw [show P + (2 * i + 2) + 1 = P + (2 * w + 1) by omega] at b
      exact a.trans b
    · rw [decide_eq_true (by omega : i + 1 < w)] at r2
      have b := one (by decide) (st_sm_t h0 (P + (2 * i + 2)) h2 h3 t0 t1 t2 t3 r2)
      rw [show P + (2 * i + 2) + 1 = P + (2 * (i + 1) + 1) by omega] at b
      exact timed_cast ((a.trans b).trans (ih (i + 1) (by omega) (by omega))) (by omega)

/-- Steps for one column: `2 w + 2`, plus `2 w` more when it is selected. -/
def colCost (w : ℕ) (selected : Bool) : ℕ := if selected then 4 * w + 2 else 2 * w + 2

open RecoveryExecution in
theorem column (w m n c acc x j P : ℕ) (t1 : List Bool) (hw : 1 ≤ w) (hj : j < m) (hjc : j < c)
    (hread : ∀ r, r < 2 * w + 1 → readTapeBit t1 (P + r) = (frame (binary w x)).getD r false) :
    Timed machine (colCost w (n.testBit j))
      (cfg COL (2 * j) P 0 j (frame (binary m n)) t1 (sframe (binary w acc)) (marks c j))
      (cfg COL (2 * (j + 1)) (P + (2 * w + 1)) 0 (j + 1) (frame (binary m n)) t1
        (sframe (binary w (if n.testBit j then acc ^^^ x else acc))) (marks c (j + 1))) := by
  have r0 := hread 0 (by omega)
  rw [show (0 : ℕ) = 2 * 0 by rfl, frame_even, binary_length, decide_eq_true (by omega : 0 < w)] at r0
  simp only [Nat.mul_zero, Nat.add_zero] at r0
  have a := one (by decide) (st_col_t (2 * j) P 0 j (frame (binary m n)) t1 (sframe (binary w acc)) (marks c j) r0)
  rw [marks_mark c j hjc] at a
  have hsel : readTapeBit (frame (binary m n)) (2 * j + 1) = n.testBit j := by
    rw [read_eq, frame_odd, binary_getD _ _ _ hj]
  cases hb : n.testBit j with
  | true =>
    rw [hb] at hsel
    have b := one (by decide) (st_sel_t (2 * j + 1) P 0 (j + 1) (frame (binary m n)) t1 (sframe (binary w acc)) (marks c (j + 1)) hsel)
    have e0 : sframe (binary w acc) = sframe (word w (xorPrefix acc x 0)) := by
      rw [binary_eq_word]; congr 1
    rw [e0, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, show P + 1 = P + (2 * 0 + 1) by omega,
      show (0 : ℕ) + 1 = 2 * 0 + 1 by rfl] at b
    rw [e0] at a
    have x1 := xor_loop w acc x (2 * (j + 1)) (j + 1) P (frame (binary m n)) t1 (marks c (j + 1)) hread w 0 (by omega) hw
    have x2 := rewind_a w (acc ^^^ x).testBit (2 * (j + 1)) (P + (2 * w + 1)) (j + 1) (frame (binary m n)) t1
      (marks c (j + 1)) (w - 1) (by omega)
    rw [show 2 * (w - 1) + 1 = 2 * w - 1 by omega] at x2
    have hx : sframe (binary w (acc ^^^ x)) = sframe (word w (acc ^^^ x).testBit) := by rw [binary_eq_word]
    simp only [colCost, ↓reduceIte, hx, e0]
    exact timed_cast (((a.trans b).trans x1).trans x2) (by omega)
  | false =>
    rw [hb] at hsel
    have b := one (by decide) (st_sel_f (2 * j + 1) P 0 (j + 1) (frame (binary m n)) t1 (sframe (binary w acc)) (marks c (j + 1)) hsel)
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega, show P + 1 = P + (2 * 0 + 1) by omega] at b
    have s1 := skip_loop w x (2 * (j + 1)) 0 (j + 1) P (frame (binary m n)) t1 (sframe (binary w acc)) (marks c (j + 1)) hread w 0 (by omega) hw
    simp only [colCost, Bool.false_eq_true, ↓reduceIte]
    exact timed_cast ((a.trans b).trans s1) (by omega)

/-! ### All columns -/

/-- The value after the columns `xs`, the first of which has index `j`. -/
def fold (n j : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | x :: xs, acc => fold n (j + 1) xs (if n.testBit j then acc ^^^ x else acc)

def colsCost (w n j : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: xs => colCost w (n.testBit j) + colsCost w n (j + 1) xs

theorem colsCost_le (w n j : ℕ) (xs : List ℕ) : colsCost w n j xs ≤ xs.length * (4 * w + 2) := by
  induction xs generalizing j with
  | nil => simp [colsCost]
  | cons x xs ih =>
    have h := ih (j + 1)
    have hc : colCost w (n.testBit j) ≤ 4 * w + 2 := by unfold colCost; split <;> omega
    simp only [colsCost, List.length_cons]
    nlinarith

theorem value_eq_fold (cols : List ℕ) (n : ℕ) : value cols n = fold n 0 cols 0 := by
  unfold value
  suffices h : ∀ (xs : List ℕ) (j acc : ℕ),
      (xs.zipIdx j).foldl (fun acc cj => if n.testBit cj.2 then acc ^^^ cj.1 else acc) acc = fold n j xs acc from
    h cols 0 0
  intro xs
  induction xs with
  | nil => intro j acc; rfl
  | cons x xs ih => intro j acc; simp only [List.zipIdx_cons, List.foldl_cons, fold]; exact ih (j + 1) _

open RecoveryExecution in
theorem columns (w m n c : ℕ) (hw : 1 ≤ w) (t1 : List Bool) :
    ∀ (rest : List ℕ) (j P acc : ℕ), j + rest.length ≤ m → j + rest.length < c →
    (∀ i x, rest[i]? = some x → ∀ r, r < 2 * w + 1 →
      readTapeBit t1 (P + i * (2 * w + 1) + r) = (frame (binary w x)).getD r false) →
    Timed machine (colsCost w n j rest)
      (cfg COL (2 * j) P 0 j (frame (binary m n)) t1 (sframe (binary w acc)) (marks c j))
      (cfg COL (2 * (j + rest.length)) (P + rest.length * (2 * w + 1)) 0 (j + rest.length)
        (frame (binary m n)) t1 (sframe (binary w (fold n j rest acc))) (marks c (j + rest.length))) := by
  intro rest
  induction rest with
  | nil => intro j P acc _ _ _; simpa [colsCost, fold] using Timed.refl machine _
  | cons x xs ih =>
    intro j P acc hm hc hread
    have h0 : ∀ r, r < 2 * w + 1 → readTapeBit t1 (P + r) = (frame (binary w x)).getD r false := by
      intro r hr; simpa using hread 0 x rfl r hr
    have a := column w m n c acc x j P t1 hw (by simp at hm; omega) (by simp at hc; omega) h0
    have b := ih (j + 1) (P + (2 * w + 1)) (if n.testBit j then acc ^^^ x else acc)
      (by simp at hm; omega) (by simp at hc; omega)
      (fun i y hy r hr => by
        have := hread (i + 1) y (by simpa using hy) r hr
        rw [show P + (i + 1) * (2 * w + 1) + r = P + (2 * w + 1) + i * (2 * w + 1) + r by ring] at this
        exact this)
    simp only [colsCost, fold, List.length_cons]
    rw [show j + (xs.length + 1) = j + 1 + xs.length by omega,
      show P + (xs.length + 1) * (2 * w + 1) = P + (2 * w + 1) + xs.length * (2 * w + 1) by ring]
    exact a.trans b

theorem columns_read (w : ℕ) (cols : List ℕ) (i x : ℕ) (hx : cols[i]? = some x) (r : ℕ) (hr : r < 2 * w + 1) :
    readTapeBit (columnsWord w cols) (0 + i * (2 * w + 1) + r) = (frame (binary w x)).getD r false := by
  have hi : i < cols.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
  have hsplit : cols = cols.take i ++ x :: cols.drop (i + 1) := by
    rw [List.getElem?_eq_getElem hi] at hx
    have e := List.take_append_drop i cols
    rw [List.drop_eq_getElem_cons hi, Option.some_inj.mp hx] at e
    exact e.symm
  have hl : (columnsWord w (cols.take i)).length = i * (2 * w + 1) := by
    rw [columnsWord_length, List.length_take, min_eq_left (by omega)]
  have := column_read w x (cols.take i) (cols.drop (i + 1)) r hr
  rw [← hsplit, hl] at this
  simpa using this

/-! ### The final unmarking loop -/

open RecoveryExecution in
theorem ruler (w h0 h3 Y : ℕ) (t0 t1 t3 : List Bool) (G : ℕ → Bool) :
    ∀ k i, i + k = w → 1 ≤ k →
    Timed machine (2 * k) (cfg RO h0 (Y + (2 * k - 1)) (2 * i + 1) h3 t0 t1 (sframe (word w G)) t3)
      (cfg RWOB h0 Y (2 * w - 1) h3 t0 t1 (sframe (word w G)) t3) := by
  intro k
  induction k with
  | zero => intro i _ hk; omega
  | succ k ih =>
    intro i hik _
    have a := one (by decide) (st_ro h0 (Y + (2 * (k + 1) - 1)) (2 * i + 1) h3 t0 t1 (sframe (word w G)) t3)
    rw [show Y + (2 * (k + 1) - 1) - 1 = Y + 2 * k by omega, show 2 * i + 1 + 1 = 2 * i + 2 by omega] at a
    have hb := sword_even w G i
    by_cases hlast : k = 0
    · subst hlast
      rw [decide_eq_false (by omega : ¬ i + 1 < w)] at hb
      have b := one (by decide) (st_re_f h0 (Y + 2 * 0) (2 * i + 2) h3 t0 t1 (sframe (word w G)) t3 hb)
      rw [show 2 * i + 2 - 1 = 2 * w - 1 by omega, show Y + 2 * 0 = Y by omega] at b
      exact a.trans b
    · rw [decide_eq_true (by omega : i + 1 < w)] at hb
      have b := one (by decide) (st_re_t h0 (Y + 2 * k) (2 * i + 2) h3 t0 t1 (sframe (word w G)) t3 hb)
      rw [show Y + 2 * k - 1 = Y + (2 * k - 1) by omega, show 2 * i + 2 + 1 = 2 * (i + 1) + 1 by omega] at b
      exact timed_cast ((a.trans b).trans (ih (i + 1) (by omega) (by omega))) (by omega)

open RecoveryExecution in
theorem final_loop (w c : ℕ) (hw : 1 ≤ w) (t0 t1 : List Bool) (G : ℕ → Bool) :
    ∀ k, k ≤ c →
    Timed machine (k * (4 * w + 2)) (cfg FIN (2 * k) (k * (2 * w + 1)) 0 (k - 1) t0 t1 (sframe (word w G)) (marks c k))
      (cfg FIN 0 0 0 0 t0 t1 (sframe (word w G)) (marks c 0)) := by
  intro k
  induction k with
  | zero => intro _; simpa using Timed.refl machine _
  | succ k ih =>
    intro hk
    have a := one (by decide) (st_fin_t (2 * (k + 1)) ((k + 1) * (2 * w + 1)) 0 (k + 1 - 1) t0 t1
      (sframe (word w G)) (marks c (k + 1)) (by rw [show k + 1 - 1 = k by omega]; exact marks_read c k))
    rw [show k + 1 - 1 = k by omega, marks_erase c k (by omega)] at a
    have b := one (by decide) (st_fin2 (2 * (k + 1) - 1) ((k + 1) * (2 * w + 1) - 1) 0 (k - 1) t0 t1
      (sframe (word w G)) (marks c k))
    rw [show 2 * (k + 1) - 1 - 1 = 2 * k by omega,
      show (k + 1) * (2 * w + 1) - 1 - 1 = k * (2 * w + 1) + (2 * w - 1) by
        rw [Nat.add_mul, Nat.one_mul]; omega,
      show (0 : ℕ) + 1 = 2 * 0 + 1 by rfl] at b
    have r := ruler w (2 * k) (k - 1) (k * (2 * w + 1)) t0 t1 (marks c k) G w 0 (by omega) hw
    have rw' := rewind_b w G (2 * k) (k * (2 * w + 1)) (k - 1) t0 t1 (marks c k) (w - 1) (by omega)
    rw [show 2 * (w - 1) + 1 = 2 * w - 1 by omega] at rw'
    exact timed_cast ((((a.trans b).trans r).trans rw').trans (ih (by omega))) (by rw [Nat.add_mul]; omega)

/-! ### The whole call -/

theorem initial (t0 t1 t2 t3 : List Bool) :
    initialConfiguration machine ![t0, t1, t2, t3] = cfg START 0 0 0 0 t0 t1 t2 t3 := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

open RecoveryExecution in
theorem ready (m width n a c : ℕ) (cols : List ℕ) (hlen : cols.length ≤ m)
    (hcols : ∀ x ∈ cols, x < 2 ^ width) (ha : a < 2 ^ width) (hc : width + cols.length + 2 ≤ c) :
    ClockJoin.ReadyRun machine (budget cols.length width m c)
      ![frame (binary m n), columnsWord width cols, frame (binary width a), zeros c]
      ![frame (binary m n), columnsWord width cols, frame (binary width (value cols n)), zeros c] := by
  -- `hcols` and `ha` are the caller's range facts; the run is correct without them.
  have _ := hcols
  have _ := ha
  rcases Nat.eq_zero_or_pos width with hw0 | hw
  · -- width 0: the assignment tape is `[false]`; the machine halts at once.
    subst hw0
    have s := one (by decide) (st_start0 0 0 0 (frame (binary m n)) (columnsWord 0 cols)
      (frame (binary 0 a)) (zeros c) rfl)
    obtain ⟨r, hr, hf, hs⟩ := s.run rfl
    refine ClockJoin.enlarge machine 1 _ _ _ ⟨r, ?_, ?_, ?_, ?_⟩ (by unfold budget; omega)
    · rw [run, initial]; exact hr
    · rw [hf]; funext i; fin_cases i <;> rfl
    · intro i; rw [hf]; fin_cases i <;> rfl
    · omega
  · -- width ≥ 1
    have p := prelude width a hw 0 0 0 (frame (binary m n)) (columnsWord width cols) (zeros c)
    rw [← marks_zero] at p
    have q := columns width m n c hw (columnsWord width cols) cols 0 0 0 (by omega) (by omega)
      (fun i x hx r hr => columns_read width cols i x hx r hr)
    simp only [Nat.mul_zero, Nat.zero_add] at q
    have hv : sframe (binary width (fold n 0 cols 0)) = sframe (word width (fold n 0 cols 0).testBit) := by
      rw [binary_eq_word]
    rw [hv] at q
    have e := one (by decide) (st_col_f (2 * cols.length) (cols.length * (2 * width + 1)) 0 cols.length
      (frame (binary m n)) (columnsWord width cols) (sframe (word width (fold n 0 cols 0).testBit))
      (marks c cols.length)
      (by rw [show cols.length * (2 * width + 1) = (columnsWord width cols).length by simp]
          exact columns_end width cols))
    have f := final_loop width c hw (frame (binary m n)) (columnsWord width cols) (fold n 0 cols 0).testBit
      cols.length (by omega)
    have g := one (by decide) (st_fin_f 0 0 0 0 (frame (binary m n)) (columnsWord width cols)
      (sframe (word width (fold n 0 cols 0).testBit)) (marks c 0) (marks_read_zero c))
    rw [write_eq_set _ _ _ (by simp),
      sframe_restore _ (List.ne_nil_of_length_pos (by rw [word_length]; omega)),
      show frame (word width (fold n 0 cols 0).testBit) = frame (binary width (fold n 0 cols 0)) by
        rw [binary_eq_word]] at g
    have whole := (((p.trans q).trans e).trans f).trans g
    obtain ⟨r, hr, hf, hs⟩ := whole.run rfl
    refine ClockJoin.enlarge machine _ _ _ _ ⟨r, ?_, ?_, ?_, le_of_eq hs⟩ ?_
    · rw [run, initial]; exact hr
    · rw [hf, value_eq_fold, ← marks_zero]; funext i; fin_cases i <;> rfl
    · intro i; rw [hf]; fin_cases i <;> rfl
    · have := colsCost_le width n 0 cols
      unfold budget; nlinarith

/-! ### The value itself -/

theorem fold_lt (w n : ℕ) : ∀ (xs : List ℕ) (j acc : ℕ), (∀ x ∈ xs, x < 2 ^ w) → acc < 2 ^ w →
    fold n j xs acc < 2 ^ w := by
  intro xs
  induction xs with
  | nil => intro j acc _ h; exact h
  | cons x xs ih =>
    intro j acc hx h
    apply ih (j + 1) _ (fun y hy => hx y (by simp [hy]))
    split
    · exact Nat.xor_lt_two_pow h (hx x (by simp))
    · exact h

theorem value_lt (cols : List ℕ) (n width : ℕ) :
    (∀ x ∈ cols, x < 2 ^ width) → value cols n < 2 ^ width := by
  intro h
  rw [value_eq_fold]
  exact fold_lt width n cols 0 0 h (Nat.two_pow_pos width)

theorem fold_powers (n : ℕ) : ∀ (k j : ℕ),
    fold n j ((List.range' j k).map (2 ^ ·)) (n % 2 ^ j) = n % 2 ^ (j + k) := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ih =>
    intro j
    rw [List.range'_succ, List.map_cons, fold, show j + (k + 1) = (j + 1) + k by omega, ← ih (j + 1)]
    congr 1
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hb : n.testBit j
    · simp only [hb, if_true, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
      by_cases hij : i = j
      · subst hij; simp [hb]
      · rcases Nat.lt_or_gt_of_ne hij with h | h
        · simp [h, show i < j + 1 by omega, Ne.symm hij]
        · simp [show ¬ i < j by omega, show ¬ i < j + 1 by omega, Ne.symm hij]
    · simp only [hb, Bool.false_eq_true, if_false, Nat.testBit_mod_two_pow]
      by_cases hij : i = j
      · subst hij; simp [hb]
      · rcases Nat.lt_or_gt_of_ne hij with h | h
        · simp [h, show i < j + 1 by omega]
        · simp [show ¬ i < j by omega, show ¬ i < j + 1 by omega]

theorem value_identity (d n : ℕ) : n < 2 ^ d → value ((List.range d).map (2 ^ ·)) n = n := by
  intro h
  have e := fold_powers n d 0
  simp only [pow_zero, Nat.mod_one, Nat.zero_add] at e
  rw [value_eq_fold, List.range_eq_range', e, Nat.mod_eq_of_lt h]

/-! ### Computable twin: `machine` itself runs; `Checks/OrdinaryMatrixScorePhiChecks.lean` evaluates it
against `value` on concrete instances. -/

def testInput (m width a c : ℕ) (cols : List ℕ) (n : ℕ) : Fin 4 → List Bool :=
  ![frame (binary m n), columnsWord width cols, frame (binary width a), zeros c]

def testRun (m width a c : ℕ) (cols : List ℕ) (n : ℕ) :=
  (run machine (budget cols.length width m c) (testInput m width a c cols n)).map fun r =>
    (r.final.tapes 0 == frame (binary m n), r.final.tapes 1 == columnsWord width cols,
     r.final.tapes 2 == frame (binary width (value cols n)), r.final.tapes 3 == zeros c,
     (List.finRange 4).all (fun i => r.final.heads i == 0), r.steps, value cols n)

end NearCubicWires.RepairOrdinary.MatrixScorePhi
