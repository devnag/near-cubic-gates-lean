import Proof.Wire_3_5.ListMachineRowFilter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun atomCode monoBits recW polyWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

/-- What the output receives: the word, or nothing. -/
def ow (cp : Bool) (w : List Bool) : List Bool := if cp then w else []

theorem ow_append (cp : Bool) (x y : List Bool) : ow cp x ++ ow cp y = ow cp (x ++ y) := by
  cases cp <;> simp [ow]

theorem ow_nil (cp : Bool) : ow cp [] = [] := by cases cp <;> rfl

namespace PolyCopy
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

def wr (cp b : Bool) : Option Bool := if cp then some b else none
def mv (cp : Bool) : HeadMove := if cp then .right else .stay

/-- Tape 0 the store (read), tape 1 the output. State `0` reads a record marker or the polynomial's end, `1` a
frame marker or the frame's end, `2` a frame bit, `3` halts one cell past the polynomial. Every bit read is written
to the output when `cp`. -/
def machine (cp : Bool) : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none (wr cp true) .right (mv cp)
      else act 3 none (wr cp false) .right (mv cp))
    else if q.val = 1 then some (if sc 0 then act 2 none (wr cp true) .right (mv cp)
      else act 0 none (wr cp false) .right (mv cp))
    else if q.val = 2 then some (act 1 none (wr cp (sc 0)) .right (mv cp))
    else none

theorem rule0 (cp x y : Bool) : (machine cp).rule 0 ![x, y] =
    some (if x then act 1 none (wr cp true) .right (mv cp) else act 3 none (wr cp false) .right (mv cp)) := by
  simp [machine]
theorem rule1 (cp x y : Bool) : (machine cp).rule 1 ![x, y] =
    some (if x then act 2 none (wr cp true) .right (mv cp) else act 0 none (wr cp false) .right (mv cp)) := by
  simp [machine]
theorem rule2 (cp x y : Bool) : (machine cp).rule 2 ![x, y] = some (act 1 none (wr cp x) .right (mv cp)) := by
  simp [machine]

theorem one_step (cp : Bool) (q q' : Fin 4) (A : List Bool) (h : ℕ) (o B : List Bool) (b : Bool)
    (hr : (machine cp).rule q ![readTapeBit A h, readTapeBit (overlay o B) o.length] =
      some (act q' none (wr cp b) .right (mv cp))) :
    Timed (machine cp) 1 (cfg q A (overlay o B) h o.length)
      (cfg q' A (overlay (o ++ ow cp [b]) B) (h + 1) (o ++ ow cp [b]).length) := by
  have hq : (machine cp).halted q = false := by
    have : q.val ≠ 3 := by
      intro e
      have : q = 3 := Fin.ext e
      subst this; simp [machine] at hr
    simp [machine, this]
  have s := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg (machine cp) q q' A (overlay o B) h o.length none
    (wr cp b) .right (mv cp) hr
  cases cp
  · simp only [wr, mv, NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, Bool.false_eq_true,
      if_false] at s
    simpa [ow] using Timed.single (p := machine false) hq s
  · simp only [wr, mv, NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, if_true, overlay_write] at s
    have e : (o ++ [b]).length = o.length + 1 := by simp
    rw [← e] at s
    simpa [ow] using Timed.single (p := machine true) hq s

theorem frame_timed (cp : Bool) (tail B : List Bool) : ∀ (w pre o : List Bool),
    Timed (machine cp) (2 * w.length + 1)
      (cfg 1 (pre ++ frame w ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ frame w ++ tail) (overlay (o ++ ow cp (frame w)) B) (pre.length + (2 * w.length + 1))
        (o ++ ow cp (frame w)).length) := by
  intro w
  induction w with
  | nil =>
    intro pre o
    have hr : readTapeBit (pre ++ frame [] ++ tail) pre.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre tail false
    have := one_step cp 1 0 (pre ++ frame [] ++ tail) pre.length o B false (by rw [rule1, hr]; simp)
    simpa [frame] using this
  | cons b w ih =>
    intro pre o
    have hr : readTapeBit (pre ++ frame (b :: w) ++ tail) pre.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre (b :: frame w ++ tail) true
    have hb : readTapeBit (pre ++ frame (b :: w) ++ tail) (pre.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) b
    have t1 := one_step cp 1 2 (pre ++ frame (b :: w) ++ tail) pre.length o B true (by rw [rule1, hr]; simp)
    have t2 := one_step cp 2 1 (pre ++ frame (b :: w) ++ tail) (pre.length + 1) (o ++ ow cp [true]) B b
      (by rw [rule2, hb])
    have e0 : pre ++ frame (b :: w) ++ tail = (pre ++ [true, b]) ++ frame w ++ tail := by
      simp [frame, List.append_assoc]
    have t3 := ih (pre ++ [true, b]) (o ++ ow cp [true] ++ ow cp [b])
    rw [← e0] at t3
    have e1 : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    have e2 : o ++ ow cp [true] ++ ow cp [b] ++ ow cp (frame w) = o ++ ow cp (frame (b :: w)) := by
      rw [List.append_assoc, List.append_assoc, ow_append, ow_append]; simp [frame]
    rw [e1, e2, show pre.length + 1 + 1 + (2 * w.length + 1) = pre.length + (2 * (b :: w).length + 1) by
      simp; omega] at t3
    have := (t1.trans t2).trans t3
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (b :: w).length + 1 by simp; omega] at this

theorem rec_timed (cp : Bool) (tail B : List Bool) (m : List ℕ) (pre o : List Bool) :
    Timed (machine cp) (recW m).length
      (cfg 0 (pre ++ recW m ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ recW m ++ tail) (overlay (o ++ ow cp (recW m)) B) (pre.length + (recW m).length)
        (o ++ ow cp (recW m)).length) := by
  have hr : readTapeBit (pre ++ recW m ++ tail) pre.length = true := by
    simpa [recW, List.append_assoc] using Streaming.read_append pre (frame (monoBits m) ++ tail) true
  have t1 := one_step cp 0 1 (pre ++ recW m ++ tail) pre.length o B true (by rw [rule0, hr]; simp)
  have e0 : pre ++ recW m ++ tail = (pre ++ [true]) ++ frame (monoBits m) ++ tail := by simp [recW]
  have t2 := frame_timed cp tail B (monoBits m) (pre ++ [true]) (o ++ ow cp [true])
  rw [← e0] at t2
  have e2 : o ++ ow cp [true] ++ ow cp (frame (monoBits m)) = o ++ ow cp (recW m) := by
    rw [List.append_assoc, ow_append]; simp [recW]
  have e3 : (pre ++ [true]).length = pre.length + 1 := by simp
  rw [e3] at t2
  rw [e2, show pre.length + 1 + (2 * (monoBits m).length + 1) = pre.length + (recW m).length by
    simp [Rec.recW_length]; omega] at t2
  have := t1.trans t2
  rwa [show 1 + (2 * (monoBits m).length + 1) = (recW m).length by simp [Rec.recW_length]; omega] at this

theorem recs_timed (cp : Bool) (tail B : List Bool) : ∀ (p : List (List ℕ)) (pre o : List Bool),
    Timed (machine cp) (p.flatMap recW).length
      (cfg 0 (pre ++ p.flatMap recW ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ p.flatMap recW ++ tail) (overlay (o ++ ow cp (p.flatMap recW)) B)
        (pre.length + (p.flatMap recW).length) (o ++ ow cp (p.flatMap recW)).length) := by
  intro p
  induction p with
  | nil => intro pre o; simpa [ow_nil] using Timed.refl (machine cp) (cfg 0 (pre ++ tail) (overlay o B) pre.length o.length)
  | cons m p ih =>
    intro pre o
    have t1 := rec_timed cp (p.flatMap recW ++ tail) B m pre o
    have e0 : pre ++ (m :: p).flatMap recW ++ tail = pre ++ recW m ++ (p.flatMap recW ++ tail) := by simp
    rw [← e0] at t1
    have t2 := ih (pre ++ recW m) (o ++ ow cp (recW m))
    have e1 : pre ++ recW m ++ p.flatMap recW ++ tail = pre ++ (m :: p).flatMap recW ++ tail := by simp
    rw [e1] at t2
    have e2 : o ++ ow cp (recW m) ++ ow cp (p.flatMap recW) = o ++ ow cp ((m :: p).flatMap recW) := by
      rw [List.append_assoc, ow_append]; simp
    have e3 : (pre ++ recW m).length = pre.length + (recW m).length := by simp
    rw [e3] at t2
    rw [e2, show pre.length + (recW m).length + (p.flatMap recW).length = pre.length + ((m :: p).flatMap recW).length by
      simp; omega] at t2
    have := t1.trans t2
    rwa [show (recW m).length + (p.flatMap recW).length = ((m :: p).flatMap recW).length by simp] at this

/-- **Copy or pass a printed polynomial.** -/
theorem run (cp : Bool) (pre : List Bool) (p : List (List ℕ)) (tail o B : List Bool) :
    Step (machine cp) (polyWord p).length ![pre.length, o.length] ![pre ++ polyWord p ++ tail, overlay o B]
      ![pre.length + (polyWord p).length, (o ++ ow cp (polyWord p)).length]
      ![pre ++ polyWord p ++ tail, overlay (o ++ ow cp (polyWord p)) B] := by
  have e0 : pre ++ polyWord p ++ tail = pre ++ p.flatMap recW ++ (false :: tail) := by simp [polyWord]
  have t1 := recs_timed cp (false :: tail) B p pre o
  have hr : readTapeBit (pre ++ p.flatMap recW ++ (false :: tail)) (pre ++ p.flatMap recW).length = false := by
    simpa [List.append_assoc] using Streaming.read_append (pre ++ p.flatMap recW) tail false
  have hr' : readTapeBit (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length) = false := by
    simpa using hr
  have t2 := one_step cp 0 3 (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length)
    (o ++ ow cp (p.flatMap recW)) B false (by rw [rule0, hr']; simp)
  have t := t1.trans t2
  rw [← e0] at t
  have e2 : o ++ ow cp (p.flatMap recW) ++ ow cp [false] = o ++ ow cp (polyWord p) := by
    rw [List.append_assoc, ow_append]; simp [polyWord]
  rw [e2, show (p.flatMap recW).length + 1 = (polyWord p).length by simp [polyWord],
    show pre.length + (p.flatMap recW).length + 1 = pre.length + (polyWord p).length by simp [polyWord]; omega] at t
  obtain ⟨r, hr, hf, hs⟩ := t.run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end PolyCopy

/-! ## Selecting a row's factors from the store -/

/-- The store of a population's visit factors: the pairs `(N_k, P_k)`. -/
def stW (ps : List (List (List ℕ) × List (List ℕ))) : List Bool := ps.flatMap fun q => polyWord q.1 ++ polyWord q.2

/-- The factor records of the row `r`: `P_k` where `r_k`, else `N_k`. -/
def selW (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) : List Bool :=
  (r.zip ps).flatMap fun bq => true :: polyWord (if bq.1 then bq.2.2 else bq.2.1)

/-- Layout: 0 the row, 1 the store, 2 the output. -/
noncomputable def skipX : Machine 3 2 := RecoveryFocus.machine ![(0 : Fin 3)] Rec.Skip.machine
noncomputable def putT : Machine 3 2 := RecoveryFocus.machine ![(2 : Fin 3)] (Put.machine true)
noncomputable def pc (cp : Bool) : Machine 3 4 := RecoveryFocus.machine ![(1 : Fin 3), 2] (PolyCopy.machine cp)
noncomputable def brSel := Block.branchM (0 : Fin 3) (Composition.machine (pc false) (pc true))
  (Composition.machine (pc true) (pc false))
noncomputable def selBody := Composition.machine (Composition.machine (Composition.machine skipX putT) brSel) skipX
/-- **The selection loop.** -/
noncomputable def selM := StreamController.machine selBody (0 : Fin 3)

theorem skipX_step (h s o : ℕ) (X S O : List Bool) : Step skipX 1 ![h, s, o] ![X, S, O] ![h + 1, s, o] ![X, S, O] := by
  have d := dockRun (Rec.Skip.run X h) ![(0 : Fin 3)] (by intro a b _; exact Subsingleton.elim a b) ![h, s, o] ![X, S, O]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine d.congr ?_ ?_
  · apply dockH_eq_of _ (by intro a b _; exact Subsingleton.elim a b)
    · intro j; fin_cases j; rfl
    · intro i hi; fin_cases i
      · exact absurd rfl (hi 0)
      · rfl
      · rfl
  · apply install_eq_of _ (by intro a b _; exact Subsingleton.elim a b)
    · intro j; fin_cases j; rfl
    · intro i hi; fin_cases i <;> rfl

theorem putT_step (h s : ℕ) (X S o B : List Bool) :
    Step putT 1 ![h, s, o.length] ![X, S, overlay o B] ![h, s, (o ++ [true]).length] ![X, S, overlay (o ++ [true]) B] := by
  have d := dockRun (Put.run true o B) ![(2 : Fin 3)] (by intro a b _; exact Subsingleton.elim a b)
    ![h, s, o.length] ![X, S, overlay o B] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  refine d.congr ?_ ?_
  · apply dockH_eq_of _ (by intro a b _; exact Subsingleton.elim a b)
    · intro j; fin_cases j; rfl
    · intro i hi; fin_cases i
      · rfl
      · rfl
      · exact absurd rfl (hi 0)
  · apply install_eq_of _ (by intro a b _; exact Subsingleton.elim a b)
    · intro j; fin_cases j; rfl
    · intro i hi; fin_cases i
      · rfl
      · rfl
      · exact absurd rfl (hi 0)

theorem pair12_inj : Function.Injective ![(1 : Fin 3), 2] := by decide

theorem pc_step (cp : Bool) (h : ℕ) (X pre : List Bool) (p : List (List ℕ)) (tail o B : List Bool) :
    Step (pc cp) (polyWord p).length ![h, pre.length, o.length] ![X, pre ++ polyWord p ++ tail, overlay o B]
      ![h, pre.length + (polyWord p).length, (o ++ ow cp (polyWord p)).length]
      ![X, pre ++ polyWord p ++ tail, overlay (o ++ ow cp (polyWord p)) B] := by
  have d := dockRun (PolyCopy.run cp pre p tail o B) ![(1 : Fin 3), 2] pair12_inj ![h, pre.length, o.length]
    ![X, pre ++ polyWord p ++ tail, overlay o B] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine d.congr ?_ ?_
  · apply dockH_eq_of _ pair12_inj
    · intro j; fin_cases j <;> rfl
    · intro i hi; fin_cases i
      · rfl
      · exact absurd rfl (hi 0)
      · exact absurd rfl (hi 1)
  · apply install_eq_of _ pair12_inj
    · intro j; fin_cases j <;> rfl
    · intro i hi; fin_cases i
      · rfl
      · exact absurd rfl (hi 0)
      · exact absurd rfl (hi 1)

/-- One selected factor: pass or copy `N`, then copy or pass `P`, by the row bit `b`. -/
theorem brSel_step (b : Bool) (h : ℕ) (X pre : List Bool) (N P : List (List ℕ)) (tail o B : List Bool)
    (hb : readTapeBit X h = b) :
    Step brSel ((polyWord N).length + 1 + (polyWord P).length + 2) ![h, pre.length, o.length]
      ![X, pre ++ (polyWord N ++ polyWord P) ++ tail, overlay o B]
      ![h, pre.length + (polyWord N ++ polyWord P).length, (o ++ polyWord (if b then P else N)).length]
      ![X, pre ++ (polyWord N ++ polyWord P) ++ tail, overlay (o ++ polyWord (if b then P else N)) B] := by
  have e0 : pre ++ (polyWord N ++ polyWord P) ++ tail = pre ++ polyWord N ++ (polyWord P ++ tail) := by simp
  have e1 : pre ++ (polyWord N ++ polyWord P) ++ tail = (pre ++ polyWord N) ++ polyWord P ++ tail := by simp
  cases b
  · have s1 := pc_step true h X pre N (polyWord P ++ tail) o B
    have s2 := pc_step false h X (pre ++ polyWord N) P tail (o ++ ow true (polyWord N)) B
    rw [← e0] at s1
    rw [← e1] at s2
    have e2 : pre.length + (polyWord N).length = (pre ++ polyWord N).length := by simp
    rw [e2] at s1
    have t := Block.branch_false (0 : Fin 3) (Composition.machine (pc false) (pc true)) (s1.seq s2)
      (by simpa using hb)
    refine t.congr ?_ ?_
    · simp [ow, Nat.add_assoc]
    · simp [ow]
  · have s1 := pc_step false h X pre N (polyWord P ++ tail) o B
    have s2 := pc_step true h X (pre ++ polyWord N) P tail (o ++ ow false (polyWord N)) B
    rw [← e0] at s1
    rw [← e1] at s2
    have e2 : pre.length + (polyWord N).length = (pre ++ polyWord N).length := by simp
    rw [e2] at s1
    have e3 : o ++ ow false (polyWord N) = o := by simp [ow]
    rw [e3] at s1 s2
    have t := Block.branch_true (0 : Fin 3) (Composition.machine (pc true) (pc false)) (s1.seq s2)
      (by simpa using hb)
    refine t.congr ?_ ?_
    · simp [ow, Nat.add_assoc]
    · simp [ow]

/-! ### Reading a framed row, splitting the store -/

theorem frame_split (r : List Bool) (j : ℕ) (hj : j < r.length) :
    frame r = Streaming.marks (r.take j) ++ (true :: r[j] :: frame (r.drop (j + 1))) := by
  conv_lhs => rw [← List.take_append_drop j r]
  rw [Streaming.frame_append, List.drop_eq_getElem_cons hj]
  rfl

theorem frame_read_mark (r : List Bool) (j : ℕ) (hj : j < r.length) : readTapeBit (frame r) (2 * j) = true := by
  rw [frame_split r j hj]
  have := Streaming.read_append (Streaming.marks (r.take j)) (r[j] :: frame (r.drop (j + 1))) true
  simpa [List.length_take, Nat.min_eq_left hj.le] using this

theorem frame_read_bit (r : List Bool) (j : ℕ) (hj : j < r.length) : readTapeBit (frame r) (2 * j + 1) = r[j] := by
  rw [frame_split r j hj]
  have := Streaming.read_append (Streaming.marks (r.take j) ++ [true]) (frame (r.drop (j + 1))) r[j]
  simpa [List.length_take, Nat.min_eq_left hj.le, List.append_assoc] using this

theorem frame_read_end (r : List Bool) : readTapeBit (frame r) (2 * r.length) = false := by
  have := Streaming.frame_append r []
  rw [List.append_nil] at this
  rw [this]
  have h := Streaming.read_append (Streaming.marks r) [] false
  simpa [frame] using h

theorem stW_split (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) (hj : j < ps.length) :
    stW ps = stW (ps.take j) ++ (polyWord ps[j].1 ++ polyWord ps[j].2) ++ stW (ps.drop (j + 1)) := by
  conv_lhs => rw [← List.take_append_drop j ps, List.drop_eq_getElem_cons hj]
  simp only [stW, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem stW_take_succ (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) (hj : j < ps.length) :
    stW (ps.take (j + 1)) = stW (ps.take j) ++ (polyWord ps[j].1 ++ polyWord ps[j].2) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [stW, List.flatMap_append, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem selW_take_succ (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) (hj : j < r.length)
    (hl : r.length = ps.length) :
    selW (r.take (j + 1)) (ps.take (j + 1)) =
      selW (r.take j) (ps.take j) ++ (true :: polyWord (if r[j] then ps[j].2 else ps[j].1)) := by
  have hj' : j < ps.length := hl ▸ hj
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj']
  unfold selW
  rw [List.zip_append (by simp [List.length_take]; omega)]
  simp

/-- The cost of pass `j` of the selection loop. -/
def selPass (ps : List (List (List ℕ) × List (List ℕ))) (j : ℕ) : ℕ :=
  (1 + 1 + 1) + 1 + ((polyWord (ps.getD j ([], [])).1).length + 1 + (polyWord (ps.getD j ([], [])).2).length + 2) + 1 + 1

/-- The selection's heads and tapes before pass `j`. -/
def selH (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) (o : List Bool) (j : ℕ) : Fin 3 → ℕ :=
  ![2 * j, (stW (ps.take j)).length, (o ++ selW (r.take j) (ps.take j)).length]
def selA (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) (tail o B : List Bool) (j : ℕ) :
    Fin 3 → List Bool :=
  ![frame r, stW ps ++ tail, overlay (o ++ selW (r.take j) (ps.take j)) B]

theorem selBody_step (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) (hl : r.length = ps.length)
    (tail o B : List Bool) (j : ℕ) (hj : j < r.length) :
    Step selBody (selPass ps j) (selH r ps o j) (selA r ps tail o B j) (selH r ps o (j + 1)) (selA r ps tail o B (j + 1)) := by
  have hj' : j < ps.length := hl ▸ hj
  set sel := o ++ selW (r.take j) (ps.take j) with hsel
  have s1 := skipX_step (2 * j) (stW (ps.take j)).length sel.length (frame r) (stW ps ++ tail) (overlay sel B)
  have s2 := putT_step (2 * j + 1) (stW (ps.take j)).length (frame r) (stW ps ++ tail) sel B
  have hsplit : stW ps ++ tail = stW (ps.take j) ++ (polyWord ps[j].1 ++ polyWord ps[j].2) ++
      (stW (ps.drop (j + 1)) ++ tail) := by
    rw [stW_split ps j hj']; simp [List.append_assoc]
  rw [hsplit] at s1 s2
  have s3 := brSel_step r[j] (2 * j + 1) (frame r) (stW (ps.take j)) ps[j].1 ps[j].2 (stW (ps.drop (j + 1)) ++ tail)
    (sel ++ [true]) B (frame_read_bit r j hj)
  have s4 := skipX_step (2 * j + 1) ((stW (ps.take j)).length + (polyWord ps[j].1 ++ polyWord ps[j].2).length)
    (sel ++ [true] ++ polyWord (if r[j] then ps[j].2 else ps[j].1)).length (frame r)
    (stW (ps.take j) ++ (polyWord ps[j].1 ++ polyWord ps[j].2) ++ (stW (ps.drop (j + 1)) ++ tail))
    (overlay (sel ++ [true] ++ polyWord (if r[j] then ps[j].2 else ps[j].1)) B)
  have t := ((s1.seq s2).seq s3).seq s4
  rw [← hsplit] at t
  have eo : sel ++ [true] ++ polyWord (if r[j] then ps[j].2 else ps[j].1) = o ++ selW (r.take (j + 1)) (ps.take (j + 1)) := by
    rw [selW_take_succ r ps j hj hl, hsel]; simp [List.append_assoc]
  rw [eo] at t
  refine (t.congr ?_ rfl).enlarge (le_of_eq ?_)
  · simp only [selH, stW_take_succ ps j hj', List.length_append]
    funext i; fin_cases i <;> simp; omega
  · simp [selPass, List.getElem?_eq_getElem hj']

/-- **The selection loop**: for the row `r`, the output receives the factor records `selW r ps`. -/
theorem sel_run (r : List Bool) (ps : List (List (List ℕ) × List (List ℕ))) (hl : r.length = ps.length)
    (tail o B : List Bool) :
    Step selM (((List.range r.length).map fun j => selPass ps j + 2).sum + 1) ![0, 0, o.length]
      ![frame r, stW ps ++ tail, overlay o B] ![2 * r.length, (stW ps).length, (o ++ selW r ps).length]
      ![frame r, stW ps ++ tail, overlay (o ++ selW r ps) B] := by
  have hW := Block.WhileBody.run ({
    body := selBody
    tape := (0 : Fin 3)
    bound := r.length
    H := selH r ps o
    A := selA r ps tail o B
    cost := selPass ps
    step := fun j hj => selBody_step r ps hl tail o B j hj
    cont := by
      intro j hj
      simpa [selH, selA] using frame_read_mark r j hj
    halt := by simpa [selH, selA] using frame_read_end r } : Block.WhileBody 3 _)
  have e0 : selH r ps o 0 = ![0, 0, o.length] := by simp [selH, selW, stW]
  have e1 : selA r ps tail o B 0 = ![frame r, stW ps ++ tail, overlay o B] := by simp [selA, selW]
  have t1 : r.take r.length = r := List.take_length
  have t2 : ps.take r.length = ps := by rw [hl]; exact List.take_length
  have e2 : selH r ps o r.length = ![2 * r.length, (stW ps).length, (o ++ selW r ps).length] := by
    simp only [selH, t1, t2]
  have e3 : selA r ps tail o B r.length = ![frame r, stW ps ++ tail, overlay (o ++ selW r ps) B] := by
    simp only [selA, t1, t2]
  have hW' : Step selM (((List.range (r.length - 0)).map fun i => selPass ps (0 + i) + 2).sum + 1)
      (selH r ps o 0) (selA r ps tail o B 0) (selH r ps o r.length) (selA r ps tail o B r.length) := hW
  simp only [Nat.sub_zero, Nat.zero_add] at hW'
  rw [e0, e1, e2, e3] at hW'
  exact hW'

end NearCubicWires.WireExponent3_5.ListMachine.Row
