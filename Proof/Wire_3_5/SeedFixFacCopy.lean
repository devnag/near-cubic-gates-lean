import Proof.Wire_3_5.GF2Machines
import Proof.Wire_3_5.ListMachineEncoding

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (atomCode monoBits recW polyWord)

/-- What the output receives: the word when copying, nothing when passing. -/
def owC (cp : Bool) (w : List Bool) : List Bool := if cp then w else []

theorem owC_append (cp : Bool) (x y : List Bool) : owC cp x ++ owC cp y = owC cp (x ++ y) := by
  cases cp <;> simp [owC]

theorem owC_nil (cp : Bool) : owC cp [] = [] := by cases cp <;> rfl

/-- A factor record: a marker, then the printed polynomial. -/
def facRec (f : List (List ℕ)) : List Bool := true :: polyWord f

/-- A term's factor records. -/
def facRecs (fs : List (List (List ℕ))) : List Bool := fs.flatMap facRec

namespace FacCopy
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

def wr (cp b : Bool) : Option Bool := if cp then some b else none
def mv (cp : Bool) : HeadMove := if cp then .right else .stay

/-- State `0` at a factor marker or the records' terminator (halt, not consumed), `1` at a monomial marker or the
polynomial's end, `2` at a frame marker or the frame's end, `3` at a frame bit; `4` halts. -/
def machine (cp : Bool) : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none (wr cp true) .right (mv cp) else act 4 none none .stay .stay)
    else if q.val = 1 then some (if sc 0 then act 2 none (wr cp true) .right (mv cp)
      else act 0 none (wr cp false) .right (mv cp))
    else if q.val = 2 then some (if sc 0 then act 3 none (wr cp true) .right (mv cp)
      else act 1 none (wr cp false) .right (mv cp))
    else if q.val = 3 then some (act 2 none (wr cp (sc 0)) .right (mv cp))
    else none

theorem rule0 (cp x y : Bool) : (machine cp).rule 0 ![x, y] =
    some (if x then act 1 none (wr cp true) .right (mv cp) else act 4 none none .stay .stay) := by
  simp [machine]
theorem rule1 (cp x y : Bool) : (machine cp).rule 1 ![x, y] =
    some (if x then act 2 none (wr cp true) .right (mv cp) else act 0 none (wr cp false) .right (mv cp)) := by
  simp [machine]
theorem rule2 (cp x y : Bool) : (machine cp).rule 2 ![x, y] =
    some (if x then act 3 none (wr cp true) .right (mv cp) else act 1 none (wr cp false) .right (mv cp)) := by
  simp [machine]
theorem rule3 (cp x y : Bool) : (machine cp).rule 3 ![x, y] = some (act 2 none (wr cp x) .right (mv cp)) := by
  simp [machine]

theorem one_step (cp : Bool) (q q' : Fin 5) (A : List Bool) (h : ℕ) (o B : List Bool) (b : Bool)
    (hr : (machine cp).rule q ![readTapeBit A h, readTapeBit (overlay o B) o.length] =
      some (act q' none (wr cp b) .right (mv cp))) :
    Timed (machine cp) 1 (cfg q A (overlay o B) h o.length)
      (cfg q' A (overlay (o ++ owC cp [b]) B) (h + 1) (o ++ owC cp [b]).length) := by
  have hq : (machine cp).halted q = false := by
    have : q.val ≠ 4 := by
      intro e
      have : q = 4 := Fin.ext e
      subst this; simp [machine] at hr
    simp [machine, this]
  have s := NearCubicWires.WireExponent3_5.GF2.Two.step_cfg (machine cp) q q' A (overlay o B) h o.length none
    (wr cp b) .right (mv cp) hr
  cases cp
  · simp only [wr, mv, NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, Bool.false_eq_true,
      if_false] at s
    simpa [owC] using Timed.single (p := machine false) hq s
  · simp only [wr, mv, NearCubicWires.WireExponent3_5.GF2.Two.wr, HeadMove.apply, if_true, overlay_write] at s
    have e : (o ++ [b]).length = o.length + 1 := by simp
    rw [← e] at s
    simpa [owC] using Timed.single (p := machine true) hq s

theorem frame_timed (cp : Bool) (tail B : List Bool) : ∀ (w pre o : List Bool),
    Timed (machine cp) (2 * w.length + 1)
      (cfg 2 (pre ++ frame w ++ tail) (overlay o B) pre.length o.length)
      (cfg 1 (pre ++ frame w ++ tail) (overlay (o ++ owC cp (frame w)) B) (pre.length + (2 * w.length + 1))
        (o ++ owC cp (frame w)).length) := by
  intro w
  induction w with
  | nil =>
    intro pre o
    have hr : readTapeBit (pre ++ frame [] ++ tail) pre.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre tail false
    have := one_step cp 2 1 (pre ++ frame [] ++ tail) pre.length o B false (by rw [rule2, hr]; simp)
    simpa [frame] using this
  | cons b w ih =>
    intro pre o
    have hr : readTapeBit (pre ++ frame (b :: w) ++ tail) pre.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre (b :: frame w ++ tail) true
    have hb : readTapeBit (pre ++ frame (b :: w) ++ tail) (pre.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) b
    have t1 := one_step cp 2 3 (pre ++ frame (b :: w) ++ tail) pre.length o B true (by rw [rule2, hr]; simp)
    have t2 := one_step cp 3 2 (pre ++ frame (b :: w) ++ tail) (pre.length + 1) (o ++ owC cp [true]) B b
      (by rw [rule3, hb])
    have e0 : pre ++ frame (b :: w) ++ tail = (pre ++ [true, b]) ++ frame w ++ tail := by
      simp [frame, List.append_assoc]
    have t3 := ih (pre ++ [true, b]) (o ++ owC cp [true] ++ owC cp [b])
    rw [← e0] at t3
    have e1 : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    have e2 : o ++ owC cp [true] ++ owC cp [b] ++ owC cp (frame w) = o ++ owC cp (frame (b :: w)) := by
      rw [List.append_assoc, List.append_assoc, owC_append, owC_append]; simp [frame]
    rw [e1, e2, show pre.length + 1 + 1 + (2 * w.length + 1) = pre.length + (2 * (b :: w).length + 1) by
      simp; omega] at t3
    have := (t1.trans t2).trans t3
    rwa [show 1 + 1 + (2 * w.length + 1) = 2 * (b :: w).length + 1 by simp; omega] at this

theorem rec_timed (cp : Bool) (tail B : List Bool) (m : List ℕ) (pre o : List Bool) :
    Timed (machine cp) (recW m).length
      (cfg 1 (pre ++ recW m ++ tail) (overlay o B) pre.length o.length)
      (cfg 1 (pre ++ recW m ++ tail) (overlay (o ++ owC cp (recW m)) B) (pre.length + (recW m).length)
        (o ++ owC cp (recW m)).length) := by
  have hr : readTapeBit (pre ++ recW m ++ tail) pre.length = true := by
    simpa [recW, List.append_assoc] using Streaming.read_append pre (frame (monoBits m) ++ tail) true
  have t1 := one_step cp 1 2 (pre ++ recW m ++ tail) pre.length o B true (by rw [rule1, hr]; simp)
  have e0 : pre ++ recW m ++ tail = (pre ++ [true]) ++ frame (monoBits m) ++ tail := by simp [recW]
  have t2 := frame_timed cp tail B (monoBits m) (pre ++ [true]) (o ++ owC cp [true])
  rw [← e0] at t2
  have e2 : o ++ owC cp [true] ++ owC cp (frame (monoBits m)) = o ++ owC cp (recW m) := by
    rw [List.append_assoc, owC_append]; simp [recW]
  have e3 : (pre ++ [true]).length = pre.length + 1 := by simp
  rw [e3] at t2
  rw [e2, show pre.length + 1 + (2 * (monoBits m).length + 1) = pre.length + (recW m).length by
    simp [ListMachine.Rec.recW_length]; omega] at t2
  have := t1.trans t2
  rwa [show 1 + (2 * (monoBits m).length + 1) = (recW m).length by simp [ListMachine.Rec.recW_length]; omega] at this

theorem recs_timed (cp : Bool) (tail B : List Bool) : ∀ (p : List (List ℕ)) (pre o : List Bool),
    Timed (machine cp) (p.flatMap recW).length
      (cfg 1 (pre ++ p.flatMap recW ++ tail) (overlay o B) pre.length o.length)
      (cfg 1 (pre ++ p.flatMap recW ++ tail) (overlay (o ++ owC cp (p.flatMap recW)) B)
        (pre.length + (p.flatMap recW).length) (o ++ owC cp (p.flatMap recW)).length) := by
  intro p
  induction p with
  | nil => intro pre o; simpa [owC_nil] using Timed.refl (machine cp) (cfg 1 (pre ++ tail) (overlay o B) pre.length o.length)
  | cons m p ih =>
    intro pre o
    have t1 := rec_timed cp (p.flatMap recW ++ tail) B m pre o
    have e0 : pre ++ (m :: p).flatMap recW ++ tail = pre ++ recW m ++ (p.flatMap recW ++ tail) := by simp
    rw [← e0] at t1
    have t2 := ih (pre ++ recW m) (o ++ owC cp (recW m))
    have e1 : pre ++ recW m ++ p.flatMap recW ++ tail = pre ++ (m :: p).flatMap recW ++ tail := by simp
    rw [e1] at t2
    have e2 : o ++ owC cp (recW m) ++ owC cp (p.flatMap recW) = o ++ owC cp ((m :: p).flatMap recW) := by
      rw [List.append_assoc, owC_append]; simp
    have e3 : (pre ++ recW m).length = pre.length + (recW m).length := by simp
    rw [e3] at t2
    rw [e2, show pre.length + (recW m).length + (p.flatMap recW).length = pre.length + ((m :: p).flatMap recW).length by
      simp; omega] at t2
    have := t1.trans t2
    rwa [show (recW m).length + (p.flatMap recW).length = ((m :: p).flatMap recW).length by simp] at this

/-- A printed polynomial, from state `1` back to the factor level `0`. -/
theorem poly_timed (cp : Bool) (tail B : List Bool) (p : List (List ℕ)) (pre o : List Bool) :
    Timed (machine cp) (polyWord p).length
      (cfg 1 (pre ++ polyWord p ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ polyWord p ++ tail) (overlay (o ++ owC cp (polyWord p)) B) (pre.length + (polyWord p).length)
        (o ++ owC cp (polyWord p)).length) := by
  have e0 : pre ++ polyWord p ++ tail = pre ++ p.flatMap recW ++ (false :: tail) := by simp [polyWord]
  have t1 := recs_timed cp (false :: tail) B p pre o
  have hr : readTapeBit (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length) = false := by
    simpa [List.append_assoc] using Streaming.read_append (pre ++ p.flatMap recW) tail false
  have t2 := one_step cp 1 0 (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length)
    (o ++ owC cp (p.flatMap recW)) B false (by rw [rule1, hr]; simp)
  have t := t1.trans t2
  rw [← e0] at t
  have e2 : o ++ owC cp (p.flatMap recW) ++ owC cp [false] = o ++ owC cp (polyWord p) := by
    rw [List.append_assoc, owC_append]; simp [polyWord]
  rw [e2, show (p.flatMap recW).length + 1 = (polyWord p).length by simp [polyWord],
    show pre.length + (p.flatMap recW).length + 1 = pre.length + (polyWord p).length by simp [polyWord]; omega] at t
  exact t

theorem fac_timed (cp : Bool) (tail B : List Bool) (f : List (List ℕ)) (pre o : List Bool) :
    Timed (machine cp) (facRec f).length
      (cfg 0 (pre ++ facRec f ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ facRec f ++ tail) (overlay (o ++ owC cp (facRec f)) B) (pre.length + (facRec f).length)
        (o ++ owC cp (facRec f)).length) := by
  have hr : readTapeBit (pre ++ facRec f ++ tail) pre.length = true := by
    simpa [facRec, List.append_assoc] using Streaming.read_append pre (polyWord f ++ tail) true
  have t1 := one_step cp 0 1 (pre ++ facRec f ++ tail) pre.length o B true (by rw [rule0, hr]; simp)
  have e0 : pre ++ facRec f ++ tail = (pre ++ [true]) ++ polyWord f ++ tail := by simp [facRec]
  have t2 := poly_timed cp tail B f (pre ++ [true]) (o ++ owC cp [true])
  rw [← e0] at t2
  have e2 : o ++ owC cp [true] ++ owC cp (polyWord f) = o ++ owC cp (facRec f) := by
    rw [List.append_assoc, owC_append]; simp [facRec]
  have e3 : (pre ++ [true]).length = pre.length + 1 := by simp
  rw [e3, e2, show pre.length + 1 + (polyWord f).length = pre.length + (facRec f).length by simp [facRec]; omega] at t2
  have := t1.trans t2
  rwa [show 1 + (polyWord f).length = (facRec f).length by simp [facRec]; omega] at this

theorem facs_timed (cp : Bool) (tail B : List Bool) : ∀ (fs : List (List (List ℕ))) (pre o : List Bool),
    Timed (machine cp) (facRecs fs).length
      (cfg 0 (pre ++ facRecs fs ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ facRecs fs ++ tail) (overlay (o ++ owC cp (facRecs fs)) B)
        (pre.length + (facRecs fs).length) (o ++ owC cp (facRecs fs)).length) := by
  intro fs
  induction fs with
  | nil => intro pre o; simpa [facRecs, owC_nil] using Timed.refl (machine cp) (cfg 0 (pre ++ tail) (overlay o B) pre.length o.length)
  | cons f fs ih =>
    intro pre o
    have t1 := fac_timed cp (facRecs fs ++ tail) B f pre o
    have e0 : pre ++ facRecs (f :: fs) ++ tail = pre ++ facRec f ++ (facRecs fs ++ tail) := by simp [facRecs]
    rw [← e0] at t1
    have t2 := ih (pre ++ facRec f) (o ++ owC cp (facRec f))
    have e1 : pre ++ facRec f ++ facRecs fs ++ tail = pre ++ facRecs (f :: fs) ++ tail := by simp [facRecs]
    rw [e1] at t2
    have e2 : o ++ owC cp (facRec f) ++ owC cp (facRecs fs) = o ++ owC cp (facRecs (f :: fs)) := by
      rw [List.append_assoc, owC_append]; simp [facRecs]
    have e3 : (pre ++ facRec f).length = pre.length + (facRec f).length := by simp
    rw [e3] at t2
    rw [e2, show pre.length + (facRec f).length + (facRecs fs).length = pre.length + (facRecs (f :: fs)).length by
      simp [facRecs]; omega] at t2
    have := t1.trans t2
    rwa [show (facRec f).length + (facRecs fs).length = (facRecs (f :: fs)).length by simp [facRecs]] at this

/-- **Copy or pass a term's factor records**, stopping on their terminator. -/
theorem run (cp : Bool) (pre : List Bool) (fs : List (List (List ℕ))) (tail o B : List Bool) :
    Step (machine cp) ((facRecs fs).length + 1) ![pre.length, o.length]
      ![pre ++ facRecs fs ++ false :: tail, overlay o B]
      ![pre.length + (facRecs fs).length, (o ++ owC cp (facRecs fs)).length]
      ![pre ++ facRecs fs ++ false :: tail, overlay (o ++ owC cp (facRecs fs)) B] := by
  have t1 := facs_timed cp (false :: tail) B fs pre o
  have hr : readTapeBit (pre ++ facRecs fs ++ false :: tail) (pre.length + (facRecs fs).length) = false := by
    simpa [List.append_assoc] using Streaming.read_append (pre ++ facRecs fs) tail false
  have hs : step (machine cp) (cfg 0 (pre ++ facRecs fs ++ false :: tail) (overlay (o ++ owC cp (facRecs fs)) B)
        (pre.length + (facRecs fs).length) (o ++ owC cp (facRecs fs)).length) =
      some (cfg 4 (pre ++ facRecs fs ++ false :: tail) (overlay (o ++ owC cp (facRecs fs)) B)
        (pre.length + (facRecs fs).length) (o ++ owC cp (facRecs fs)).length) := by
    rw [NearCubicWires.WireExponent3_5.GF2.Two.step_cfg (machine cp) 0 4 _ _ _ _ none none .stay .stay
      (by rw [rule0, hr]; simp)]
    rfl
  have t2 := Timed.single (p := machine cp) rfl hs
  obtain ⟨r, hr', hf, hs'⟩ := (t1.trans t2).run rfl
  refine ⟨r, ?_, ?_, ?_, by omega⟩
  · exact hr'
  · rw [hf]; rfl
  · rw [hf]; rfl

end FacCopy

end NearCubicWires.WireExponent3_5.SeedFix
