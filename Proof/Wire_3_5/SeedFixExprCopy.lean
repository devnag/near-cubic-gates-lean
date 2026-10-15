import Proof.Wire_3_5.SeedFixExprMul

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (atomCode monoBits recW polyWord coefWord termWord exprWord)

namespace ExprCopy
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)
open FacCopy (wr mv)

/-- States: `0` the expression level (a term marker, or the terminator: consumed, halt), `1` the coefficient frame
(a marker or its end), `2` a coefficient bit, `3` the factor level (a factor marker, or the term's end), `4` the
polynomial level, `5` a monomial frame, `6` a monomial bit; `7` halts. -/
def machine (cp : Bool) : Machine 2 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 7
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none (wr cp true) .right (mv cp)
      else act 7 none (wr cp false) .right (mv cp))
    else if q.val = 1 then some (if sc 0 then act 2 none (wr cp true) .right (mv cp)
      else act 3 none (wr cp false) .right (mv cp))
    else if q.val = 2 then some (act 1 none (wr cp (sc 0)) .right (mv cp))
    else if q.val = 3 then some (if sc 0 then act 4 none (wr cp true) .right (mv cp)
      else act 0 none (wr cp false) .right (mv cp))
    else if q.val = 4 then some (if sc 0 then act 5 none (wr cp true) .right (mv cp)
      else act 3 none (wr cp false) .right (mv cp))
    else if q.val = 5 then some (if sc 0 then act 6 none (wr cp true) .right (mv cp)
      else act 4 none (wr cp false) .right (mv cp))
    else if q.val = 6 then some (act 5 none (wr cp (sc 0)) .right (mv cp))
    else none

theorem one_step (cp : Bool) (q q' : Fin 8) (A : List Bool) (h : ℕ) (o B : List Bool) (b : Bool)
    (hq7 : q.val ≠ 7)
    (hr : (machine cp).rule q ![readTapeBit A h, readTapeBit (overlay o B) o.length] =
      some (act q' none (wr cp b) .right (mv cp))) :
    Timed (machine cp) 1 (cfg q A (overlay o B) h o.length)
      (cfg q' A (overlay (o ++ owC cp [b]) B) (h + 1) (o ++ owC cp [b]).length) := by
  have hq : (machine cp).halted q = false := by simp [machine, hq7]
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

/-- A frame from state `qm` (markers) with bits in state `qb`, ending in state `qe`. -/
theorem frame_timed (cp : Bool) (qm qb qe : Fin 8) (hm7 : qm.val ≠ 7) (hb7 : qb.val ≠ 7)
    (hT : ∀ y, (machine cp).rule qm ![true, y] = some (act qb none (wr cp true) .right (mv cp)))
    (hF : ∀ y, (machine cp).rule qm ![false, y] = some (act qe none (wr cp false) .right (mv cp)))
    (hB : ∀ x y, (machine cp).rule qb ![x, y] = some (act qm none (wr cp x) .right (mv cp)))
    (tail B : List Bool) : ∀ (w pre o : List Bool),
    Timed (machine cp) (2 * w.length + 1)
      (cfg qm (pre ++ frame w ++ tail) (overlay o B) pre.length o.length)
      (cfg qe (pre ++ frame w ++ tail) (overlay (o ++ owC cp (frame w)) B) (pre.length + (2 * w.length + 1))
        (o ++ owC cp (frame w)).length) := by
  intro w
  induction w with
  | nil =>
    intro pre o
    have hr : readTapeBit (pre ++ frame [] ++ tail) pre.length = false := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre tail false
    have := one_step cp qm qe (pre ++ frame [] ++ tail) pre.length o B false hm7 (by rw [hr]; exact hF _)
    simpa [frame] using this
  | cons b w ih =>
    intro pre o
    have hr : readTapeBit (pre ++ frame (b :: w) ++ tail) pre.length = true := by
      simpa [frame, List.append_assoc] using Streaming.read_append pre (b :: frame w ++ tail) true
    have hb : readTapeBit (pre ++ frame (b :: w) ++ tail) (pre.length + 1) = b := by
      simpa [frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) b
    have t1 := one_step cp qm qb (pre ++ frame (b :: w) ++ tail) pre.length o B true hm7 (by rw [hr]; exact hT _)
    have t2 := one_step cp qb qm (pre ++ frame (b :: w) ++ tail) (pre.length + 1) (o ++ owC cp [true]) B b hb7
      (by rw [hb]; exact hB _ _)
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
      (cfg 4 (pre ++ recW m ++ tail) (overlay o B) pre.length o.length)
      (cfg 4 (pre ++ recW m ++ tail) (overlay (o ++ owC cp (recW m)) B) (pre.length + (recW m).length)
        (o ++ owC cp (recW m)).length) := by
  have hr : readTapeBit (pre ++ recW m ++ tail) pre.length = true := by
    simpa [recW, List.append_assoc] using Streaming.read_append pre (frame (monoBits m) ++ tail) true
  have t1 := one_step cp 4 5 (pre ++ recW m ++ tail) pre.length o B true (by decide) (by rw [hr]; simp [machine])
  have e0 : pre ++ recW m ++ tail = (pre ++ [true]) ++ frame (monoBits m) ++ tail := by simp [recW]
  have t2 := frame_timed cp 5 6 4 (by decide) (by decide) (fun y => by simp [machine]) (fun y => by simp [machine])
    (fun x y => by simp [machine]) tail B (monoBits m) (pre ++ [true]) (o ++ owC cp [true])
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
      (cfg 4 (pre ++ p.flatMap recW ++ tail) (overlay o B) pre.length o.length)
      (cfg 4 (pre ++ p.flatMap recW ++ tail) (overlay (o ++ owC cp (p.flatMap recW)) B)
        (pre.length + (p.flatMap recW).length) (o ++ owC cp (p.flatMap recW)).length) := by
  intro p
  induction p with
  | nil => intro pre o; simpa [owC_nil] using Timed.refl (machine cp) (cfg 4 (pre ++ tail) (overlay o B) pre.length o.length)
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

theorem poly_timed (cp : Bool) (tail B : List Bool) (p : List (List ℕ)) (pre o : List Bool) :
    Timed (machine cp) (polyWord p).length
      (cfg 4 (pre ++ polyWord p ++ tail) (overlay o B) pre.length o.length)
      (cfg 3 (pre ++ polyWord p ++ tail) (overlay (o ++ owC cp (polyWord p)) B) (pre.length + (polyWord p).length)
        (o ++ owC cp (polyWord p)).length) := by
  have e0 : pre ++ polyWord p ++ tail = pre ++ p.flatMap recW ++ (false :: tail) := by simp [polyWord]
  have t1 := recs_timed cp (false :: tail) B p pre o
  have hr : readTapeBit (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length) = false := by
    simpa [List.append_assoc] using Streaming.read_append (pre ++ p.flatMap recW) tail false
  have t2 := one_step cp 4 3 (pre ++ p.flatMap recW ++ (false :: tail)) (pre.length + (p.flatMap recW).length)
    (o ++ owC cp (p.flatMap recW)) B false (by decide) (by rw [hr]; simp [machine])
  have t := t1.trans t2
  rw [← e0] at t
  have e2 : o ++ owC cp (p.flatMap recW) ++ owC cp [false] = o ++ owC cp (polyWord p) := by
    rw [List.append_assoc, owC_append]; simp [polyWord]
  rw [e2, show (p.flatMap recW).length + 1 = (polyWord p).length by simp [polyWord],
    show pre.length + (p.flatMap recW).length + 1 = pre.length + (polyWord p).length by simp [polyWord]; omega] at t
  exact t

theorem fac_timed (cp : Bool) (tail B : List Bool) (f : List (List ℕ)) (pre o : List Bool) :
    Timed (machine cp) (facRec f).length
      (cfg 3 (pre ++ facRec f ++ tail) (overlay o B) pre.length o.length)
      (cfg 3 (pre ++ facRec f ++ tail) (overlay (o ++ owC cp (facRec f)) B) (pre.length + (facRec f).length)
        (o ++ owC cp (facRec f)).length) := by
  have hr : readTapeBit (pre ++ facRec f ++ tail) pre.length = true := by
    simpa [facRec, List.append_assoc] using Streaming.read_append pre (polyWord f ++ tail) true
  have t1 := one_step cp 3 4 (pre ++ facRec f ++ tail) pre.length o B true (by decide) (by rw [hr]; simp [machine])
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
      (cfg 3 (pre ++ facRecs fs ++ tail) (overlay o B) pre.length o.length)
      (cfg 3 (pre ++ facRecs fs ++ tail) (overlay (o ++ owC cp (facRecs fs)) B)
        (pre.length + (facRecs fs).length) (o ++ owC cp (facRecs fs)).length) := by
  intro fs
  induction fs with
  | nil => intro pre o; simpa [facRecs, owC_nil] using Timed.refl (machine cp) (cfg 3 (pre ++ tail) (overlay o B) pre.length o.length)
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

/-- A term record `true :: termWord t`, from and back to the expression level. -/
theorem term_timed (cp : Bool) (tail B : List Bool) (t : ℤ × List (List (List ℕ))) (pre o : List Bool) :
    Timed (machine cp) (recT t).length
      (cfg 0 (pre ++ recT t ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ recT t ++ tail) (overlay (o ++ owC cp (recT t)) B) (pre.length + (recT t).length)
        (o ++ owC cp (recT t)).length) := by
  set w := decide (t.1 < 0) :: Nat.bits t.1.natAbs
  have eR : recT t = [true] ++ frame w ++ facRecs t.2 ++ [false] := by
    simp [recT, termWord_eq, coefWord, w, List.append_assoc]
  set S := pre ++ recT t ++ tail
  have eS : S = pre ++ [true] ++ frame w ++ facRecs t.2 ++ (false :: tail) := by simp [S, eR]
  have hr0 : readTapeBit S pre.length = true := by
    rw [eS]; simpa [List.append_assoc] using Streaming.read_append pre (frame w ++ facRecs t.2 ++ false :: tail) true
  have t1 := one_step cp 0 1 S pre.length o B true (by decide) (by rw [hr0]; simp [machine])
  have t2 := frame_timed cp 1 2 3 (by decide) (by decide) (fun y => by simp [machine]) (fun y => by simp [machine])
    (fun x y => by simp [machine]) (facRecs t.2 ++ false :: tail) B w (pre ++ [true]) (o ++ owC cp [true])
  have eS2 : pre ++ [true] ++ frame w ++ (facRecs t.2 ++ false :: tail) = S := by rw [eS]; simp
  rw [eS2] at t2
  have t3 := facs_timed cp (false :: tail) B t.2 (pre ++ [true] ++ frame w) (o ++ owC cp [true] ++ owC cp (frame w))
  have eS3 : pre ++ [true] ++ frame w ++ facRecs t.2 ++ false :: tail = S := by rw [eS]
  rw [eS3] at t3
  have hr4 : readTapeBit S (pre ++ [true] ++ frame w ++ facRecs t.2).length = false := by
    rw [eS]; simpa [List.append_assoc] using Streaming.read_append (pre ++ [true] ++ frame w ++ facRecs t.2) tail false
  have t4 := one_step cp 3 0 S (pre ++ [true] ++ frame w ++ facRecs t.2).length
    (o ++ owC cp [true] ++ owC cp (frame w) ++ owC cp (facRecs t.2)) B false (by decide) (by rw [hr4]; simp [machine])
  have eL1 : (pre ++ [true]).length = pre.length + 1 := by simp
  have eL3 : (pre ++ [true] ++ frame w).length = pre.length + 1 + (2 * w.length + 1) := by simp [frame_length]; omega
  rw [eL1] at t2
  rw [eL3] at t3
  have eL4 : (pre ++ [true] ++ frame w ++ facRecs t.2).length = pre.length + 1 + (2 * w.length + 1) + (facRecs t.2).length := by
    simp [frame_length]; omega
  rw [eL4] at t4
  have hT := ((t1.trans t2).trans t3).trans t4
  have eO : o ++ owC cp [true] ++ owC cp (frame w) ++ owC cp (facRecs t.2) ++ owC cp [false] = o ++ owC cp (recT t) := by
    simp only [List.append_assoc, owC_append, eR]
  have eN : (recT t).length = 1 + (2 * w.length + 1) + (facRecs t.2).length + 1 := by
    rw [eR]; simp [frame_length]; omega
  rw [eO, show pre.length + 1 + (2 * w.length + 1) + (facRecs t.2).length + 1 = pre.length + (recT t).length by
    rw [eN]; omega, show 1 + (2 * w.length + 1) + (facRecs t.2).length + 1 = (recT t).length from eN.symm] at hT
  exact hT

theorem terms_timed (cp : Bool) (tail B : List Bool) : ∀ (V : List (ℤ × List (List (List ℕ)))) (pre o : List Bool),
    Timed (machine cp) (V.flatMap recT).length
      (cfg 0 (pre ++ V.flatMap recT ++ tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ V.flatMap recT ++ tail) (overlay (o ++ owC cp (V.flatMap recT)) B)
        (pre.length + (V.flatMap recT).length) (o ++ owC cp (V.flatMap recT)).length) := by
  intro V
  induction V with
  | nil => intro pre o; simpa [owC_nil] using Timed.refl (machine cp) (cfg 0 (pre ++ tail) (overlay o B) pre.length o.length)
  | cons t V ih =>
    intro pre o
    have t1 := term_timed cp (V.flatMap recT ++ tail) B t pre o
    have e0 : pre ++ (t :: V).flatMap recT ++ tail = pre ++ recT t ++ (V.flatMap recT ++ tail) := by simp
    rw [← e0] at t1
    have t2 := ih (pre ++ recT t) (o ++ owC cp (recT t))
    have e1 : pre ++ recT t ++ V.flatMap recT ++ tail = pre ++ (t :: V).flatMap recT ++ tail := by simp
    rw [e1] at t2
    have e2 : o ++ owC cp (recT t) ++ owC cp (V.flatMap recT) = o ++ owC cp ((t :: V).flatMap recT) := by
      rw [List.append_assoc, owC_append]; simp
    have e3 : (pre ++ recT t).length = pre.length + (recT t).length := by simp
    rw [e3] at t2
    rw [e2, show pre.length + (recT t).length + (V.flatMap recT).length = pre.length + ((t :: V).flatMap recT).length by
      simp; omega] at t2
    have := t1.trans t2
    rwa [show (recT t).length + (V.flatMap recT).length = ((t :: V).flatMap recT).length by simp] at this

/-- **Copy or pass a printed expression**, its terminator consumed. -/
theorem run (cp : Bool) (pre : List Bool) (V : List (ℤ × List (List (List ℕ)))) (tail o B : List Bool) :
    Step (machine cp) (exprWord V).length ![pre.length, o.length] ![pre ++ exprWord V ++ tail, overlay o B]
      ![pre.length + (exprWord V).length, (o ++ owC cp (exprWord V)).length]
      ![pre ++ exprWord V ++ tail, overlay (o ++ owC cp (exprWord V)) B] := by
  have e0 : pre ++ exprWord V ++ tail = pre ++ V.flatMap recT ++ (false :: tail) := by simp [exprWord_eq]
  have t1 := terms_timed cp (false :: tail) B V pre o
  have hr : readTapeBit (pre ++ V.flatMap recT ++ (false :: tail)) (pre.length + (V.flatMap recT).length) = false := by
    simpa [List.append_assoc] using Streaming.read_append (pre ++ V.flatMap recT) tail false
  have t2 := one_step cp 0 7 (pre ++ V.flatMap recT ++ (false :: tail)) (pre.length + (V.flatMap recT).length)
    (o ++ owC cp (V.flatMap recT)) B false (by decide) (by rw [hr]; simp [machine])
  have t := t1.trans t2
  rw [← e0] at t
  have e2 : o ++ owC cp (V.flatMap recT) ++ owC cp [false] = o ++ owC cp (exprWord V) := by
    rw [List.append_assoc, owC_append]; simp [exprWord_eq]
  rw [e2, show (V.flatMap recT).length + 1 = (exprWord V).length by simp [exprWord_eq],
    show pre.length + (V.flatMap recT).length + 1 = pre.length + (exprWord V).length by simp [exprWord_eq]; omega] at t
  obtain ⟨r, hr', hf, hs⟩ := t.run rfl
  exact ⟨r, hr', by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end ExprCopy

end NearCubicWires.WireExponent3_5.SeedFix
