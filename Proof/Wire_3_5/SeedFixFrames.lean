import Proof.Wire_3_5.SeedFixCoef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

/-- The pairs of a framed word (`frame w = pairsOf w ++ [false]`). -/
def pairsOf (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

theorem frame_pairs (w : List Bool) : frame w = pairsOf w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, pairsOf, ih]

theorem pairsOf_length (w : List Bool) : (pairsOf w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [pairsOf, List.flatMap_cons, List.length_append] at ih ⊢; rw [ih]; simp; ring

theorem pairsOf_append (u v : List Bool) : pairsOf (u ++ v) = pairsOf u ++ pairsOf v := by
  simp [pairsOf]

/-! ## `PairsC cp`: a framed word's pairs, copied or passed, stopping on its terminator -/

namespace PairsC
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)
open FacCopy (wr mv)

/-- State `0` at a marker (copy it) or the terminator (halt, not consumed), `1` at a bit. -/
def machine (cp : Bool) : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then act 1 none (wr cp true) .right (mv cp) else act 2 none none .stay .stay)
    else if q.val = 1 then some (act 0 none (wr cp (sc 0)) .right (mv cp))
    else none

theorem one_step (cp : Bool) (q q' : Fin 3) (A : List Bool) (h : ℕ) (o B : List Bool) (b : Bool) (hq2 : q.val ≠ 2)
    (hr : (machine cp).rule q ![readTapeBit A h, readTapeBit (overlay o B) o.length] =
      some (act q' none (wr cp b) .right (mv cp))) :
    Timed (machine cp) 1 (cfg q A (overlay o B) h o.length)
      (cfg q' A (overlay (o ++ owC cp [b]) B) (h + 1) (o ++ owC cp [b]).length) := by
  have hq : (machine cp).halted q = false := by simp [machine, hq2]
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

theorem timed (cp : Bool) (tail B : List Bool) : ∀ (w pre o : List Bool),
    Timed (machine cp) (2 * w.length)
      (cfg 0 (pre ++ pairsOf w ++ false :: tail) (overlay o B) pre.length o.length)
      (cfg 0 (pre ++ pairsOf w ++ false :: tail) (overlay (o ++ owC cp (pairsOf w)) B) (pre.length + 2 * w.length)
        (o ++ owC cp (pairsOf w)).length) := by
  intro w
  induction w with
  | nil => intro pre o; simpa [pairsOf, owC_nil] using Timed.refl (machine cp) (cfg 0 (pre ++ false :: tail) (overlay o B) pre.length o.length)
  | cons b w ih =>
    intro pre o
    set S := pre ++ pairsOf (b :: w) ++ false :: tail
    have eS : S = (pre ++ [true, b]) ++ pairsOf w ++ false :: tail := by simp [S, pairsOf]
    have hr : readTapeBit S pre.length = true := by
      rw [eS]; simpa [List.append_assoc] using Streaming.read_append pre (b :: (pairsOf w ++ false :: tail)) true
    have hb : readTapeBit S (pre.length + 1) = b := by
      rw [eS]; simpa [List.append_assoc] using Streaming.read_append (pre ++ [true]) (pairsOf w ++ false :: tail) b
    have t1 := one_step cp 0 1 S pre.length o B true (by decide) (by rw [hr]; simp [machine])
    have t2 := one_step cp 1 0 S (pre.length + 1) (o ++ owC cp [true]) B b (by decide) (by rw [hb]; simp [machine])
    have t3 := ih (pre ++ [true, b]) (o ++ owC cp [true] ++ owC cp [b])
    rw [← eS] at t3
    have e1 : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    have e2 : o ++ owC cp [true] ++ owC cp [b] ++ owC cp (pairsOf w) = o ++ owC cp (pairsOf (b :: w)) := by
      rw [List.append_assoc, List.append_assoc, owC_append, owC_append]; simp [pairsOf]
    rw [e1, e2, show pre.length + 1 + 1 + 2 * w.length = pre.length + 2 * (b :: w).length by simp; omega] at t3
    have := (t1.trans t2).trans t3
    rwa [show 1 + 1 + 2 * w.length = 2 * (b :: w).length by simp; omega] at this

/-- **A framed word's pairs, copied or passed**, the source head stopping on the terminator. -/
theorem run (cp : Bool) (pre w tail o B : List Bool) :
    Step (machine cp) (2 * w.length + 1) ![pre.length, o.length] ![pre ++ frame w ++ tail, overlay o B]
      ![pre.length + 2 * w.length, (o ++ owC cp (pairsOf w)).length]
      ![pre ++ frame w ++ tail, overlay (o ++ owC cp (pairsOf w)) B] := by
  have eS : pre ++ frame w ++ tail = pre ++ pairsOf w ++ false :: tail := by simp [frame_pairs]
  have t1 := timed cp tail B w pre o
  rw [← eS] at t1
  have hr : readTapeBit (pre ++ frame w ++ tail) (pre.length + 2 * w.length) = false := by
    rw [eS, show pre.length + 2 * w.length = (pre ++ pairsOf w).length by simp [pairsOf_length]]
    simpa [List.append_assoc] using Streaming.read_append (pre ++ pairsOf w) tail false
  have hs : step (machine cp) (cfg 0 (pre ++ frame w ++ tail) (overlay (o ++ owC cp (pairsOf w)) B)
        (pre.length + 2 * w.length) (o ++ owC cp (pairsOf w)).length) =
      some (cfg 2 (pre ++ frame w ++ tail) (overlay (o ++ owC cp (pairsOf w)) B)
        (pre.length + 2 * w.length) (o ++ owC cp (pairsOf w)).length) := by
    rw [NearCubicWires.WireExponent3_5.GF2.Two.step_cfg (machine cp) 0 2 _ _ _ _ none none .stay .stay
      (by rw [hr]; simp [machine])]
    rfl
  obtain ⟨r, hr', hf, hs'⟩ := (t1.trans (Timed.single (p := machine cp) rfl hs)).run rfl
  exact ⟨r, hr', by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end PairsC

/-! ## Whole framed words -/

/-- Copy a framed word, both heads past its terminator. -/
noncomputable def frameT := Composition.machine (PairsC.machine true) CopyCell.machine

theorem frameT_run (pre w tail o B : List Bool) :
    Step frameT (2 * w.length + 1 + 1 + 1) ![pre.length, o.length] ![pre ++ frame w ++ tail, overlay o B]
      ![pre.length + (frame w).length, (o ++ frame w).length] ![pre ++ frame w ++ tail, overlay (o ++ frame w) B] := by
  have h1 := PairsC.run true pre w tail o B
  simp only [owC, if_true] at h1
  have hr : readTapeBit (pre ++ frame w ++ tail) (pre.length + 2 * w.length) = false := by
    rw [frame_pairs, show pre.length + 2 * w.length = (pre ++ pairsOf w).length by simp [pairsOf_length]]
    simpa [List.append_assoc] using Streaming.read_append (pre ++ pairsOf w) tail false
  have h2 := CopyCell.run (pre ++ frame w ++ tail) (pre.length + 2 * w.length) (o ++ pairsOf w) B
  rw [hr] at h2
  have hall := h1.seq (h2.congr_in (by funext j; fin_cases j <;> rfl) rfl)
  have eW : o ++ pairsOf w ++ [false] = o ++ frame w := by rw [frame_pairs]; simp
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · show pre.length + 2 * w.length + 1 = pre.length + (frame w).length; simp [frame_length]; omega
    · show (o ++ pairsOf w).length + 1 = (o ++ frame w).length; rw [← eW]; simp; omega
  · funext j; fin_cases j
    · rfl
    · show overlay (o ++ pairsOf w ++ [false]) B = overlay (o ++ frame w) B; rw [eW]

def s2Src : Fin 1 → Fin 2 := ![0]

theorem dockH_s2Src (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) : dockH s2Src H v = ![v 0, H 1] := by
  funext i; fin_cases i
  · exact dockH_slot _ (by decide) _ _ 0
  · exact dockH_other _ _ _ _ (by decide)

theorem install_s2Src (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install s2Src A v = ![v 0, A 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)

/-- Pass a framed word, the source head past its terminator. -/
noncomputable def frameP := Composition.machine (PairsC.machine false) (RecoveryFocus.machine s2Src nudgeM)

theorem frameP_run (pre w tail o B : List Bool) :
    Step frameP (2 * w.length + 1 + 1 + 1) ![pre.length, o.length] ![pre ++ frame w ++ tail, overlay o B]
      ![pre.length + (frame w).length, o.length] ![pre ++ frame w ++ tail, overlay o B] := by
  have h1 := PairsC.run false pre w tail o B
  simp only [owC, Bool.false_eq_true, if_false, List.append_nil] at h1
  have h2 := dockRun (nudge_run (pre ++ frame w ++ tail) (pre.length + 2 * w.length)) s2Src (by decide)
    ![pre.length + 2 * w.length, o.length] ![pre ++ frame w ++ tail, overlay o B]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_s2Src, install_s2Src] at h2
  have hall := h1.seq (h2.congr (hout' := ![pre.length + 2 * w.length + 1, o.length])
    (tout' := ![pre ++ frame w ++ tail, overlay o B]) (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))
  refine hall.congr ?_ rfl
  funext j; fin_cases j
  · show pre.length + 2 * w.length + 1 = pre.length + (frame w).length; simp [frame_length]; omega
  · rfl

/-! ## A counter field into a framed word -/

namespace BitPair
open NearCubicWires.WireExponent3_5.GF2.Three (act cfg)

/-- Tapes `0` the ruler, `1` the source, `2` the output: append `true`, then the source bit; step ruler and source. -/
def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none none (some true) .stay .stay .right)
    else if q.val = 1 then some (act 2 none none (some (sc 1)) .right .right .right)
    else none

theorem run (U S : List Bool) (hu hs : ℕ) (o B : List Bool) :
    Step machine 2 ![hu, hs, o.length] ![U, S, overlay o B] ![hu + 1, hs + 1, o.length + 2]
      ![U, S, overlay (o ++ [true, readTapeBit S hs]) B] := by
  set b := readTapeBit S hs
  have s1 : step machine (cfg 0 U S (overlay o B) hu hs o.length) =
      some (cfg 1 U S (overlay (o ++ [true]) B) hu hs (o.length + 1)) := by
    rw [Three.step_cfg machine 0 1 U S (overlay o B) hu hs o.length none none (some true) .stay .stay .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply, overlay_write]
  have s2 : step machine (cfg 1 U S (overlay (o ++ [true]) B) hu hs (o.length + 1)) =
      some (cfg 2 U S (overlay (o ++ [true, b]) B) (hu + 1) (hs + 1) (o.length + 2)) := by
    rw [Three.step_cfg machine 1 2 U S (overlay (o ++ [true]) B) hu hs (o.length + 1) none none (some b)
      .right .right .right (by simp [machine, b])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true]) B b
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  obtain ⟨r, hr, hf, hs'⟩ := ((Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end BitPair

noncomputable def bitsLoopM := StreamController.machine BitPair.machine 0

def bitsH (pre o bits : List Bool) (i : ℕ) : Fin 3 → ℕ := ![i, pre.length + i, (o ++ pairsOf (bits.take i)).length]
def bitsA (U S o B bits : List Bool) (i : ℕ) : Fin 3 → List Bool := ![U, S, overlay (o ++ pairsOf (bits.take i)) B]

/-- **A field of `r` source bits as a word's pairs**, along a unit ruler of `r` cells. -/
theorem bitsLoop_run (r : ℕ) (rus pre bits post o B : List Bool) (hb : bits.length = r) :
    Step bitsLoopM (r * (2 + 2) + 1) ![0, pre.length, o.length]
      ![List.replicate r true ++ false :: rus, pre ++ bits ++ post, overlay o B]
      ![r, pre.length + r, (o ++ pairsOf bits).length]
      ![List.replicate r true ++ false :: rus, pre ++ bits ++ post, overlay (o ++ pairsOf bits) B] := by
  set U := List.replicate r true ++ false :: rus
  set S := pre ++ bits ++ post
  have hread : ∀ i, i < r → readTapeBit S (pre.length + i) = bits.getD i false := by
    intro i hi
    have hi' : i < bits.length := by omega
    have eb : bits = bits.take i ++ bits[i] :: bits.drop (i + 1) := by
      rw [← List.drop_eq_getElem_cons hi', List.take_append_drop]
    have e : S = (pre ++ bits.take i) ++ bits[i] :: (bits.drop (i + 1) ++ post) := by
      rw [show S = pre ++ (bits.take i ++ bits[i] :: bits.drop (i + 1)) ++ post from by simp only [S]; rw [← eb]]
      simp only [List.append_assoc, List.cons_append]
    rw [e, show pre.length + i = (pre ++ bits.take i).length by simp; omega, Streaming.read_append,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl
  have etake : ∀ i, i < r → bits.take (i + 1) = bits.take i ++ [bits.getD i false] := by
    intro i hi
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  let L : WhileBody 3 _ :=
    { body := BitPair.machine
      tape := 0
      bound := r
      H := bitsH pre o bits
      A := bitsA U S o B bits
      cost := fun _ => 2
      step := fun i hi => by
        have h := BitPair.run U S i (pre.length + i) (o ++ pairsOf (bits.take i)) B
        rw [hread i hi] at h
        have et := etake i hi
        refine h.congr ?_ ?_
        · funext j; fin_cases j
          · rfl
          · show pre.length + i + 1 = pre.length + (i + 1); omega
          · show (o ++ pairsOf (bits.take i)).length + 2 = (o ++ pairsOf (bits.take (i + 1))).length
            rw [et, pairsOf_append]; simp [pairsOf]; omega
        · funext j; fin_cases j
          · rfl
          · rfl
          · show overlay (o ++ pairsOf (bits.take i) ++ [true, bits.getD i false]) B =
              overlay (o ++ pairsOf (bits.take (i + 1))) B
            rw [et, pairsOf_append]; simp [pairsOf]
      cont := fun i hi => by
        show readTapeBit U i = true
        exact read_rep_app r i (false :: rus) hi
      halt := by
        show readTapeBit U r = false
        simpa using Streaming.read_append (List.replicate r true) rus false }
  have h := L.run
  rw [L.rest_const 2 (fun _ => rfl)] at h
  have er : bits.take r = bits := by rw [← hb, List.take_length]
  have e0 : bitsH pre o bits 0 = ![0, pre.length, o.length] := by
    funext j; fin_cases j <;> simp [bitsH, pairsOf]
  have e1 : bitsA U S o B bits 0 = ![U, S, overlay o B] := by
    funext j; fin_cases j <;> simp [bitsA, pairsOf]
  have e2 : bitsH pre o bits r = ![r, pre.length + r, (o ++ pairsOf bits).length] := by
    funext j; fin_cases j <;> simp [bitsH, er]
  have e3 : bitsA U S o B bits r = ![U, S, overlay (o ++ pairsOf bits) B] := by
    funext j; fin_cases j <;> simp [bitsA, er]
  exact (h.congr_in e0 e1).congr e2 e3

namespace EndF

/-- Write `false` at the head and move right (a word's terminator). -/
def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .right⟩ else none

theorem run (o B : List Bool) :
    Step machine 1 ![o.length] ![overlay o B] ![o.length + 1] ![overlay (o ++ [false]) B] := by
  have hs : step machine ⟨machine.start, ![o.length], ![overlay o B]⟩ =
      some ⟨1, ![o.length + 1], ![overlay (o ++ [false]) B]⟩ := by
    simp [step, machine]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, overlay_write]
  obtain ⟨r, hr, hf, hs'⟩ := (Timed.single (p := machine) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

end EndF

end NearCubicWires.WireExponent3_5.SeedFix
