import Proof.Wire_3_5.SeedFixFetch

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

/-- `n` zero bits of a framed word. -/
def zw (n : ℕ) : List Bool := (List.replicate n [true, false]).flatten

theorem zw_succ (n : ℕ) : zw (n + 1) = zw n ++ [true, false] := by
  unfold zw; rw [List.replicate_succ', List.flatten_append]; simp

theorem zw_add (a b : ℕ) : zw (a + b) = zw a ++ zw b := by
  unfold zw; rw [List.replicate_add, List.flatten_append]

theorem zw_zero : zw 0 = [] := rfl

theorem zw_length (n : ℕ) : (zw n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zw_succ, List.length_append, ih]; simp; ring

theorem frame_zeros (n : ℕ) : frame (List.replicate n false ++ [true]) = zw n ++ [true, true, false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, frame, ih]
    simp [zw, List.replicate_succ]

theorem bits_two_pow : ∀ n : ℕ, Nat.bits (2 ^ n) = List.replicate n false ++ [true]
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, show 2 ^ n * 2 = Nat.bit false (2 ^ n) by simp [Nat.bit_val]; ring,
      Nat.bits_append_bit _ _ (fun h => absurd h (by positivity)), bits_two_pow n]
    simp [List.replicate_succ]

theorem exprWord_single (c : ℤ) : exprWord [(c, [])] = true :: (coefWord c ++ [false, false]) := by
  simp [exprWord, termWord]

theorem coefWord_pow (s : Bool) (E : ℕ) :
    coefWord ((if s then -1 else 1) * 2 ^ E) = [true, s] ++ zw E ++ [true, true, false] := by
  have hb := bits_two_pow E
  cases s
  · have h1 : ((if false = true then -1 else 1) * (2 : ℤ) ^ E) = 2 ^ E := by simp
    have h2 : ¬ ((2 : ℤ) ^ E < 0) := not_lt.mpr (by positivity)
    rw [h1, coefWord, decide_eq_false h2, show ((2 : ℤ) ^ E).natAbs = 2 ^ E by simp [Int.natAbs_pow], hb, frame,
      frame_zeros]
    simp
  · have h1 : ((if true = true then -1 else 1) * (2 : ℤ) ^ E) = -2 ^ E := by simp
    have h2 : (-(2 : ℤ) ^ E < 0) := by simp [pow_pos]
    rw [h1, coefWord, decide_eq_true h2, show (-(2 : ℤ) ^ E).natAbs = 2 ^ E by simp [Int.natAbs_pow], hb, frame,
      frame_zeros]
    simp

/-- **The coefficient term's word**: `[true, true, sign]`, `E` zero bits, `[true, true, false, false, false]`. -/
theorem coefExprWord (s : Bool) (E : ℕ) :
    exprWord [((if s then -1 else 1) * 2 ^ E, [])] = [true, true, s] ++ zw E ++ [true, true, false, false, false] := by
  rw [exprWord_single, coefWord_pow]
  simp

theorem read_rep_app (n i : ℕ) (t : List Bool) (hi : i < n) : readTapeBit (List.replicate n true ++ t) i = true := by
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## Small writers -/

namespace PairStep
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Tapes `0` a unit ruler, `1` the output: append a zero bit's pair, step the ruler. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q _ =>
    if q.val = 0 then some (act 1 none (some true) .stay .right)
    else if q.val = 1 then some (act 2 none (some false) .right .right)
    else none

theorem run (U : List Bool) (h : ℕ) (o B : List Bool) :
    Step machine 2 ![h, o.length] ![U, overlay o B] ![h + 1, o.length + 2] ![U, overlay (o ++ [true, false]) B] := by
  have s1 : step machine (cfg 0 U (overlay o B) h o.length) = some (cfg 1 U (overlay (o ++ [true]) B) h (o.length + 1)) := by
    rw [Two.step_cfg machine 0 1 U (overlay o B) h o.length none (some true) .stay .right (by simp [machine])]
    simp only [Two.wr, HeadMove.apply, overlay_write]
  have s2 : step machine (cfg 1 U (overlay (o ++ [true]) B) h (o.length + 1)) =
      some (cfg 2 U (overlay (o ++ [true, false]) B) (h + 1) (o.length + 2)) := by
    rw [Two.step_cfg machine 1 2 U (overlay (o ++ [true]) B) h (o.length + 1) none (some false) .right .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true]) B false
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  obtain ⟨r, hr, hf, hs⟩ := ((Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end PairStep

noncomputable def pairLoopM := StreamController.machine PairStep.machine 0

def pairH (o : List Bool) (i : ℕ) : Fin 2 → ℕ := ![i, (o ++ zw i).length]
def pairA (U o B : List Bool) (i : ℕ) : Fin 2 → List Bool := ![U, overlay (o ++ zw i) B]

theorem pair_step (U o B : List Bool) (i : ℕ) :
    Step PairStep.machine 2 (pairH o i) (pairA U o B i) (pairH o (i + 1)) (pairA U o B (i + 1)) := by
  have h := PairStep.run U i (o ++ zw i) B
  refine h.congr ?_ ?_
  · funext j; fin_cases j
    · rfl
    · show (o ++ zw i).length + 2 = (o ++ zw (i + 1)).length
      rw [zw_succ]; simp; omega
  · funext j; fin_cases j
    · rfl
    · show overlay (o ++ zw i ++ [true, false]) B = overlay (o ++ zw (i + 1)) B
      rw [zw_succ]; simp

/-- **`n` zero bits' pairs**, one per cell of a unit ruler. -/
theorem pairLoop_run (n : ℕ) (us o B : List Bool) :
    Step pairLoopM (n * (2 + 2) + 1) ![0, o.length] ![List.replicate n true ++ false :: us, overlay o B]
      ![n, (o ++ zw n).length] ![List.replicate n true ++ false :: us, overlay (o ++ zw n) B] := by
  set U := List.replicate n true ++ false :: us
  let L : WhileBody 2 _ :=
    { body := PairStep.machine
      tape := 0
      bound := n
      H := pairH o
      A := pairA U o B
      cost := fun _ => 2
      step := fun i _ => pair_step U o B i
      cont := fun i hi => by
        show readTapeBit U i = true
        exact read_rep_app n i (false :: us) hi
      halt := by
        show readTapeBit U n = false
        simpa using Streaming.read_append (List.replicate n true) us false }
  have h := L.run
  rw [L.rest_const 2 (fun _ => rfl)] at h
  have e0 : pairH o 0 = ![0, o.length] := by funext j; fin_cases j <;> simp [pairH, zw_zero]
  have e1 : pairA U o B 0 = ![U, overlay o B] := by funext j; fin_cases j <;> simp [pairA, zw_zero]
  exact (h.congr_in e0 e1)

/-! ## The head and the tail of the coefficient term -/

namespace HeadCell
open NearCubicWires.WireExponent3_5.GF2.Two (act cfg)

/-- Tapes `0` the sign cell, `1` the output: the term marker, the frame marker, the sign. -/
def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q sc =>
    if q.val = 0 then some (act 1 none (some true) .stay .right)
    else if q.val = 1 then some (act 2 none (some true) .stay .right)
    else if q.val = 2 then some (act 3 none (some (sc 0)) .stay .right)
    else none

theorem run (s : Bool) (o B : List Bool) :
    Step machine 3 ![0, o.length] ![[s], overlay o B] ![0, o.length + 3] ![[s], overlay (o ++ [true, true, s]) B] := by
  have s1 : step machine (cfg 0 [s] (overlay o B) 0 o.length) = some (cfg 1 [s] (overlay (o ++ [true]) B) 0 (o.length + 1)) := by
    rw [Two.step_cfg machine 0 1 [s] (overlay o B) 0 o.length none (some true) .stay .right (by simp [machine])]
    simp only [Two.wr, HeadMove.apply, overlay_write]
  have s2 : step machine (cfg 1 [s] (overlay (o ++ [true]) B) 0 (o.length + 1)) =
      some (cfg 2 [s] (overlay (o ++ [true, true]) B) 0 (o.length + 2)) := by
    rw [Two.step_cfg machine 1 2 [s] (overlay (o ++ [true]) B) 0 (o.length + 1) none (some true) .stay .right
      (by simp [machine])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true]) B true
    rw [List.length_append, List.length_singleton] at this
    rw [this, List.append_assoc]
    rfl
  have s3 : step machine (cfg 2 [s] (overlay (o ++ [true, true]) B) 0 (o.length + 2)) =
      some (cfg 3 [s] (overlay (o ++ [true, true, s]) B) 0 (o.length + 3)) := by
    rw [Two.step_cfg machine 2 3 [s] (overlay (o ++ [true, true]) B) 0 (o.length + 2) none (some s) .stay .right
      (by simp [machine, readTapeBit])]
    simp only [Two.wr, HeadMove.apply]
    have := overlay_write (o ++ [true, true]) B s
    rw [List.length_append, show [true, true].length = 2 from rfl] at this
    rw [this, List.append_assoc]
    rfl
  obtain ⟨r, hr, hf, hs⟩ := (((Timed.single (p := machine) rfl s1).trans (Timed.single (p := machine) rfl s2)).trans
    (Timed.single (p := machine) rfl s3)).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

end HeadCell

namespace TailW

/-- Write `[true, true, false, false, false]` at the head, moving right. -/
def machine : Machine 1 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 5
  rule := fun q _ =>
    if q.val = 0 then some ⟨1, fun _ => some true, fun _ => .right⟩
    else if q.val = 1 then some ⟨2, fun _ => some true, fun _ => .right⟩
    else if q.val = 2 then some ⟨3, fun _ => some false, fun _ => .right⟩
    else if q.val = 3 then some ⟨4, fun _ => some false, fun _ => .right⟩
    else if q.val = 4 then some ⟨5, fun _ => some false, fun _ => .right⟩
    else none

theorem one (q q' : Fin 6) (hq : q.val ≠ 5) (b : Bool) (o B : List Bool)
    (hr : ∀ sc, machine.rule q sc = some ⟨q', fun _ => some b, fun _ => .right⟩) :
    Timed machine 1 ⟨q, ![o.length], ![overlay o B]⟩ ⟨q', ![(o ++ [b]).length], ![overlay (o ++ [b]) B]⟩ := by
  have hs : step machine ⟨q, ![o.length], ![overlay o B]⟩ = some ⟨q', ![(o ++ [b]).length], ![overlay (o ++ [b]) B]⟩ := by
    unfold step
    rw [hr]
    simp only [Option.map_some, Option.some.injEq]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, overlay_write]
  exact Timed.single (p := machine) (by simp [machine, hq]) hs

theorem run (o B : List Bool) :
    Step machine 5 ![o.length] ![overlay o B] ![o.length + 5] ![overlay (o ++ [true, true, false, false, false]) B] := by
  have t1 := one 0 1 (by decide) true o B (fun _ => by simp [machine])
  have t2 := one 1 2 (by decide) true (o ++ [true]) B (fun _ => by simp [machine])
  have t3 := one 2 3 (by decide) false (o ++ [true] ++ [true]) B (fun _ => by simp [machine])
  have t4 := one 3 4 (by decide) false (o ++ [true] ++ [true] ++ [false]) B (fun _ => by simp [machine])
  have t5 := one 4 5 (by decide) false (o ++ [true] ++ [true] ++ [false] ++ [false]) B (fun _ => by simp [machine])
  obtain ⟨r, hr, hf, hs⟩ := ((((t1.trans t2).trans t3).trans t4).trans t5).run rfl
  refine ⟨r, hr, ?_, ?_, by omega⟩
  · rw [hf]; funext i; fin_cases i; simp
  · rw [hf]; funext i; fin_cases i; simp

end TailW

/-! ## The coefficient writer (tapes 0 the sign bits, 1 the unit word, 2 the sign cell, 3 the `2kh` ruler, 4 the
exponent tape, 5 the accumulator, 6 and 7 logs) -/

def c8F : Fin 4 → Fin 8 := ![1, 0, 2, 7]

theorem install_c8F (A : Fin 8 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install c8F A v = ![v 1, v 0, v 2, A 3, A 4, A 5, A 6, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8F (H : Fin 8 → ℕ) (v : Fin 4 → ℕ) :
    dockH c8F H v = ![v 1, v 0, v 2, H 3, H 4, H 5, H 6, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def c8H : Fin 2 → Fin 8 := ![2, 5]

theorem install_c8H (A : Fin 8 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install c8H A v = ![A 0, A 1, v 0, A 3, A 4, v 1, A 6, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8H (H : Fin 8 → ℕ) (v : Fin 2 → ℕ) :
    dockH c8H H v = ![H 0, H 1, v 0, H 3, H 4, v 1, H 6, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def c8R : Fin 3 → Fin 8 := ![3, 5, 6]

theorem install_c8R (A : Fin 8 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install c8R A v = ![A 0, A 1, A 2, v 0, A 4, v 1, v 2, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8R (H : Fin 8 → ℕ) (v : Fin 3 → ℕ) :
    dockH c8R H v = ![H 0, H 1, H 2, v 0, H 4, v 1, v 2, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def c8B : Fin 1 → Fin 8 := ![0]

theorem install_c8B (A : Fin 8 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c8B A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8B (H : Fin 8 → ℕ) (v : Fin 1 → ℕ) :
    dockH c8B H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def c8X : Fin 2 → Fin 8 := ![4, 5]

theorem install_c8X (A : Fin 8 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install c8X A v = ![A 0, A 1, A 2, A 3, v 0, v 1, A 6, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8X (H : Fin 8 → ℕ) (v : Fin 2 → ℕ) :
    dockH c8X H v = ![H 0, H 1, H 2, H 3, v 0, v 1, H 6, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def c8T : Fin 1 → Fin 8 := ![5]

theorem install_c8T (A : Fin 8 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c8T A v = ![A 0, A 1, A 2, A 3, A 4, v 0, A 6, A 7] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c8T (H : Fin 8 → ℕ) (v : Fin 1 → ℕ) :
    dockH c8T H v = ![H 0, H 1, H 2, H 3, H 4, v 0, H 6, H 7] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def selF : Fin 3 → Bool := ![true, true, false]
def selRu : Fin 2 → Bool := ![true, false]

/-- The zeros of one sign bit: `2kh` pairs when set, nothing when clear. -/
noncomputable def betaBody :=
  Composition.machine (Composition.machine (RecoveryFocus.machine c8B nudgeM)
    (branchM (0 : Fin 8) (RecoveryFocus.machine c8R (MaskedReset.machine pairLoopM selRu)) (idle 8)))
    (RecoveryFocus.machine c8B nudgeM)

noncomputable def betaLoopM := StreamController.machine betaBody 0

def cnt (bs : List Bool) (i : ℕ) : ℕ := (bs.take i).count true

def betaH (bs : List Bool) (R2 : ℕ) (o0 : List Bool) (i : ℕ) : Fin 8 → ℕ :=
  ![2 * i, 0, 0, 0, 0, (o0 ++ zw (R2 * cnt bs i)).length, 0, 0]

def betaA (bs : List Bool) (R2 : ℕ) (s : Bool) (rus xs OB o0 : List Bool) (e cL cF : ℕ) (i : ℕ) : Fin 8 → List Bool :=
  ![frame bs, frame (List.replicate bs.length true), [s], List.replicate R2 true ++ false :: rus,
    List.replicate e true ++ false :: xs, overlay (o0 ++ zw (R2 * cnt bs i)) OB, List.replicate cL false,
    List.replicate cF false]

theorem read_idle {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) : Step (idle t) 0 H A H A := by
  obtain ⟨r, hr, hf, hs⟩ := (Timed.refl (idle t) ⟨(idle t).start, H, A⟩).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

def betaCost (bs : List Bool) (R2 : ℕ) (i : ℕ) : ℕ :=
  1 + 1 + ((if bs.getD i false then 2 * (R2 * (2 + 2) + 1) + 2 else 0) + 2) + 1 + 1

theorem cnt_succ (bs : List Bool) (i : ℕ) (hi : i < bs.length) :
    cnt bs (i + 1) = cnt bs i + (if bs.getD i false then 1 else 0) := by
  unfold cnt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.count_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  split <;> simp_all

/-- The zeros of sign bit `i`, from the bit's cell. -/
theorem beta_bit (bs : List Bool) (R2 : ℕ) (s : Bool) (rus xs OB o0 : List Bool) (e cL cF : ℕ)
    (hcL : R2 * (2 + 2) + 1 ≤ cL) (i : ℕ) (hi : i < bs.length) :
    Step (branchM (0 : Fin 8) (RecoveryFocus.machine c8R (MaskedReset.machine pairLoopM selRu)) (idle 8))
      ((if bs.getD i false then 2 * (R2 * (2 + 2) + 1) + 2 else 0) + 2)
      ![2 * i + 1, 0, 0, 0, 0, (o0 ++ zw (R2 * cnt bs i)).length, 0, 0] (betaA bs R2 s rus xs OB o0 e cL cF i)
      ![2 * i + 1, 0, 0, 0, 0, (o0 ++ zw (R2 * cnt bs (i + 1))).length, 0, 0]
      (betaA bs R2 s rus xs OB o0 e cL cF (i + 1)) := by
  set A := betaA bs R2 s rus xs OB o0 e cL cF i
  set o := o0 ++ zw (R2 * cnt bs i)
  have hbit : readTapeBit (frame bs) (2 * i + 1) = bs.getD i false := by
    rw [read_frame_bit _ i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  by_cases hb : bs.getD i false = true
  · have hp := pairLoop_run R2 rus o OB
    have hp0 := hp.mask (cap := cL) selRu (by intro j hj; fin_cases j <;> first | rfl | simp [selRu] at hj) hcL
    have hp1 : Step (MaskedReset.machine pairLoopM selRu) (2 * (R2 * (2 + 2) + 1) + 2) ![0, o.length, 0]
        ![List.replicate R2 true ++ false :: rus, overlay o OB, List.replicate cL false]
        ![0, (o ++ zw R2).length, 0] ![List.replicate R2 true ++ false :: rus, overlay (o ++ zw R2) OB,
          List.replicate cL false] := by
      refine (hp0.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
    have hd := dockRun hp1 c8R (by decide) ![2 * i + 1, 0, 0, 0, 0, o.length, 0, 0] A
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
    rw [dockH_c8R, install_c8R] at hd
    have hb' := branch_true (0 : Fin 8) (idle 8) hd (by show readTapeBit (frame bs) (2 * i + 1) = true; rw [hbit, hb])
    rw [if_pos hb]
    have eo : o ++ zw R2 = o0 ++ zw (R2 * cnt bs (i + 1)) := by
      rw [cnt_succ bs i hi, if_pos hb, Nat.mul_add, Nat.mul_one, zw_add]; simp [o]
    rw [eo] at hb'
    exact hb'.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  · have hb0 : bs.getD i false = false := by simpa using hb
    have hd := read_idle (t := 8) ![2 * i + 1, 0, 0, 0, 0, o.length, 0, 0] A
    have hb' := branch_false (0 : Fin 8) (RecoveryFocus.machine c8R (MaskedReset.machine pairLoopM selRu)) hd
      (by show readTapeBit (frame bs) (2 * i + 1) = false; rw [hbit, hb0])
    rw [if_neg hb]
    have ecnt : cnt bs (i + 1) = cnt bs i := by rw [cnt_succ bs i hi, if_neg hb]; rfl
    have eA : betaA bs R2 s rus xs OB o0 e cL cF (i + 1) = A := by
      show betaA bs R2 s rus xs OB o0 e cL cF (i + 1) = betaA bs R2 s rus xs OB o0 e cL cF i
      unfold betaA; rw [ecnt]
    rw [eA, ecnt]
    exact hb'

theorem beta_step (bs : List Bool) (R2 : ℕ) (s : Bool) (rus xs OB o0 : List Bool) (e cL cF : ℕ)
    (hcL : R2 * (2 + 2) + 1 ≤ cL) (i : ℕ) (hi : i < bs.length) :
    Step betaBody (betaCost bs R2 i) (betaH bs R2 o0 i) (betaA bs R2 s rus xs OB o0 e cL cF i)
      (betaH bs R2 o0 (i + 1)) (betaA bs R2 s rus xs OB o0 e cL cF (i + 1)) := by
  have s1 := dockRun (nudge_run (frame bs) (2 * i)) c8B (by decide) (betaH bs R2 o0 i)
    (betaA bs R2 s rus xs OB o0 e cL cF i) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c8B, install_c8B] at s1
  have s2 := beta_bit bs R2 s rus xs OB o0 e cL cF hcL i hi
  have s3 := dockRun (nudge_run (frame bs) (2 * i + 1)) c8B (by decide)
    ![2 * i + 1, 0, 0, 0, 0, (o0 ++ zw (R2 * cnt bs (i + 1))).length, 0, 0] (betaA bs R2 s rus xs OB o0 e cL cF (i + 1))
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c8B, install_c8B] at s3
  have hall := ((s1.congr (hout' := ![2 * i + 1, 0, 0, 0, 0, (o0 ++ zw (R2 * cnt bs i)).length, 0, 0])
      (tout' := betaA bs R2 s rus xs OB o0 e cL cF i)
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).seq s2).seq s3
  unfold betaCost
  refine hall.congr ?_ ?_
  · funext j; fin_cases j
    · show 2 * i + 1 + 1 = 2 * (i + 1); ring
    all_goals rfl
  · funext j; fin_cases j <;> rfl

theorem betaLoop_run (bs : List Bool) (R2 : ℕ) (s : Bool) (rus xs OB o0 : List Bool) (e cL cF : ℕ)
    (hcL : R2 * (2 + 2) + 1 ≤ cL) :
    Step betaLoopM (((List.range (bs.length - 0)).map (fun i => betaCost bs R2 (0 + i) + 2)).sum + 1)
      (betaH bs R2 o0 0) (betaA bs R2 s rus xs OB o0 e cL cF 0)
      (betaH bs R2 o0 bs.length) (betaA bs R2 s rus xs OB o0 e cL cF bs.length) := by
  let L : WhileBody 8 _ :=
    { body := betaBody
      tape := 0
      bound := bs.length
      H := betaH bs R2 o0
      A := betaA bs R2 s rus xs OB o0 e cL cF
      cost := betaCost bs R2
      step := fun i hi => beta_step bs R2 s rus xs OB o0 e cL cF hcL i hi
      cont := fun i hi => by
        show readTapeBit (frame bs) (2 * i) = true
        exact read_frame_mark _ i hi
      halt := by
        show readTapeBit (frame bs) (2 * bs.length) = false
        exact read_frame_end bs }
  exact L.run

def selAll : Fin 8 → Bool := ![true, false, false, false, true, true, false, false]

/-- **The coefficient term writer**: the sign's parity, `[true, true, sign]`, the zeros, the tail, every head back at
cell 0. -/
noncomputable def coefM :=
  MaskedReset.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine c8F (MaskedReset.machine (FoldCell.machine parityStep false) selF))
    (RecoveryFocus.machine c8H HeadCell.machine)) betaLoopM) (RecoveryFocus.machine c8X pairLoopM))
    (RecoveryFocus.machine c8T TailW.machine)) selAll

/-- The parity of the sign bits. -/
def parity (bs : List Bool) : Bool := foldBits parityStep false (List.replicate bs.length true) bs

def coefCost (bs : List Bool) (R2 e : ℕ) : ℕ :=
  2 * ((2 * (2 * bs.length + 1) + 2) + 1 + 3 + 1 +
    ((((List.range (bs.length - 0)).map (fun i => betaCost bs R2 (0 + i) + 2)).sum + 1)) + 1 + (e * (2 + 2) + 1) + 1 +
      5) + 2

theorem coef_run (bs : List Bool) (R2 : ℕ) (sg0 : Bool) (rus xs OB : List Bool) (e cL cF cM : ℕ)
    (hcL : R2 * (2 + 2) + 1 ≤ cL) (hcF : 2 * bs.length + 1 ≤ cF) (hcM : coefCost bs R2 e ≤ 2 * cM + 2) :
    Step coefM (coefCost bs R2 e) (fun _ => 0)
      (Fin.addCases ![frame bs, frame (List.replicate bs.length true), [sg0], List.replicate R2 true ++ false :: rus,
        List.replicate e true ++ false :: xs, OB, List.replicate cL false, List.replicate cF false]
        (fun _ : Fin 1 => List.replicate cM false))
      (fun _ => 0)
      (Fin.addCases ![frame bs, frame (List.replicate bs.length true), [parity bs],
        List.replicate R2 true ++ false :: rus, List.replicate e true ++ false :: xs,
        overlay (exprWord [((if parity bs then -1 else 1) * 2 ^ (R2 * cnt bs bs.length + e), [])]) OB,
        List.replicate cL false, List.replicate cF false] (fun _ : Fin 1 => List.replicate cM false)) := by
  set p := parity bs
  set ONES := frame (List.replicate bs.length true)
  set RU := List.replicate R2 true ++ false :: rus
  set XE := List.replicate e true ++ false :: xs
  set o0 : List Bool := [true, true, p]
  -- 1: the parity
  have hf := FoldCell.run parityStep false (List.replicate bs.length true) bs sg0 (by simp)
  rw [List.length_replicate] at hf
  have hf' : Step (FoldCell.machine parityStep false) (2 * bs.length + 1) (fun _ => 0) ![ONES, frame bs, [sg0]]
      ![2 * bs.length, 2 * bs.length, 0] ![ONES, frame bs, [p]] :=
    hf.congr_in (by funext j; fin_cases j <;> rfl) rfl
  have hfm := maskZero hf' selF (by intro j hj; fin_cases j <;> first | rfl | simp [selF] at hj) hcF
  have hfm' : Step (MaskedReset.machine (FoldCell.machine parityStep false) selF) (2 * (2 * bs.length + 1) + 2)
      (fun _ => 0) ![ONES, frame bs, [sg0], List.replicate cF false] (fun _ => 0)
      ![ONES, frame bs, [p], List.replicate cF false] := by
    refine (hfm.congr_in rfl ?_).congr rfl ?_ <;> funext j <;> fin_cases j <;> rfl
  have s1 := dockKeep hfm' c8F (by decide) (fun _ => 0)
    ![frame bs, ONES, [sg0], RU, XE, OB, List.replicate cL false, List.replicate cF false]
    (fun _ => rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_c8F] at s1
  -- 2: the head
  have hh := HeadCell.run p [] OB
  have s2 := dockRun hh c8H (by decide) (fun _ => 0)
    ![frame bs, ONES, [p], RU, XE, OB, List.replicate cL false, List.replicate cF false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_c8H, install_c8H] at s2
  -- 3: the zeros of the sign bits
  have s3 := betaLoop_run bs R2 p rus xs OB o0 e cL cF hcL
  set c := R2 * cnt bs bs.length
  -- 4: the zeros of the exponent
  have hx := pairLoop_run e xs (o0 ++ zw c) OB
  have s4 := dockRun hx c8X (by decide) (betaH bs R2 o0 bs.length) (betaA bs R2 p rus xs OB o0 e cL cF bs.length)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_c8X, install_c8X] at s4
  -- 5: the tail
  have ht := TailW.run (o0 ++ zw c ++ zw e) OB
  have s5 := dockRun ht c8T (by decide) ![2 * bs.length, 0, 0, 0, e, (o0 ++ zw c ++ zw e).length, 0, 0]
    ![frame bs, ONES, [p], RU, XE, overlay (o0 ++ zw c ++ zw e) OB, List.replicate cL false, List.replicate cF false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c8T, install_c8T] at s5
  have e30 : betaH bs R2 o0 0 = ![0, 0, 0, 0, 0, 3, 0, 0] := by
    funext j; fin_cases j <;> simp [betaH, cnt, zw_zero, o0]
  have e31 : betaA bs R2 p rus xs OB o0 e cL cF 0 =
      ![frame bs, ONES, [p], RU, XE, overlay o0 OB, List.replicate cL false, List.replicate cF false] := by
    funext j; fin_cases j <;> simp [betaA, cnt, zw_zero, ONES, RU, XE]
  rw [e30, e31] at s3
  have hall := ((((s1.congr (tout' := ![frame bs, ONES, [p], RU, XE, OB, List.replicate cL false,
      List.replicate cF false]) rfl (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![0, 0, 0, 0, 0, 3, 0, 0])
      (tout' := ![frame bs, ONES, [p], RU, XE, overlay o0 OB, List.replicate cL false, List.replicate cF false])
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq s3).seq
    (s4.congr (hout' := ![2 * bs.length, 0, 0, 0, e, (o0 ++ zw c ++ zw e).length, 0, 0])
      (tout' := ![frame bs, ONES, [p], RU, XE, overlay (o0 ++ zw c ++ zw e) OB, List.replicate cL false,
        List.replicate cF false]) (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl))).seq s5
  have hm := hall.mask (cap := cM) selAll (by intro j _; fin_cases j <;> rfl) (by unfold coefCost at hcM; omega)
  have eW : o0 ++ zw c ++ zw e ++ [true, true, false, false, false] =
      exprWord [((if p then -1 else 1) * 2 ^ (c + e), [])] := by
    rw [coefExprWord, zw_add]; simp [o0]
  rw [eW] at hm
  unfold coefCost
  exact (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)

end NearCubicWires.WireExponent3_5.SeedFix
