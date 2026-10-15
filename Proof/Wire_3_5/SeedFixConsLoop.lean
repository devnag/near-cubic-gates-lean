import Proof.Wire_3_5.SeedFixConsRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

/-! ## `ClearFrame`: a framed word, padded with blanks, erased to blanks -/

namespace ClearFrame

def cfg (q : Fin 3) (A : List Bool) (h : ℕ) : Configuration 1 3 := ⟨q, ![h], ![A]⟩

/-- State `0` at a marker (a set marker is cleared, a blank one halts), state `1` at the word's bit (cleared). -/
def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q sc =>
    if q.val = 0 then some (if sc 0 then ⟨1, ![some false], ![.right]⟩ else ⟨2, ![none], ![.stay]⟩)
    else if q.val = 1 then some ⟨0, ![some false], ![.right]⟩
    else none

theorem step_cfg (q next : Fin 3) (A : List Bool) (h : ℕ) (w : Option Bool) (m : HeadMove)
    (hr : machine.rule q ![readTapeBit A h] = some ⟨next, ![w], ![m]⟩) :
    step machine (cfg q A h) = some (cfg next (Two.wr A h w) (m.apply h)) := by
  have hs : (cfg q A h).scanned = ![readTapeBit A h] := by
    funext i; fin_cases i; rfl
  unfold step
  rw [hs]
  change (machine.rule q _).map _ = _
  rw [hr]
  simp only [Option.map_some, Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i; rfl
  · funext i; fin_cases i; cases w <;> rfl

/-- The pairs of a framed word (`frame u = pairs u ++ [false]`). -/
def pairs (u : List Bool) : List Bool := u.flatMap fun c => [true, c]

theorem frame_eq (u : List Bool) : frame u = pairs u ++ [false] := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [frame, pairs, ih]

theorem pairs_length (u : List Bool) : (pairs u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons c u ih => simp only [pairs, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢; rw [ih]; simp; ring

theorem timed (Z : List Bool) : ∀ (u P : List Bool),
    RecoveryExecution.Timed machine (2 * u.length + 1) (cfg 0 (P ++ (pairs u ++ false :: Z)) P.length)
      (cfg 2 (P ++ (List.replicate (2 * u.length) false ++ false :: Z)) (P.length + 2 * u.length))
  | [], P => by
    have hr : readTapeBit (P ++ (pairs [] ++ false :: Z)) P.length = false := by
      simpa [pairs] using Streaming.read_append P Z false
    have hs : step machine (cfg 0 (P ++ (pairs [] ++ false :: Z)) P.length) =
        some (cfg 2 (P ++ (pairs [] ++ false :: Z)) P.length) := by
      rw [step_cfg 0 2 _ P.length none .stay (by simp [machine, hr])]
      rfl
    simpa [pairs] using RecoveryExecution.Timed.single (p := machine) rfl hs
  | c :: u, P => by
    have e0 : P ++ (pairs (c :: u) ++ false :: Z) = P ++ true :: (c :: (pairs u ++ false :: Z)) := by
      simp [pairs]
    have hr0 : readTapeBit (P ++ true :: (c :: (pairs u ++ false :: Z))) P.length = true :=
      Streaming.read_append _ _ _
    have hw0 : writeTapeBit (P ++ true :: (c :: (pairs u ++ false :: Z))) P.length false =
        (P ++ [false]) ++ c :: (pairs u ++ false :: Z) := by
      rw [write_mid]; simp
    have hs0 : step machine (cfg 0 (P ++ true :: (c :: (pairs u ++ false :: Z))) P.length) =
        some (cfg 1 ((P ++ [false]) ++ c :: (pairs u ++ false :: Z)) (P.length + 1)) := by
      rw [step_cfg 0 1 _ P.length (some false) .right (by simp [machine, hr0])]
      simp only [Two.wr, HeadMove.apply, hw0]
    have hw1 : writeTapeBit ((P ++ [false]) ++ c :: (pairs u ++ false :: Z)) (P.length + 1) false =
        (P ++ [false, false]) ++ (pairs u ++ false :: Z) := by
      have := write_mid (P ++ [false]) (pairs u ++ false :: Z) c false
      rw [List.length_append, List.length_singleton] at this
      rw [this]; simp
    have hs1 : step machine (cfg 1 ((P ++ [false]) ++ c :: (pairs u ++ false :: Z)) (P.length + 1)) =
        some (cfg 0 ((P ++ [false, false]) ++ (pairs u ++ false :: Z)) (P.length + 1 + 1)) := by
      rw [step_cfg 1 0 _ (P.length + 1) (some false) .right (by simp [machine])]
      simp only [Two.wr, HeadMove.apply, hw1]
    have t0 := RecoveryExecution.Timed.single (p := machine) rfl hs0
    have t1 := RecoveryExecution.Timed.single (p := machine) rfl hs1
    have tail := timed Z u (P ++ [false, false])
    have e1 : (P ++ [false, false]).length = P.length + 1 + 1 := by simp
    have e2 : (P ++ [false, false]) ++ (List.replicate (2 * u.length) false ++ false :: Z) =
        P ++ (List.replicate (2 * (c :: u).length) false ++ false :: Z) := by
      rw [List.length_cons, show 2 * (u.length + 1) = 2 * u.length + 1 + 1 by ring, List.replicate_succ,
        List.replicate_succ]
      simp
    have e3 : P.length + 1 + 1 + 2 * u.length = P.length + 2 * (c :: u).length := by simp; ring
    rw [e1, e2, e3] at tail
    have := (t0.trans t1).trans tail
    rw [e0]
    rwa [show 1 + 1 + (2 * u.length + 1) = 2 * (c :: u).length + 1 by simp; ring] at this

/-- **A padded framed word erased**: the tape ends all blank, of the same length. -/
theorem clear_run (w : List Bool) (R : ℕ) (hR : 2 * w.length + 1 ≤ R) :
    Step machine (2 * w.length + 1) ![0] ![pad R (frame w)] ![2 * w.length] ![List.replicate R false] := by
  have e : pad R (frame w) = [] ++ (pairs w ++ false :: List.replicate (R - 2 * w.length - 1) false) := by
    rw [frame_eq]
    unfold pad
    rw [List.length_append, pairs_length]
    simp [List.append_assoc]
    omega
  obtain ⟨r, hr, hf, hs⟩ := (timed (List.replicate (R - 2 * w.length - 1) false) w []).run rfl
  refine ⟨r, ?_, ?_, ?_, by omega⟩
  · rw [e]; exact hr
  · rw [hf]; simp [cfg]
  · rw [hf]
    show ![[] ++ (List.replicate (2 * w.length) false ++ false :: List.replicate (R - 2 * w.length - 1) false)] =
      ![List.replicate R false]
    have : List.replicate (2 * w.length) false ++ false :: List.replicate (R - 2 * w.length - 1) false =
        List.replicate R false := by
      rw [← List.replicate_succ, ← List.replicate_add]
      congr 1; omega
    rw [List.nil_append, this]

end ClearFrame

/-- A word written over a blank tape is the word padded with blanks. -/
theorem overlay_blank (w : List Bool) (R : ℕ) : overlay w (List.replicate R false) = pad R w := by
  simp [overlay, pad, List.drop_replicate]

/-! ## The constraint records -/

/-- A constraint record: a marker, the label's framed word, then the target's. -/
def consRec (ℓ k : ℕ) (con : ℕ × ℕ) : List Bool := true :: (frame (binary ℓ con.1) ++ frame (binary k con.2))

def recLen (ℓ k : ℕ) : ℕ := 2 * ℓ + 2 * k + 3

theorem consRec_length (ℓ k : ℕ) (con : ℕ × ℕ) : (consRec ℓ k con).length = recLen ℓ k := by
  simp [consRec, recLen]; omega

/-- The constraint tape: the records, a terminator, stale cells. -/
def consTape (ℓ k : ℕ) (cons : List (ℕ × ℕ)) (stale : List Bool) : List Bool :=
  cons.flatMap (consRec ℓ k) ++ false :: stale

theorem flatMap_consRec_length (ℓ k : ℕ) (cs : List (ℕ × ℕ)) :
    (cs.flatMap (consRec ℓ k)).length = cs.length * recLen ℓ k := by
  induction cs with
  | nil => simp
  | cons c cs ih => rw [List.flatMap_cons, List.length_append, consRec_length, ih, List.length_cons]; ring

theorem consTape_split (ℓ k : ℕ) (cons : List (ℕ × ℕ)) (stale : List Bool) (i : ℕ) (hi : i < cons.length) :
    consTape ℓ k cons stale = (cons.take i).flatMap (consRec ℓ k) ++ consRec ℓ k cons[i] ++
      ((cons.drop (i + 1)).flatMap (consRec ℓ k) ++ false :: stale) := by
  have e : cons = cons.take i ++ cons[i] :: cons.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  calc consTape ℓ k cons stale = consTape ℓ k (cons.take i ++ cons[i] :: cons.drop (i + 1)) stale :=
        congrArg (fun c => consTape ℓ k c stale) e
    _ = _ := by simp only [consTape, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem consTape_read (ℓ k : ℕ) (cons : List (ℕ × ℕ)) (stale : List Bool) (i : ℕ) (hi : i ≤ cons.length) :
    readTapeBit (consTape ℓ k cons stale) (i * recLen ℓ k) = decide (i < cons.length) := by
  by_cases h : i < cons.length
  · rw [consTape_split ℓ k cons stale i h, decide_eq_true h]
    have hl : ((cons.take i).flatMap (consRec ℓ k)).length = i * recLen ℓ k := by
      rw [flatMap_consRec_length, List.length_take, Nat.min_eq_left (by omega)]
    rw [← hl, List.append_assoc]
    exact Streaming.read_append _ _ _
  · have hi' : i = cons.length := by omega
    subst hi'
    rw [decide_eq_false h, ← flatMap_consRec_length]
    exact Streaming.read_append _ _ _

/-! ## The block's registers across records -/

/-- The block's registers: the power, column, product and reduction words, the mask, the record register, the bit cell,
the label tape and the table (before its blank tail). -/
structure Regs where
  a : ℕ
  c : ℕ
  x : ℕ
  z : ℕ
  mc : ℕ
  r : List Bool
  b : Bool
  fl : List Bool
  T : List Bool

/-- The registers after one more record (`consRows_run`'s exit). -/
def Regs.next (p ℓ twoH k plen : ℕ) (R : Regs) (con : ℕ × ℕ) : Regs :=
  ⟨accPow p ℓ con.1 twoH, curG p ℓ con.1 R.c twoH, xG p ℓ con.1 R.x twoH, zG p ℓ con.1 R.z twoH, (lfsr p ℓ)^[k] 1,
    recRow ℓ (colTable p ℓ twoH con.1) plen R.r k, bitRow (colTable p ℓ twoH con.1) plen R.b k, frame (binary ℓ con.1),
    tabWords p ℓ con.1 twoH⟩

def regsAt (p ℓ twoH k plen : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ)) (i : ℕ) : Regs :=
  (cons.take i).foldl (Regs.next p ℓ twoH k plen) R0

theorem regsAt_succ (p ℓ twoH k plen : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ)) (i : ℕ) (hi : i < cons.length) :
    regsAt p ℓ twoH k plen R0 cons (i + 1) = (regsAt p ℓ twoH k plen R0 cons i).next p ℓ twoH k plen cons[i] := by
  unfold regsAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldl_append]
  rfl

/-- The invariant the block needs of its registers. -/
def Regs.Ok (ℓ twoH : ℕ) (R : Regs) : Prop :=
  R.r.length ≤ 2 * ℓ + 1 ∧ R.fl.length ≤ 2 * ℓ + 1 ∧ R.T.length = twoH * (ℓ * (2 * ℓ + 1))

theorem foldl_ok (p ℓ twoH k plen : ℕ) : ∀ (L : List (ℕ × ℕ)) (R : Regs), R.Ok ℓ twoH →
    (L.foldl (Regs.next p ℓ twoH k plen) R).Ok ℓ twoH
  | [], R, h => h
  | con :: L, R, h => by
    rw [List.foldl_cons]
    refine foldl_ok p ℓ twoH k plen L _ ⟨?_, ?_, ?_⟩
    · exact recRow_length ℓ _ plen R.r h.1 k
    · simp [Regs.next]
    · simp [Regs.next, tabWords_length]

theorem regsAt_ok (p ℓ twoH k plen : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ)) (h0 : R0.Ok ℓ twoH) (i : ℕ) :
    (regsAt p ℓ twoH k plen R0 cons i).Ok ℓ twoH :=
  foldl_ok p ℓ twoH k plen _ R0 h0

/-- The rows written for the first `i` records. -/
def rowsI (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (i : ℕ) : List Bool :=
  (cons.take i).flatMap fun con => rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k

theorem rowsI_succ (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (i : ℕ) (hi : i < cons.length) :
    rowsI p ℓ twoH k plen pfx cons (i + 1) =
      rowsI p ℓ twoH k plen pfx cons i ++ rowsOut (colTable p ℓ twoH cons[i].1) plen pfx cons[i].2 k := by
  unfold rowsI
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append]
  simp

/-! ## The bank (tapes 0–21 the block's, 22 the constraint records, 23 the copy log) -/

def bank24 (p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL : ℕ) (R : Regs) (V O S : List Bool) : Fin 24 → List Bool :=
  ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ R.a), frame (binary ℓ R.c),
    R.T ++ List.replicate m false, frame (binary ℓ p), R.fl, frame (binary ℓ R.x), frame (binary ℓ R.z), [false],
    List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, V, frame (binary plen pfx),
    frame (binary ℓ R.mc), R.r, [R.b], [false], O, frame (binary ℓ 1), List.replicate cap4 false, S,
    List.replicate cL false]

def hd24 (o s : ℕ) : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0, s, 0]

/-- The block's own 22 tapes (`consRows_run`'s layout). -/
def bank22 (p ℓ twoH plen pfx m cap cap2 cap3 cap4 : ℕ) (R : Regs) (V O : List Bool) : Fin 22 → List Bool :=
  ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ R.a), frame (binary ℓ R.c),
    R.T ++ List.replicate m false, frame (binary ℓ p), R.fl, frame (binary ℓ R.x), frame (binary ℓ R.z), [false],
    List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, V, frame (binary plen pfx),
    frame (binary ℓ R.mc), R.r, [R.b], [false], O, frame (binary ℓ 1), List.replicate cap4 false]

def hd22 (o : ℕ) : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, o, 0, 0]

def c24Nudge : Fin 1 → Fin 24 := ![22]

theorem install_c24Nudge (A : Fin 24 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c24Nudge A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 0, A 23] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c24Nudge (H : Fin 24 → ℕ) (v : Fin 1 → ℕ) :
    dockH c24Nudge H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, v 0, H 23] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def c24FL : Fin 3 → Fin 24 := ![22, 6, 23]

theorem install_c24FL (A : Fin 24 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install c24FL A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 1, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 0, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c24FL (H : Fin 24 → ℕ) (v : Fin 3 → ℕ) :
    dockH c24FL H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 1, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, v 0, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def c24V : Fin 3 → Fin 24 := ![22, 13, 23]

theorem install_c24V (A : Fin 24 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install c24V A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, v 1, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 0, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c24V (H : Fin 24 → ℕ) (v : Fin 3 → ℕ) :
    dockH c24V H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, v 1, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, v 0, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def c24Clr : Fin 2 → Fin 24 := ![13, 23]

theorem install_c24Clr (A : Fin 24 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install c24Clr A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, v 0, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, v 1] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def sel1 : Fin 1 → Bool := ![true]

noncomputable def cNudge := RecoveryFocus.machine c24Nudge nudgeM
noncomputable def cFL := RecoveryFocus.machine c24FL (MaskedReset.machine CopyO.machine selRec)
noncomputable def cV := RecoveryFocus.machine c24V (MaskedReset.machine CopyO.machine selRec)
noncomputable def cRows := TapeEmbedding.machine 2 consRowsM
noncomputable def cClr := RecoveryFocus.machine c24Clr (MaskedReset.machine ClearFrame.machine sel1)

/-- Past the marker, the label into the label tape, past the label's end. -/
noncomputable def labM := Composition.machine (Composition.machine cNudge cFL) cNudge
/-- The target onto the blank target tape, past the record's end. -/
noncomputable def tgtM := Composition.machine cV cNudge

/-- **One constraint record**: the label and the target loaded, the block, then the target tape erased. -/
noncomputable def recBody := Composition.machine (Composition.machine (Composition.machine labM tgtM) cRows) cClr

noncomputable def loopM := StreamController.machine recBody 22

def labCost (ℓ : ℕ) : ℕ := 1 + 1 + (2 * (2 * ℓ + 1) + 2) + 1 + 1
def tgtCost (k : ℕ) : ℕ := 2 * (2 * k + 1) + 2 + 1 + 1
def clrCost (k : ℕ) : ℕ := 2 * (2 * k + 1) + 2
def recCost (ℓ twoH k plen : ℕ) : ℕ := labCost ℓ + 1 + tgtCost k + 1 + consCost ℓ twoH k plen + 1 + clrCost k

/-- The label register loaded. -/
def Regs.load (R : Regs) (fl : List Bool) : Regs := ⟨R.a, R.c, R.x, R.z, R.mc, R.r, R.b, fl, R.T⟩

theorem lab_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL o : ℕ) (R : Regs) (O L0 restS : List Bool)
    (con : ℕ × ℕ) (hfl : R.fl.length ≤ 2 * ℓ + 1) (hcL : 2 * ℓ + 1 ≤ cL) :
    Step labM (labCost ℓ) (hd24 o L0.length)
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (List.replicate RV false) O (L0 ++ consRec ℓ k con ++ restS))
      (hd24 o (L0.length + 1 + 2 * ℓ + 1))
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.load (frame (binary ℓ con.1))) (List.replicate RV false) O
        (L0 ++ consRec ℓ k con ++ restS)) := by
  set S := L0 ++ consRec ℓ k con ++ restS with hS
  set P := L0.length with hP
  set Vb := List.replicate RV false
  set Cl := List.replicate cL false
  have s1 := dockRun (nudge_run S P) c24Nudge (by decide) (hd24 o P)
    (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vb O S) (by intro j; fin_cases j; rfl)
    (by intro j; fin_cases j; rfl)
  rw [dockH_c24Nudge, install_c24Nudge] at s1
  have s1' := s1.congr (hout' := hd24 o (P + 1)) (tout' := bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vb O S)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have eSL : (L0 ++ [true]) ++ frame (binary ℓ con.1) ++ (frame (binary k con.2) ++ restS) = S := by
    rw [hS]; simp [consRec, List.append_assoc]
  obtain ⟨cr, hcr, hcrf⟩ := CopyO.copy_run (L0 ++ [true]) (binary ℓ con.1) (frame (binary k con.2) ++ restS) [] R.fl
  rw [eSL] at hcr hcrf
  have hcs : Step CopyO.machine (2 * (binary ℓ con.1).length + 1) ![(L0 ++ [true]).length, 0] ![S, R.fl]
      ![(L0 ++ [true]).length + 2 * (binary ℓ con.1).length, 2 * (binary ℓ con.1).length + 1]
      ![S, frame (binary ℓ con.1)] := by
    refine ⟨cr, hcr, ?_, ?_, runFrom_steps_le _ _ _ _ hcr⟩
    · rw [hcrf]; funext j; fin_cases j <;> simp [CopyO.config, frame_length]
    · rw [hcrf]
      funext j; fin_cases j
      · rfl
      · show overlay ([] ++ frame (binary ℓ con.1)) R.fl = frame (binary ℓ con.1)
        exact overlay_exact _ _ (by rw [List.nil_append, frame_length, binary_length]; exact hfl)
  have e1 : (L0 ++ [true]).length = P + 1 := by rw [List.length_append]; rfl
  rw [binary_length, e1] at hcs
  have hm2 := hcs.mask (cap := cL) selRec (by intro j hj; fin_cases j <;> first | rfl | simp [selRec] at hj) hcL
  have hm2' : Step (MaskedReset.machine CopyO.machine selRec) (2 * (2 * ℓ + 1) + 2) ![P + 1, 0, 0] ![S, R.fl, Cl]
      ![P + 1 + 2 * ℓ, 0, 0] ![S, frame (binary ℓ con.1), Cl] := by
    refine (hm2.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s2 := dockRun hm2' c24FL (by decide) (hd24 o (P + 1))
    (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vb O S) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [dockH_c24FL, install_c24FL] at s2
  have s2' := s2.congr (hout' := hd24 o (P + 1 + 2 * ℓ))
    (tout' := bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.load (frame (binary ℓ con.1))) Vb O S)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have s3 := dockRun (nudge_run S (P + 1 + 2 * ℓ)) c24Nudge (by decide) (hd24 o (P + 1 + 2 * ℓ))
    (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.load (frame (binary ℓ con.1))) Vb O S)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c24Nudge, install_c24Nudge] at s3
  have s3' := s3.congr (hout' := hd24 o (P + 1 + 2 * ℓ + 1))
    (tout' := bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.load (frame (binary ℓ con.1))) Vb O S)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  exact (s1'.seq s2').seq s3'

theorem tgt_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL o : ℕ) (R : Regs) (O L0 restS : List Bool)
    (con : ℕ × ℕ) (hcL : 2 * k + 1 ≤ cL) :
    Step tgtM (tgtCost k) (hd24 o (L0.length + 1 + 2 * ℓ + 1))
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (List.replicate RV false) O (L0 ++ consRec ℓ k con ++ restS))
      (hd24 o (L0.length + 1 + 2 * ℓ + 1 + 2 * k + 1))
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (pad RV (frame (binary k con.2))) O
        (L0 ++ consRec ℓ k con ++ restS)) := by
  set S := L0 ++ consRec ℓ k con ++ restS with hS
  set P := L0.length with hP
  set Vb := List.replicate RV false
  set Vw := pad RV (frame (binary k con.2))
  set Cl := List.replicate cL false
  have eSV : (L0 ++ true :: frame (binary ℓ con.1)) ++ frame (binary k con.2) ++ restS = S := by
    rw [hS]; simp [consRec, List.append_assoc]
  obtain ⟨cv, hcv, hcvf⟩ := CopyO.copy_run (L0 ++ true :: frame (binary ℓ con.1)) (binary k con.2) restS [] Vb
  rw [eSV] at hcv hcvf
  have hvs : Step CopyO.machine (2 * (binary k con.2).length + 1) ![(L0 ++ true :: frame (binary ℓ con.1)).length, 0]
      ![S, Vb] ![(L0 ++ true :: frame (binary ℓ con.1)).length + 2 * (binary k con.2).length,
        2 * (binary k con.2).length + 1] ![S, Vw] := by
    refine ⟨cv, hcv, ?_, ?_, runFrom_steps_le _ _ _ _ hcv⟩
    · rw [hcvf]; funext j; fin_cases j <;> simp [CopyO.config, frame_length]
    · rw [hcvf]
      funext j; fin_cases j
      · rfl
      · show overlay ([] ++ frame (binary k con.2)) Vb = Vw
        rw [List.nil_append, overlay_blank]
  have e2 : (L0 ++ true :: frame (binary ℓ con.1)).length = P + 1 + 2 * ℓ + 1 := by
    simp [hP, frame_length]; omega
  rw [binary_length, e2] at hvs
  have hm4 := hvs.mask (cap := cL) selRec (by intro j hj; fin_cases j <;> first | rfl | simp [selRec] at hj) hcL
  have hm4' : Step (MaskedReset.machine CopyO.machine selRec) (2 * (2 * k + 1) + 2) ![P + 1 + 2 * ℓ + 1, 0, 0]
      ![S, Vb, Cl] ![P + 1 + 2 * ℓ + 1 + 2 * k, 0, 0] ![S, Vw, Cl] := by
    refine (hm4.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl
  have s4 := dockRun hm4' c24V (by decide) (hd24 o (P + 1 + 2 * ℓ + 1))
    (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vb O S) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [dockH_c24V, install_c24V] at s4
  have s4' := s4.congr (hout' := hd24 o (P + 1 + 2 * ℓ + 1 + 2 * k))
    (tout' := bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vw O S)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have s5 := dockRun (nudge_run S (P + 1 + 2 * ℓ + 1 + 2 * k)) c24Nudge (by decide)
    (hd24 o (P + 1 + 2 * ℓ + 1 + 2 * k)) (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vw O S)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c24Nudge, install_c24Nudge] at s5
  have s5' := s5.congr (hout' := hd24 o (P + 1 + 2 * ℓ + 1 + 2 * k + 1))
    (tout' := bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R Vw O S)
    (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  exact s4'.seq s5'

/-- The block on the loaded registers, with the target tape padded. -/
theorem rows_stage (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL s : ℕ) (R : Regs) (con : ℕ × ℕ)
    (rows backingO S : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (hr : R.r.length ≤ 2 * ℓ + 1)
    (hT : R.T.length = (tabWords p ℓ con.1 twoH).length)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m) :
    Step cRows (consCost ℓ twoH k plen) (hd24 rows.length s)
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.load (frame (binary ℓ con.1)))
        (pad RV (frame (binary k con.2))) (overlay rows backingO) S)
      (hd24 (rows.length + k * (2 * (twoH * ℓ - plen) + 3)) s)
      (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (R.next p ℓ twoH k plen con) (pad RV (frame (binary k con.2)))
        (overlay (rows ++ rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k) backingO) S) := by
  have hc := consRows_run p ℓ twoH k con.1 con.2 plen pfx R.a R.c R.x R.z R.mc cap cap2 cap3 cap4 m R.r R.b R.T
    rows backingO hℓ hkl hr hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4 hplen hT hm
  have hpd := hc.pad ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, RV, 0, 0, 0, 0, 0, 0, 0, 0]
  have hpd' : Step consRowsM (consCost ℓ twoH k plen) (hd22 rows.length)
      (bank22 p ℓ twoH plen pfx m cap cap2 cap3 cap4 (R.load (frame (binary ℓ con.1)))
        (pad RV (frame (binary k con.2))) (overlay rows backingO))
      (hd22 (rows.length + k * (2 * (twoH * ℓ - plen) + 3)))
      (bank22 p ℓ twoH plen pfx m cap cap2 cap3 cap4 (R.next p ℓ twoH k plen con) (pad RV (frame (binary k con.2)))
        (overlay (rows ++ rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k) backingO)) := by
    refine (hpd.congr_in ?_ ?_).congr ?_ ?_
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> first | rfl | simp [pad, bank22, Regs.load]
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> first | rfl | simp [pad, bank22, Regs.next]
  have he := hpd'.embed ![s, 0] ![S, List.replicate cL false]
  refine (he.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

theorem clr_stage (p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL o s k : ℕ) (R : Regs) (w O S : List Bool)
    (hw : w.length = k) (hRV : 2 * k + 1 ≤ RV) (hcL : 2 * k + 1 ≤ cL) :
    Step cClr (clrCost k) (hd24 o s) (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (pad RV (frame w)) O S)
      (hd24 o s) (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (List.replicate RV false) O S) := by
  have hcl := ClearFrame.clear_run w RV (by omega)
  rw [hw] at hcl
  have hcl' : Step ClearFrame.machine (2 * k + 1) (fun _ => 0) ![pad RV (frame w)] ![2 * k]
      ![List.replicate RV false] :=
    hcl.congr_in (by funext j; fin_cases j; rfl) rfl
  have hm7 := maskZero hcl' sel1 (by intro j hj; fin_cases j; simp [sel1] at hj) hcL
  have hm7' : Step (MaskedReset.machine ClearFrame.machine sel1) (2 * (2 * k + 1) + 2) (fun _ => 0)
      ![pad RV (frame w), List.replicate cL false] (fun _ => 0) ![List.replicate RV false, List.replicate cL false] := by
    refine (hm7.congr_in rfl ?_).congr rfl ?_ <;> funext j <;> fin_cases j <;> rfl
  have s7 := dockKeep hm7' c24Clr (by decide) (hd24 o s)
    (bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL R (pad RV (frame w)) O S) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [install_c24Clr] at s7
  exact s7.congr rfl (by funext j; fin_cases j <;> rfl)

/-- The bank before record `i`. -/
def loopH (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (i : ℕ) : Fin 24 → ℕ :=
  hd24 (rowsI p ℓ twoH k plen pfx cons i).length (i * recLen ℓ k)

def loopA (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO : List Bool) (i : ℕ) : Fin 24 → List Bool :=
  bank24 p ℓ twoH plen pfx m cap cap2 cap3 cap4 cL (regsAt p ℓ twoH k plen R0 cons i) (List.replicate RV false)
    (overlay (rowsI p ℓ twoH k plen pfx cons i) backingO) (consTape ℓ k cons stale)

theorem loop_step (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (h0 : R0.Ok ℓ twoH)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL) (i : ℕ) (hi : i < cons.length) :
    Step recBody (recCost ℓ twoH k plen) (loopH p ℓ twoH k plen pfx cons i)
      (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO i)
      (loopH p ℓ twoH k plen pfx cons (i + 1))
      (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO (i + 1)) := by
  have hok := regsAt_ok p ℓ twoH k plen R0 cons h0 i
  set R := regsAt p ℓ twoH k plen R0 cons i with hR
  set con := cons[i] with hcon
  set L0 := (cons.take i).flatMap (consRec ℓ k)
  set restS := (cons.drop (i + 1)).flatMap (consRec ℓ k) ++ false :: stale
  have hL0 : L0.length = i * recLen ℓ k := by
    rw [flatMap_consRec_length, List.length_take, Nat.min_eq_left (by omega)]
  have hsplit : consTape ℓ k cons stale = L0 ++ consRec ℓ k con ++ restS := consTape_split ℓ k cons stale i hi
  set rows := rowsI p ℓ twoH k plen pfx cons i
  have t1 := lab_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL rows.length R (overlay rows backingO) L0 restS con
    hok.2.1 hcL
  have t2 := tgt_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL rows.length (R.load (frame (binary ℓ con.1)))
    (overlay rows backingO) L0 restS con (by omega)
  have eP : L0.length + 1 + 2 * ℓ + 1 + 2 * k + 1 = (i + 1) * recLen ℓ k := by rw [hL0]; unfold recLen; ring
  have hT : R.T.length = (tabWords p ℓ con.1 twoH).length := by rw [hok.2.2, tabWords_length]
  have t3 := rows_stage p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL ((i + 1) * recLen ℓ k) R con rows backingO
    (L0 ++ consRec ℓ k con ++ restS) hℓ hkl hok.1 hT hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4 hplen hm
  have t4 := clr_stage p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL (rows.length + k * (2 * (twoH * ℓ - plen) + 3))
    ((i + 1) * recLen ℓ k) k (R.next p ℓ twoH k plen con) (binary k con.2)
    (overlay (rows ++ rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k) backingO) (L0 ++ consRec ℓ k con ++ restS)
    (binary_length k con.2) (by omega) (by omega)
  rw [eP] at t2
  have hall := ((t1.seq t2).seq t3).seq t4
  have eR : regsAt p ℓ twoH k plen R0 cons (i + 1) = R.next p ℓ twoH k plen con := regsAt_succ _ _ _ _ _ _ _ i hi
  have eO : rowsI p ℓ twoH k plen pfx cons (i + 1) = rows ++ rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k :=
    rowsI_succ _ _ _ _ _ _ _ i hi
  have eo : (rows ++ rowsOut (colTable p ℓ twoH con.1) plen pfx con.2 k).length =
      rows.length + k * (2 * (twoH * ℓ - plen) + 3) := by
    rw [List.length_append, rowsOut_length, colTable_length]
  unfold loopH loopA
  rw [eR, eO, hsplit, eo, ← hL0]
  exact hall

/-- **The rows of a whole system as one `Step`**: the records streamed, each through the block. -/
theorem loop_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (h0 : R0.Ok ℓ twoH)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL) :
    Step loopM (cons.length * (recCost ℓ twoH k plen + 2) + 1) (loopH p ℓ twoH k plen pfx cons 0)
      (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO 0)
      (loopH p ℓ twoH k plen pfx cons cons.length)
      (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO cons.length) := by
  let W : WhileBody 24 _ :=
    { body := recBody
      tape := 22
      bound := cons.length
      H := loopH p ℓ twoH k plen pfx cons
      A := loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO
      cost := fun _ => recCost ℓ twoH k plen
      step := fun i hi => loop_step p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO hℓ hkl h0
        hcap hcap2 hcap2' hcap2'' hcap3 hcap3' hcap4 hplen hm hRV hcL i hi
      cont := fun i hi => by
        show readTapeBit (consTape ℓ k cons stale) (i * recLen ℓ k) = true
        rw [consTape_read ℓ k cons stale i (by omega)]; simpa using hi
      halt := by
        show readTapeBit (consTape ℓ k cons stale) (cons.length * recLen ℓ k) = false
        rw [consTape_read ℓ k cons stale cons.length (le_refl _)]; simp }
  have h := W.run
  rw [W.rest_const (recCost ℓ twoH k plen) (fun _ => rfl)] at h
  exact h

/-- The system of a list is its constraints' systems, concatenated. -/
theorem system_flatMap (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    JoinElimination.system p ℓ twoH k plen pre cons =
      cons.flatMap fun con => JoinElimination.system p ℓ twoH k plen pre [con] := by
  unfold JoinElimination.system
  simp

/-- **The rows written for all records are the elimination system's records** (labels below `2^ℓ`). -/
theorem loop_system (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) (hp : GF.ModulusOk p ℓ) (hℓ : 1 ≤ ℓ)
    (hplen : plen ≤ twoH * ℓ) (hcons : ∀ con ∈ cons, con.1 < 2 ^ ℓ) :
    rowsI p ℓ twoH k plen pfx cons cons.length =
      ((JoinElimination.system p ℓ twoH k plen pfx cons).map (Gauss.rowBits (twoH * ℓ - plen))).flatMap frame := by
  unfold rowsI
  rw [List.take_length, system_flatMap, List.map_flatMap, List.flatMap_assoc]
  refine List.flatMap_congr fun con hcon => ?_
  exact rowsOut_system p ℓ twoH k plen pfx con.1 con.2 hp hℓ hplen (hcons con hcon)

end NearCubicWires.WireExponent3_5.SeedFix
