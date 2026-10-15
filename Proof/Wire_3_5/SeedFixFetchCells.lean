import Proof.Wire_3_5.SeedFixFetchAll

/-! # C4.Sb, machine part 14: the eight entries of a walk multiplied in

A term group is the coefficient times the eight entries of state `t` at the walk's cells (`termsAt`, `walkRows`). For
each slot `k` the target register gets the record number `c_k + N²·t` of entry `(t, c_k)`, whose `W`-bit word is the
cell word followed by the state word (`W = 2kh + TW`). The whole-batch fetch then multiplies that entry's rows into the
accumulator (`fetchAll_run`).

Paper quantity of the main type: the accumulator `sfold A (walk rows)` (`fetchCells_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open Split Cells Valid Cons FetchAll

namespace FetchCells

/-! ## Slot maps -/

def t3P : Fin 2 → Fin 3 := ![0, 1]

theorem install_t3P (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install t3P A v = ![v 0, v 1, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t3P (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH t3P H v = ![v 0, v 1, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def t3N : Fin 1 → Fin 3 := ![0]

theorem install_t3N (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install t3N A v = ![v 0, A 1, A 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t3N (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH t3N H v = ![v 0, H 1, H 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def t3F : Fin 2 → Fin 3 := ![2, 1]

theorem install_t3F (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install t3F A v = ![A 0, v 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_t3F (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH t3F H v = ![H 0, v 1, v 0] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_other _ _ _ _ (by decide)

def fcT : Fin 4 → Fin 19 := ![15, 10, 16, 18]

theorem install_fcT (A : Fin 19 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install fcT A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 1, A 11, A 12, A 13, A 14, v 0, v 2, A 17, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_fcT (H : Fin 19 → ℕ) (v : Fin 4 → ℕ) :
    dockH fcT H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 1, H 11, H 12, H 13, H 14, v 0, v 2, H 17, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def fcF : Fin 15 → Fin 19 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem install_fcF (A : Fin 19 → List Bool) (v : Fin 15 → List Bool) :
    RecoveryRootRound.install fcF A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, A 15, A 16, A 17, A 18] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 10
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 11
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 12
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 13
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 14
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_fcF (H : Fin 19 → ℕ) (v : Fin 15 → ℕ) :
    dockH fcF H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, H 15, H 16, H 17, H 18] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_slot _ (by decide) _ _ 9
    | exact dockH_slot _ (by decide) _ _ 10
    | exact dockH_slot _ (by decide) _ _ 11
    | exact dockH_slot _ (by decide) _ _ 12
    | exact dockH_slot _ (by decide) _ _ 13
    | exact dockH_slot _ (by decide) _ _ 14
    | exact dockH_other _ _ _ _ (by decide)

def fcN : Fin 1 → Fin 19 := ![17]

theorem install_fcN (A : Fin 19 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install fcN A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 0, A 18] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_fcN (H : Fin 19 → ℕ) (v : Fin 1 → ℕ) :
    dockH fcN H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 0, H 18] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

/-! ## The target register (tapes 0 the cell stream, 1 the target, 2 the state word) -/

noncomputable def tgtInner := Composition.machine (Composition.machine (RecoveryFocus.machine t3P (PairsC.machine true))
  (RecoveryFocus.machine t3N nudgeM)) (RecoveryFocus.machine t3F frameT)

def selTg : Fin 3 → Bool := ![false, true, true]

/-- The target register: the cell word's pairs, then the state word framed; target and state heads rewound. -/
noncomputable def tgtM := MaskedReset.machine tgtInner selTg

def tgtInnerCost (a b : ℕ) : ℕ := (2 * a + 1) + 1 + 1 + 1 + (2 * b + 1 + 1 + 1)

theorem tgt_run (pre c tail tw TG0 : List Bool) (cG : ℕ) (hlen : TG0.length = 2 * (c.length + tw.length) + 1)
    (hcG : tgtInnerCost c.length tw.length ≤ cG) :
    Step tgtM (2 * tgtInnerCost c.length tw.length + 2) ![pre.length, 0, 0, 0]
      ![pre ++ frame c ++ tail, TG0, frame tw, List.replicate cG false]
      ![pre.length + (frame c).length, 0, 0, 0]
      ![pre ++ frame c ++ tail, frame (c ++ tw), frame tw, List.replicate cG false] := by
  set S := pre ++ frame c ++ tail
  have h1 := PairsC.run true pre c tail [] TG0
  simp only [owC, if_true, List.nil_append] at h1
  have h1' : Step (PairsC.machine true) (2 * c.length + 1) ![pre.length, 0] ![S, TG0]
      ![pre.length + 2 * c.length, (pairsOf c).length] ![S, overlay (pairsOf c) TG0] :=
    h1.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> simp [overlay, S])
  have s1 := dockRun h1' t3P (by decide) ![pre.length, 0, 0] ![S, TG0, frame tw]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_t3P, install_t3P] at s1
  have s2 := dockRun (nudge_run S (pre.length + 2 * c.length)) t3N (by decide)
    ![pre.length + 2 * c.length, (pairsOf c).length, 0] ![S, overlay (pairsOf c) TG0, frame tw]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_t3N, install_t3N] at s2
  have h3 := frameT_run [] tw [] (pairsOf c) TG0
  have h3' : Step frameT (2 * tw.length + 1 + 1 + 1) ![0, (pairsOf c).length] ![frame tw, overlay (pairsOf c) TG0]
      ![(frame tw).length, (pairsOf c ++ frame tw).length] ![frame tw, overlay (pairsOf c ++ frame tw) TG0] :=
    (h3.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> simp)).congr
      (by funext j; fin_cases j <;> simp) (by funext j; fin_cases j <;> simp)
  have s3 := dockRun h3' t3F (by decide) ![pre.length + 2 * c.length + 1, (pairsOf c).length, 0]
    ![S, overlay (pairsOf c) TG0, frame tw] (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_t3F, install_t3F] at s3
  have hall := ((s1.congr (hout' := ![pre.length + 2 * c.length, (pairsOf c).length, 0])
      (tout' := ![S, overlay (pairsOf c) TG0, frame tw]) (by funext j; fin_cases j <;> rfl)
      (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (hout' := ![pre.length + 2 * c.length + 1, (pairsOf c).length, 0])
      (tout' := ![S, overlay (pairsOf c) TG0, frame tw]) (by funext j; fin_cases j <;> rfl)
      (by funext j; fin_cases j <;> rfl))).seq s3
  have eT : overlay (pairsOf c ++ frame tw) TG0 = frame (c ++ tw) := by
    have hl : (pairsOf c ++ frame tw).length = TG0.length := by
      rw [hlen, List.length_append, pairsOf_length, frame_length]; ring
    rw [frame_append]
    simp [overlay, hl]
  rw [eT] at hall
  have hm := hall.mask (cap := cG) selTg (by intro j hj; fin_cases j <;> first | rfl | simp [selTg] at hj) hcG
  unfold tgtInnerCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j
    · show pre.length + 2 * c.length + 1 = pre.length + (frame c).length
      rw [frame_length]; omega
    all_goals rfl
  · funext j; fin_cases j <;> rfl

/-! ## The eight fetches (tapes 0–14 the fetch's bank, 15 the cell stream, 16 the state word, 17 the slot ruler, 18 the
target's log) -/

/-- The accumulator after the entries of the first `k` targets. -/
def fcSt (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (k : ℕ) : FoldSt :=
  (es.take k).foldl (fun s e => foldAt s (ents.getD e []) (ents.getD e []).length) s0

theorem fcSt_succ (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (k : ℕ) (hk : k < es.length) :
    fcSt s0 ents es (k + 1) = foldAt (fcSt s0 ents es k) (ents.getD es[k] []) (ents.getD es[k] []).length := by
  unfold fcSt
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

theorem sfold_append (A : SExpr) (L M : List SExpr) : sfold A (L ++ M) = sfold (sfold A L) M := by
  unfold sfold; rw [List.foldl_append]

/-- The product after all targets: the rows of every target entry, in order. -/
theorem fcSt_A (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) :
    (fcSt s0 ents es es.length).A = sfold s0.A (es.flatMap fun e => ents.getD e []) := by
  unfold fcSt
  rw [List.take_length]
  induction es generalizing s0 with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, sfold_append, foldAt_A]

def tgAt (e0 : ℕ) (es : List ℕ) (k : ℕ) : ℕ := if k = 0 then e0 else es.getD (k - 1) 0
def flAt (f0 : Bool) (n : ℕ) (es : List ℕ) (k : ℕ) : Bool := if k = 0 then f0 else decide (n - 1 = es.getD (k - 1) 0)

def fcH (cs : List (List Bool)) (k : ℕ) : Fin 19 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ((cs.take k).flatMap frame).length, 0, k, 0]

def fcA (B : List Bool) (s : FoldSt) (cI cT cA cC W e cE : ℕ) (fl : Bool) (cF : ℕ) (CL tw R8 : List Bool) (cG : ℕ) :
    Fin 19 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false, frame (binary W 0), frame (binary W e), [fl], [true], List.replicate cE false,
    List.replicate cF false, CL, frame tw, R8, List.replicate cG false]

/-- One slot: the target register, the whole-batch fetch, one ruler step. -/
noncomputable def fcBody := Composition.machine (Composition.machine (RecoveryFocus.machine fcT tgtM)
  (RecoveryFocus.machine fcF fetchAllM)) (RecoveryFocus.machine fcN nudgeM)

noncomputable def fcLoopM := StreamController.machine fcBody 17

def fcCost (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool)) (tw : List Bool) (W : ℕ)
    (k : ℕ) : ℕ :=
  (2 * tgtInnerCost (cs.getD k []).length tw.length + 2) + 1 + fetchAllCost (fcSt s0 ents es k) ents W (es.getD k 0) + 1 +
    1

/-- The hypotheses of the eight fetches. -/
structure FcOk (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cI cT cA cC W cE cF : ℕ) : Prop where
  hN : ents.length ≤ 2 ^ W
  he : ∀ e ∈ es, e < ents.length
  hcE : 2 * W + 2 ≤ cE
  h0 : ∀ k < es.length, ∀ a ∈ (fcSt s0 ents es k).A, a.1 ≠ 0
  hrs : ∀ e ∈ es, ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1
  hc : ∀ k (hk : k < es.length), ∀ r (hr : r < (ents.getD es[k] []).length),
    RowCaps (foldAt (fcSt s0 ents es k) (ents.getD es[k] []) r) (ents.getD es[k] [])[r] cI cT cA cC
  hcF : ∀ k (hk : k < es.length), fetchCost (fcSt s0 ents es k) ents W es[k] + 1 + (2 * (2 * W + 2) + 2) ≤ cF

theorem fc_step (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tailB CL tailC tw R8 : List Bool) (cI cT cA cC W e0 cE cF cG : ℕ) (f0 : Bool)
    (ok : FcOk s0 ents es cI cT cA cC W cE cF) (hCL : CL = cs.flatMap frame ++ tailC) (hlc : cs.length = es.length)
    (hcs : ∀ k (hk : k < es.length) (hk' : k < cs.length), binary W es[k] = cs[k] ++ tw)
    (hw : ∀ c ∈ cs, c.length + tw.length = W) (hcG : ∀ c ∈ cs, tgtInnerCost c.length tw.length ≤ cG)
    (k : ℕ) (hk : k < es.length) :
    Step fcBody (fcCost s0 ents es cs tw W k) (fcH cs k)
      (fcA (blockWord ents ++ tailB) (fcSt s0 ents es k) cI cT cA cC W (tgAt e0 es k) cE (flAt f0 ents.length es k) cF CL
        tw R8 cG)
      (fcH cs (k + 1))
      (fcA (blockWord ents ++ tailB) (fcSt s0 ents es (k + 1)) cI cT cA cC W (tgAt e0 es (k + 1)) cE
        (flAt f0 ents.length es (k + 1)) cF CL tw R8 cG) := by
  have hkc : k < cs.length := by omega
  set B := blockWord ents ++ tailB
  set st := fcSt s0 ents es k
  set c := cs[k]
  set e := es[k]
  set pre := (cs.take k).flatMap frame
  set fl := flAt f0 ents.length es k
  have hcm : c ∈ cs := List.getElem_mem hkc
  have eCL : CL = pre ++ frame c ++ ((cs.drop (k + 1)).flatMap frame ++ tailC) := by
    have ecs : cs = cs.take k ++ c :: cs.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hkc, List.take_append_drop]
    rw [hCL]
    conv_lhs => rw [ecs]
    simp [pre, List.append_assoc]
  -- 1: the target register
  have ht := tgt_run pre c ((cs.drop (k + 1)).flatMap frame ++ tailC) tw (frame (binary W (tgAt e0 es k))) cG
    (by rw [frame_length, binary_length, hw c hcm]) (hcG c hcm)
  rw [← eCL, ← hcs k hk hkc] at ht
  have s1 := dockRun ht fcT (by decide) (fcH cs k)
    (fcA B st cI cT cA cC W (tgAt e0 es k) cE fl cF CL tw R8 cG) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  rw [dockH_fcT, install_fcT] at s1
  -- 2: the whole-batch fetch
  have hf := fetchAll_run st ents tailB cI cT cA cC W e cE cF fl ok.hN (ok.he e (List.getElem_mem hk)) ok.hcE
    (ok.h0 k hk) (ok.hrs e (List.getElem_mem hk)) (ok.hc k hk) (ok.hcF k hk)
  have s2 := dockKeep hf fcF (by decide) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + (frame c).length, 0, k, 0]
    (fcA B st cI cT cA cC W e cE fl cF CL tw R8 cG) (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_fcF] at s2
  -- 3: one ruler step
  have s3 := dockRun (nudge_run R8 k) fcN (by decide)
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + (frame c).length, 0, k, 0]
    (fcA B (foldAt st (ents.getD e []) (ents.getD e []).length) cI cT cA cC W e cE (decide (ents.length - 1 = e)) cF CL
      tw R8 cG) (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_fcN, install_fcN] at s3
  have hall := ((s1.congr (hout' := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + (frame c).length, 0, k, 0])
      (tout' := fcA B st cI cT cA cC W e cE fl cF CL tw R8 cG) (by funext j; fin_cases j <;> rfl)
      (by funext j; fin_cases j <;> rfl)).seq
    (s2.congr (tout' := fcA B (foldAt st (ents.getD e []) (ents.getD e []).length) cI cT cA cC W e cE
      (decide (ents.length - 1 = e)) cF CL tw R8 cG) rfl (by funext j; fin_cases j <;> rfl))).seq s3
  have eSt : fcSt s0 ents es (k + 1) = foldAt st (ents.getD e []) (ents.getD e []).length := fcSt_succ s0 ents es k hk
  have eTg : tgAt e0 es (k + 1) = e := by
    simp only [tgAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have eFl : flAt f0 ents.length es (k + 1) = decide (ents.length - 1 = e) := by
    simp only [flAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have ePre : ((cs.take (k + 1)).flatMap frame).length = pre.length + (frame c).length := by
    rw [List.take_add_one, List.getElem?_eq_getElem hkc, Option.toList_some, List.flatMap_append]; simp [pre, c]
  have eH : fcH cs (k + 1) = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, pre.length + (frame c).length, 0, k + 1, 0] := by
    unfold fcH; rw [ePre]
  have eC : fcCost s0 ents es cs tw W k =
      (2 * tgtInnerCost c.length tw.length + 2) + 1 + fetchAllCost st ents W e + 1 + 1 := by
    unfold fcCost
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkc, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [eH, eSt, eTg, eFl, eC]
  exact hall.congr (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)

theorem fcLoop_run (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tailB CL tailC tw r8s : List Bool) (cI cT cA cC W e0 cE cF cG : ℕ) (f0 : Bool)
    (ok : FcOk s0 ents es cI cT cA cC W cE cF) (hCL : CL = cs.flatMap frame ++ tailC) (hlc : cs.length = es.length)
    (hcs : ∀ k (hk : k < es.length) (hk' : k < cs.length), binary W es[k] = cs[k] ++ tw)
    (hw : ∀ c ∈ cs, c.length + tw.length = W) (hcG : ∀ c ∈ cs, tgtInnerCost c.length tw.length ≤ cG) :
    Step fcLoopM (((List.range (es.length - 0)).map (fun i => fcCost s0 ents es cs tw W (0 + i) + 2)).sum + 1)
      (fcH cs 0)
      (fcA (blockWord ents ++ tailB) (fcSt s0 ents es 0) cI cT cA cC W (tgAt e0 es 0) cE (flAt f0 ents.length es 0) cF CL
        tw (List.replicate es.length true ++ false :: r8s) cG)
      (fcH cs es.length)
      (fcA (blockWord ents ++ tailB) (fcSt s0 ents es es.length) cI cT cA cC W (tgAt e0 es es.length) cE
        (flAt f0 ents.length es es.length) cF CL tw (List.replicate es.length true ++ false :: r8s) cG) := by
  set R8 := List.replicate es.length true ++ false :: r8s
  let L : WhileBody 19 _ :=
    { body := fcBody
      tape := 17
      bound := es.length
      H := fcH cs
      A := fun k => fcA (blockWord ents ++ tailB) (fcSt s0 ents es k) cI cT cA cC W (tgAt e0 es k) cE
        (flAt f0 ents.length es k) cF CL tw R8 cG
      cost := fcCost s0 ents es cs tw W
      step := fun k hk => fc_step s0 ents es cs tailB CL tailC tw R8 cI cT cA cC W e0 cE cF cG f0 ok hCL hlc hcs hw hcG k hk
      cont := fun k hk => by
        show readTapeBit R8 k = true
        exact read_rep_app es.length k (false :: r8s) hk
      halt := by
        show readTapeBit R8 es.length = false
        simpa using Streaming.read_append (List.replicate es.length true) r8s false }
  exact L.run

def selFC : Fin 19 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false,
    true, false]

/-- **The eight fetches**: every target entry multiplied in, every head back at cell 0. -/
noncomputable def fetchCellsM := MaskedReset.machine fcLoopM selFC

def fetchCellsCost (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool)) (tw : List Bool)
    (W : ℕ) : ℕ :=
  2 * (((List.range (es.length - 0)).map (fun i => fcCost s0 ents es cs tw W (0 + i) + 2)).sum + 1) + 2

def fcA20 (B : List Bool) (s : FoldSt) (cI cT cA cC W e cE : ℕ) (fl : Bool) (cF : ℕ) (CL tw R8 : List Bool)
    (cG cH : ℕ) : Fin 20 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false, frame (binary W 0), frame (binary W e), [fl], [true], List.replicate cE false,
    List.replicate cF false, CL, frame tw, R8, List.replicate cG false, List.replicate cH false]

theorem fetchCells_run (s0 : FoldSt) (ents : List (List SExpr)) (es : List ℕ) (cs : List (List Bool))
    (tailB CL tailC tw r8s : List Bool) (cI cT cA cC W e0 cE cF cG cH : ℕ) (f0 : Bool)
    (ok : FcOk s0 ents es cI cT cA cC W cE cF) (hCL : CL = cs.flatMap frame ++ tailC) (hlc : cs.length = es.length)
    (hcs : ∀ k (hk : k < es.length) (hk' : k < cs.length), binary W es[k] = cs[k] ++ tw)
    (hw : ∀ c ∈ cs, c.length + tw.length = W) (hcG : ∀ c ∈ cs, tgtInnerCost c.length tw.length ≤ cG)
    (hcH : ((List.range (es.length - 0)).map (fun i => fcCost s0 ents es cs tw W (0 + i) + 2)).sum + 1 ≤ cH) :
    Step fetchCellsM (fetchCellsCost s0 ents es cs tw W) (fun _ => 0)
      (fcA20 (blockWord ents ++ tailB) s0 cI cT cA cC W e0 cE f0 cF CL tw (List.replicate es.length true ++ false :: r8s)
        cG cH)
      (fun _ => 0)
      (fcA20 (blockWord ents ++ tailB) (fcSt s0 ents es es.length) cI cT cA cC W (tgAt e0 es es.length) cE
        (flAt f0 ents.length es es.length) cF CL tw (List.replicate es.length true ++ false :: r8s) cG cH) := by
  have hl := fcLoop_run s0 ents es cs tailB CL tailC tw r8s cI cT cA cC W e0 cE cF cG f0 ok hCL hlc hcs hw hcG
  have e0' : fcSt s0 ents es 0 = s0 := rfl
  have t0 : tgAt e0 es 0 = e0 := rfl
  have f0' : flAt f0 ents.length es 0 = f0 := rfl
  rw [e0', t0, f0'] at hl
  have hm := hl.mask (cap := cH) selFC (by intro j _; fin_cases j <;> rfl) hcH
  unfold fetchCellsCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext j <;> fin_cases j <;> rfl

end FetchCells

end NearCubicWires.WireExponent3_5.SeedFix
