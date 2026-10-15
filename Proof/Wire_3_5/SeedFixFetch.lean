import Proof.Wire_3_5.SeedFixFoldRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

/-- A state's block: its entry records, then a terminator. -/
def blockWord (ents : List (List SExpr)) : List Bool := ents.flatMap entryRec ++ [false]

/-- The block's head at entry `j`. -/
def entPos (ents : List (List SExpr)) (j : ℕ) : ℕ := ((ents.take j).flatMap entryRec).length

theorem ents_split (ents : List (List SExpr)) (tail : List Bool) (j : ℕ) (hj : j < ents.length) :
    blockWord ents ++ tail =
      (ents.take j).flatMap entryRec ++ entryRec ents[j] ++ ((ents.drop (j + 1)).flatMap entryRec ++ false :: tail) := by
  have e : ents = ents.take j ++ ents[j] :: ents.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc blockWord ents ++ tail = blockWord (ents.take j ++ ents[j] :: ents.drop (j + 1)) ++ tail :=
        congrArg (fun l => blockWord l ++ tail) e
    _ = _ := by simp only [blockWord, List.flatMap_append, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append]

theorem ents_read (ents : List (List SExpr)) (tail : List Bool) (j : ℕ) (hj : j ≤ ents.length) :
    readTapeBit (blockWord ents ++ tail) (entPos ents j) = decide (j < ents.length) := by
  unfold entPos
  by_cases h : j < ents.length
  · rw [ents_split ents tail j h, decide_eq_true h, List.append_assoc]
    exact Streaming.read_append _ _ _
  · have hj' : j = ents.length := by omega
    subst hj'
    rw [decide_eq_false h, List.take_length, blockWord, List.append_assoc]
    exact Streaming.read_append _ _ _

theorem binary_inj (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) : binary W a = binary W b ↔ a = b := by
  constructor
  · intro h
    rw [← binary_value W a ha, ← binary_value W b hb, h]
  · rintro rfl; rfl

theorem binary_wrap (W : ℕ) : binary W (2 ^ W) = binary W 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [binary_getElem, binary_getElem]
  simp only [binary_length] at h1
  rw [Nat.testBit_two_pow_of_ne (by omega), Nat.zero_testBit]

/-! ## The bank (tapes 0–8 the fold's, 9 the entry counter, 10 the target, 11 the flag, 12 the unit cell, 13 a log) -/

def bank14 (B : List Bool) (s : FoldSt) (cI cT cA cC W j e cE : ℕ) (fl : Bool) : Fin 14 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false, frame (binary W j), frame (binary W e), [fl], [true], List.replicate cE false]

def hd14 (p : ℕ) : Fin 14 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def k14F : Fin 9 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem install_k14F (A : Fin 14 → List Bool) (v : Fin 9 → List Bool) :
    RecoveryRootRound.install k14F A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, A 9, A 10, A 11, A 12, A 13] := by
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
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14F (H : Fin 14 → ℕ) (v : Fin 9 → ℕ) :
    dockH k14F H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, H 9, H 10, H 11, H 12, H 13] := by
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
    | exact dockH_other _ _ _ _ (by decide)

def k14E : Fin 4 → Fin 14 := ![9, 10, 11, 13]

theorem install_k14E (A : Fin 14 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install k14E A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, v 1, v 2, A 12, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14E (H : Fin 14 → ℕ) (v : Fin 4 → ℕ) :
    dockH k14E H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 0, v 1, v 2, H 12, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

def k14I : Fin 3 → Fin 14 := ![9, 12, 13]

theorem install_k14I (A : Fin 14 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install k14I A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, A 10, A 11, v 1, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14I (H : Fin 14 → ℕ) (v : Fin 3 → ℕ) :
    dockH k14I H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 0, H 10, H 11, v 1, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_other _ _ _ _ (by decide)

def k14N : Fin 1 → Fin 14 := ![0]

theorem install_k14N (A : Fin 14 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install k14N A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14N (H : Fin 14 → ℕ) (v : Fin 1 → ℕ) :
    dockH k14N H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def selEq : Fin 3 → Bool := ![true, true, false]
def selInc : Fin 2 → Bool := ![true, false]

noncomputable def mulBr := RecoveryFocus.machine k14F rowsMulM
noncomputable def skipBr := RecoveryFocus.machine k14F rowsSkipM

/-- One entry: compare, past its marker, multiply or pass its rows, past its terminator, count it. -/
noncomputable def entBody :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine k14E (MaskedReset.machine (EqCell.machine false) selEq)) (RecoveryFocus.machine k14N nudgeM))
    (branchM (11 : Fin 14) mulBr skipBr)) (RecoveryFocus.machine k14N nudgeM))
    (RecoveryFocus.machine k14I (MaskedReset.machine IncFlag.machine selInc))

noncomputable def fetchM := StreamController.machine entBody 0

/-- The accumulator after the entries before `j`. -/
def fetchSt (s0 : FoldSt) (ents : List (List SExpr)) (e j : ℕ) : FoldSt :=
  if e < j then foldAt s0 (ents.getD e []) (ents.getD e []).length else s0

def flagAt (f0 : Bool) (e j : ℕ) : Bool := if j = 0 then f0 else decide (j - 1 = e)

def entCost (s0 : FoldSt) (ents : List (List SExpr)) (W e j : ℕ) : ℕ :=
  2 * (2 * W + 1) + 2 + 1 + 1 + 1 +
    ((if j = e then rowsMulCost s0 (ents.getD j []) else rowsSkipCost (ents.getD j [])) + 2) + 1 + 1 + 1 +
    (2 * (2 * W + 2) + 2)

theorem ent_step (s0 : FoldSt) (ents : List (List SExpr)) (tail : List Bool) (cI cT cA cC W e cE : ℕ) (f0 : Bool)
    (hN : ents.length = 2 ^ W) (he : e < ents.length) (hcE : 2 * W + 2 ≤ cE)
    (h0 : ∀ a ∈ s0.A, a.1 ≠ 0) (hrs : ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1)
    (hc : ∀ r (hr : r < (ents.getD e []).length), RowCaps (foldAt s0 (ents.getD e []) r) (ents.getD e [])[r] cI cT cA cC)
    (j : ℕ) (hj : j < ents.length) :
    Step entBody (entCost s0 ents W e j) (hd14 (entPos ents j))
      (bank14 (blockWord ents ++ tail) (fetchSt s0 ents e j) cI cT cA cC W j e cE (flagAt f0 e j))
      (hd14 (entPos ents (j + 1)))
      (bank14 (blockWord ents ++ tail) (fetchSt s0 ents e (j + 1)) cI cT cA cC W (j + 1) e cE (flagAt f0 e (j + 1))) := by
  set B := blockWord ents ++ tail
  set st := fetchSt s0 ents e j
  set fl := flagAt f0 e j
  set rs := ents[j]
  set pre := (ents.take j).flatMap entryRec ++ [true]
  set tl := (ents.drop (j + 1)).flatMap entryRec ++ false :: tail
  have eB : pre ++ rs.flatMap rowRec ++ false :: tl = B := by
    simp only [B]; rw [ents_split ents tail j hj]; simp [pre, tl, rs, entryRec]
  have hpre : pre.length = entPos ents j + 1 := by simp [pre, entPos]
  have hjW : j < 2 ^ W := hN ▸ hj
  have heW : e < 2 ^ W := hN ▸ he
  -- 1: compare the counter with the target
  have hq := EqCell.run false (binary W j) (binary W e) fl (by simp)
  have hflag : xor false (decide (binary W j = binary W e)) = decide (j = e) := by
    rw [Bool.false_xor]; congr 1; exact propext (binary_inj W j e hjW heW)
  rw [hflag, binary_length] at hq
  have hq' := hq.mask (cap := cE) selEq (by intro i _; fin_cases i <;> rfl) (by omega)
  have hq'' : Step (MaskedReset.machine (EqCell.machine false) selEq) (2 * (2 * W + 1) + 2) (fun _ => 0)
      ![frame (binary W j), frame (binary W e), [fl], List.replicate cE false] (fun _ => 0)
      ![frame (binary W j), frame (binary W e), [decide (j = e)], List.replicate cE false] := by
    refine (hq'.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s1 := dockKeep hq'' k14E (by decide) (hd14 (entPos ents j)) (bank14 B st cI cT cA cC W j e cE fl)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  rw [install_k14E] at s1
  -- 2: past the entry marker
  have s2 := dockRun (nudge_run B (entPos ents j)) k14N (by decide) (hd14 (entPos ents j))
    (bank14 B st cI cT cA cC W j e cE (decide (j = e))) (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_k14N, install_k14N] at s2
  -- 3: multiply or pass the entry's rows
  have hgd : ents.getD j [] = rs := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hr0 : rowPos pre rs 0 = entPos ents j + 1 := by simp [rowPos, hpre]
  have hbr : Step (branchM (11 : Fin 14) mulBr skipBr)
      ((if j = e then rowsMulCost s0 (ents.getD j []) else rowsSkipCost (ents.getD j [])) + 2)
      (hd14 (entPos ents j + 1)) (bank14 B st cI cT cA cC W j e cE (decide (j = e)))
      (hd14 (rowPos pre rs rs.length)) (bank14 B (fetchSt s0 ents e (j + 1)) cI cT cA cC W j e cE (decide (j = e))) := by
    by_cases hje : j = e
    · subst hje
      have hst : st = s0 := by simp only [st, fetchSt]; rw [if_neg (lt_irrefl j)]
      have hend : fetchSt s0 ents j (j + 1) = foldAt s0 rs rs.length := by
        rw [fetchSt, if_pos (Nat.lt_succ_self j), hgd]
      rw [hgd] at hrs hc
      rw [hst]
      have hm := rowsMul_run s0 rs pre tl cI cT cA cC h0 hrs hc
      rw [eB, hr0] at hm
      have hd := dockRun hm k14F (by decide) (hd14 (entPos ents j + 1))
        (bank14 B s0 cI cT cA cC W j j cE (decide (j = j))) (by intro i; fin_cases i <;> rfl)
        (by intro i; fin_cases i <;> rfl)
      rw [dockH_k14F, install_k14F] at hd
      have hb := branch_true (11 : Fin 14) skipBr hd (by show readTapeBit [decide (j = j)] 0 = true; simp [readTapeBit])
      rw [if_pos rfl, hgd, hend]
      refine hb.congr ?_ ?_
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
    · have hend : fetchSt s0 ents e (j + 1) = st := by
        simp only [st, fetchSt]
        by_cases hlt : e < j
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
      have hm := rowsSkip_run st rs pre tl cI cT cA cC
      rw [eB, hr0] at hm
      have hd := dockRun hm k14F (by decide) (hd14 (entPos ents j + 1))
        (bank14 B st cI cT cA cC W j e cE (decide (j = e))) (by intro i; fin_cases i <;> rfl)
        (by intro i; fin_cases i <;> rfl)
      rw [dockH_k14F, install_k14F] at hd
      have hb := branch_false (11 : Fin 14) mulBr hd (by show readTapeBit [decide (j = e)] 0 = false; simp [readTapeBit, hje])
      rw [if_neg hje, hgd, hend]
      refine hb.congr ?_ ?_
      · funext i; fin_cases i <;> rfl
      · funext i; fin_cases i <;> rfl
  -- 4: past the entry's terminator
  set st' := fetchSt s0 ents e (j + 1)
  have s4 := dockRun (nudge_run B (rowPos pre rs rs.length)) k14N (by decide) (hd14 (rowPos pre rs rs.length))
    (bank14 B st' cI cT cA cC W j e cE (decide (j = e))) (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_k14N, install_k14N] at s4
  -- 5: count the entry
  have hi := IncFlag.run W j [true] 0
  have hone : (readTapeBit [true] 0).toNat = 1 := rfl
  rw [hone] at hi
  have hi' := hi.mask (cap := cE) selInc (by intro i _; fin_cases i <;> rfl) hcE
  have hi'' : Step (MaskedReset.machine IncFlag.machine selInc) (2 * (2 * W + 2) + 2) (fun _ => 0)
      ![frame (binary W j), [true], List.replicate cE false] (fun _ => 0)
      ![frame (binary W (j + 1)), [true], List.replicate cE false] := by
    refine (hi'.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl
  have s5 := dockKeep hi'' k14I (by decide) (hd14 (rowPos pre rs rs.length + 1))
    (bank14 B st' cI cT cA cC W j e cE (decide (j = e))) (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl)
  rw [install_k14I] at s5
  have hall := ((((s1.congr (tout' := bank14 B st cI cT cA cC W j e cE (decide (j = e))) rfl
      (by funext i; fin_cases i <;> rfl)).seq
    (s2.congr (hout' := hd14 (entPos ents j + 1)) (tout' := bank14 B st cI cT cA cC W j e cE (decide (j = e)))
      (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq hbr).seq
    (s4.congr (hout' := hd14 (rowPos pre rs rs.length + 1)) (tout' := bank14 B st' cI cT cA cC W j e cE (decide (j = e)))
      (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))).seq
    (s5.congr (tout' := bank14 B st' cI cT cA cC W (j + 1) e cE (decide (j = e))) rfl
      (by funext i; fin_cases i <;> rfl))
  have eP : rowPos pre rs rs.length + 1 = entPos ents (j + 1) := by
    unfold rowPos entPos
    rw [List.take_length, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]
    simp [pre, entryRec, rs]
    omega
  have eF : flagAt f0 e (j + 1) = decide (j = e) := by simp [flagAt]
  unfold entCost
  rw [eP] at hall
  rw [eF]
  exact hall

/-- **One entry of the block multiplied in**: the scan over the block's `2^{2kh}` entries, the counter back to `0`. -/
theorem fetch_run (s0 : FoldSt) (ents : List (List SExpr)) (tail : List Bool) (cI cT cA cC W e cE : ℕ) (f0 : Bool)
    (hN : ents.length = 2 ^ W) (he : e < ents.length) (hcE : 2 * W + 2 ≤ cE)
    (h0 : ∀ a ∈ s0.A, a.1 ≠ 0) (hrs : ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1)
    (hc : ∀ r (hr : r < (ents.getD e []).length), RowCaps (foldAt s0 (ents.getD e []) r) (ents.getD e [])[r] cI cT cA cC) :
    Step fetchM (((List.range (ents.length - 0)).map (fun i => entCost s0 ents W e (0 + i) + 2)).sum + 1)
      (hd14 0) (bank14 (blockWord ents ++ tail) s0 cI cT cA cC W 0 e cE f0)
      (hd14 (entPos ents ents.length))
      (bank14 (blockWord ents ++ tail) (foldAt s0 (ents.getD e []) (ents.getD e []).length) cI cT cA cC W 0 e cE
        (decide (ents.length - 1 = e))) := by
  let L : WhileBody 14 _ :=
    { body := entBody
      tape := 0
      bound := ents.length
      H := fun j => hd14 (entPos ents j)
      A := fun j => bank14 (blockWord ents ++ tail) (fetchSt s0 ents e j) cI cT cA cC W j e cE (flagAt f0 e j)
      cost := fun j => entCost s0 ents W e j
      step := fun j hj => ent_step s0 ents tail cI cT cA cC W e cE f0 hN he hcE h0 hrs hc j hj
      cont := fun j hj => by
        show readTapeBit (blockWord ents ++ tail) (entPos ents j) = true
        rw [ents_read ents tail j (by omega)]; simpa using hj
      halt := by
        show readTapeBit (blockWord ents ++ tail) (entPos ents ents.length) = false
        rw [ents_read ents tail ents.length (le_refl _)]; simp }
  have h := L.run
  have e0 : fetchSt s0 ents e 0 = s0 := by simp [fetchSt]
  have e1 : fetchSt s0 ents e ents.length = foldAt s0 (ents.getD e []) (ents.getD e []).length := by
    simp [fetchSt, he]
  have e2 : flagAt f0 e 0 = f0 := rfl
  have e3 : flagAt f0 e ents.length = decide (ents.length - 1 = e) := by
    rw [flagAt, if_neg (by omega)]
  have e4 : binary W ents.length = binary W 0 := by rw [hN, binary_wrap]
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · rfl
  · show bank14 (blockWord ents ++ tail) (fetchSt s0 ents e 0) cI cT cA cC W 0 e cE (flagAt f0 e 0) = _
    rw [e0, e2]
  · rfl
  · show bank14 (blockWord ents ++ tail) (fetchSt s0 ents e ents.length) cI cT cA cC W ents.length e cE
      (flagAt f0 e ents.length) = _
    rw [e1, e3]
    unfold bank14
    rw [e4]

end NearCubicWires.WireExponent3_5.SeedFix
