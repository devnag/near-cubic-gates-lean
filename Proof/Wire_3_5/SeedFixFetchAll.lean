import Proof.Wire_3_5.SeedFixCons

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

namespace FetchAll

/-! ## The scan over at most `2^W` records -/

theorem ent_step' (s0 : FoldSt) (ents : List (List SExpr)) (tail : List Bool) (cI cT cA cC W e cE : ℕ) (f0 : Bool)
    (hN : ents.length ≤ 2 ^ W) (he : e < ents.length) (hcE : 2 * W + 2 ≤ cE)
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
  have hjW : j < 2 ^ W := by omega
  have heW : e < 2 ^ W := by omega
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

theorem fetchLoop_run (s0 : FoldSt) (ents : List (List SExpr)) (tail : List Bool) (cI cT cA cC W e cE : ℕ) (f0 : Bool)
    (hN : ents.length ≤ 2 ^ W) (he : e < ents.length) (hcE : 2 * W + 2 ≤ cE)
    (h0 : ∀ a ∈ s0.A, a.1 ≠ 0) (hrs : ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1)
    (hc : ∀ r (hr : r < (ents.getD e []).length), RowCaps (foldAt s0 (ents.getD e []) r) (ents.getD e [])[r] cI cT cA cC) :
    Step fetchM (((List.range (ents.length - 0)).map (fun i => entCost s0 ents W e (0 + i) + 2)).sum + 1)
      (hd14 0) (bank14 (blockWord ents ++ tail) s0 cI cT cA cC W 0 e cE f0)
      (hd14 (entPos ents ents.length))
      (bank14 (blockWord ents ++ tail) (foldAt s0 (ents.getD e []) (ents.getD e []).length) cI cT cA cC W ents.length e
        cE (decide (ents.length - 1 = e))) := by
  let L : WhileBody 14 _ :=
    { body := entBody
      tape := 0
      bound := ents.length
      H := fun j => hd14 (entPos ents j)
      A := fun j => bank14 (blockWord ents ++ tail) (fetchSt s0 ents e j) cI cT cA cC W j e cE (flagAt f0 e j)
      cost := fun j => entCost s0 ents W e j
      step := fun j hj => ent_step' s0 ents tail cI cT cA cC W e cE f0 hN he hcE h0 hrs hc j hj
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
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · rfl
  · show bank14 (blockWord ents ++ tail) (fetchSt s0 ents e 0) cI cT cA cC W 0 e cE (flagAt f0 e 0) = _
    rw [e0, e2]
  · rfl
  · show bank14 (blockWord ents ++ tail) (fetchSt s0 ents e ents.length) cI cT cA cC W ents.length e cE
      (flagAt f0 e ents.length) = _
    rw [e1, e3]

/-! ## The counter cleared, the block head rewound -/

def k14Z : Fin 4 → Fin 14 := ![9, 10, 12, 13]

theorem install_k14Z (A : Fin 14 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install k14Z A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, v 1, A 11, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14Z (H : Fin 14 → ℕ) (v : Fin 4 → ℕ) :
    dockH k14Z H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, v 0, v 1, H 11, v 2, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_other _ _ _ _ (by decide)

noncomputable def clearM := RecoveryFocus.machine k14Z (MaskedReset.machine (ZipFlag.machine clearG) sel3)

theorem clear_step (B : List Bool) (s : FoldSt) (cI cT cA cC W n e cE p : ℕ) (fl : Bool) (hcE : 2 * W + 2 ≤ cE) :
    Step clearM (2 * (2 * W + 2) + 2) (hd14 p) (bank14 B s cI cT cA cC W n e cE fl) (hd14 p)
      (bank14 B s cI cT cA cC W 0 e cE fl) := by
  have h0 := GF2.zipStage cE clearG (binary W n) (binary W e) true (by simp [binary_length]) (by simpa using hcE)
  rw [zipWith_clear _ _ (by simp [binary_length]), binary_length,
    show List.replicate W false = binary W 0 from (binary_zero W).symm] at h0
  have h1 := dockKeep h0 k14Z (by decide) (hd14 p) (bank14 B s cI cT cA cC W n e cE fl)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_k14Z] at h1
  exact h1.congr rfl (by funext i; fin_cases i <;> rfl)

def selF0 : Fin 14 → Bool := ![true, false, false, false, false, false, false, false, false, false, false, false, false,
  false]

/-- **The whole-batch fetch**: the scan, the counter cleared, the block head rewound. -/
noncomputable def fetchAllM := MaskedReset.machine (Composition.machine fetchM clearM) selF0

def fetchCost (s0 : FoldSt) (ents : List (List SExpr)) (W e : ℕ) : ℕ :=
  ((List.range (ents.length - 0)).map (fun i => entCost s0 ents W e (0 + i) + 2)).sum + 1

def fetchAllCost (s0 : FoldSt) (ents : List (List SExpr)) (W e : ℕ) : ℕ :=
  2 * (fetchCost s0 ents W e + 1 + (2 * (2 * W + 2) + 2)) + 2

/-- The fetch's bank and the rewind's log. -/
def bank15 (B : List Bool) (s : FoldSt) (cI cT cA cC W e cE : ℕ) (fl : Bool) (cF : ℕ) : Fin 15 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false, frame (binary W 0), frame (binary W e), [fl], [true], List.replicate cE false,
    List.replicate cF false]

theorem fetchAll_run (s0 : FoldSt) (ents : List (List SExpr)) (tail : List Bool) (cI cT cA cC W e cE cF : ℕ) (f0 : Bool)
    (hN : ents.length ≤ 2 ^ W) (he : e < ents.length) (hcE : 2 * W + 2 ≤ cE)
    (h0 : ∀ a ∈ s0.A, a.1 ≠ 0) (hrs : ∀ V ∈ ents.getD e [], ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1)
    (hc : ∀ r (hr : r < (ents.getD e []).length), RowCaps (foldAt s0 (ents.getD e []) r) (ents.getD e [])[r] cI cT cA cC)
    (hcF : fetchCost s0 ents W e + 1 + (2 * (2 * W + 2) + 2) ≤ cF) :
    Step fetchAllM (fetchAllCost s0 ents W e) (fun _ => 0) (bank15 (blockWord ents ++ tail) s0 cI cT cA cC W e cE f0 cF)
      (fun _ => 0)
      (bank15 (blockWord ents ++ tail) (foldAt s0 (ents.getD e []) (ents.getD e []).length) cI cT cA cC W e cE
        (decide (ents.length - 1 = e)) cF) := by
  have h1 := fetchLoop_run s0 ents tail cI cT cA cC W e cE f0 hN he hcE h0 hrs hc
  have h2 := clear_step (blockWord ents ++ tail) (foldAt s0 (ents.getD e []) (ents.getD e []).length) cI cT cA cC W
    ents.length e cE (entPos ents ents.length) (decide (ents.length - 1 = e)) hcE
  have hall := h1.seq h2
  have hm := hall.mask (cap := cF) selF0 (by intro i _; fin_cases i <;> rfl) hcF
  unfold fetchAllCost fetchCost
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> fin_cases i <;> rfl

end FetchAll

end NearCubicWires.WireExponent3_5.SeedFix
