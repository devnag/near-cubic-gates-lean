import Proof.Gates.Cells.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable {C : Ctx}

def a3 : Fin VV := ⟨103, by decide⟩
def a4 : Fin VV := ⟨104, by decide⟩
def a5 : Fin VV := ⟨105, by decide⟩
def a6 : Fin VV := ⟨106, by decide⟩
def a7 : Fin VV := ⟨107, by decide⟩
def a8 : Fin VV := ⟨108, by decide⟩

/-- Prelude values used here. -/
def pR : Fin VV := ⟨30, by decide⟩
def p2VW : Fin VV := ⟨31, by decide⟩
def p2K : Fin VV := ⟨32, by decide⟩
def p2KF : Fin VV := ⟨33, by decide⟩
def pTH : Fin VV := ⟨34, by decide⟩
def pTL : Fin VV := ⟨35, by decide⟩
/-- The pass flag of the current cell. -/
def cPass : Fin VV := ⟨40, by decide⟩

/-- A record passes (machine form of `Recs.recOK`). -/
def recOKm (Vv Kk KF th tl rec : ℕ) : Prop :=
  (rec / Vv % Kk / KF = 1 → rec % Vv < th) ∧ (rec / Vv % Kk / KF = 2 → rec % Vv < tl)

instance (Vv Kk KF th tl rec : ℕ) : Decidable (recOKm Vv Kk KF th tl rec) := by unfold recOKm; infer_instance

/-- Test one record in `t3`: clear `cPass` if it fails. Scratch `a3 … a8`. -/
def testRec : St VV MM :=
  .seq (.op (.dm t3 p2VW a3 a4)) (.seq (.op (.dm a3 p2K a5 a6)) (.seq (.op (.dm a6 p2KF a7 a8))
    (.seq (.ite (.eq a7 v1) (.ite (.lt a4 pTH) skipS (.op (.zero cPass))) skipS)
      (.ite (.eq a7 v2) (.ite (.lt a4 pTL) skipS (.op (.zero cPass))) skipS))))

def testT : List (Fin VV) := [a3, a4, a5, a6, a7, a8, cPass, vJ]

theorem testRec_spec (a : DS VV MM) (hc : Cst a) (hV : 0 < a.env p2VW) (hK : 0 < a.env p2K) (hKF : 0 < a.env p2KF)
    (hW1 : 2 * a.env p2VW ≤ 2 ^ C.Wd) (hW2 : 2 * a.env p2K ≤ 2 ^ C.Wd) (hW3 : 2 * a.env p2KF ≤ 2 ^ C.Wd) :
    Hs C testRec a 20 (fun b => b.env cPass = (if recOKm (a.env p2VW) (a.env p2K) (a.env p2KF) (a.env pTH)
      (a.env pTL) (a.env t3) then a.env cPass else 0) ∧ b.sh = a.sh ∧ Fr a b testT) := by
  set rec := a.env t3
  set Vv := a.env p2VW
  set Kk := a.env p2K
  set KF := a.env p2KF
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (1 + (3 + 3 + 1) + 1) + 1)
    (hs_dm C t3 p2VW a3 a4 a (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hV hW1)
    (fun b1 hb1 => ?_)) (by norm_num) (fun _ h => h)
  subst hb1
  set b1 := (a.set a3 (rec / Vv)).set a4 (rec % Vv) with hb1
  have e1 : b1.env p2K = Kk := by show _ = a.env p2K; simp only [hb1]; vsimp []
  have e2 : b1.env p2KF = KF := by show _ = a.env p2KF; simp only [hb1]; vsimp []
  have e3 : b1.env a3 = rec / Vv := by simp only [hb1]; vsimp []
  have e4 : b1.env a4 = rec % Vv := by simp only [hb1]; vsimp []
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (3 + 3 + 1) + 1)
    (hs_dm C a3 p2K a5 a6 b1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e1]; exact hK) (by rw [e1]; exact hW2)) (fun b2 hb2 => ?_)) (by norm_num) (fun _ h => h)
  subst hb2
  set b2 := (b1.set a5 (b1.env a3 / b1.env p2K)).set a6 (b1.env a3 % b1.env p2K) with hb2
  have f2 : b2.env p2KF = KF := by simp only [hb2]; vsimp [e2]
  have f6 : b2.env a6 = rec / Vv % Kk := by simp only [hb2]; vsimp [e3, e1]
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 3 + 3 + 1)
    (hs_dm C a6 p2KF a7 a8 b2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [f2]; exact hKF) (by rw [f2]; exact hW3)) (fun b3 hb3 => ?_)) (by norm_num) (fun _ h => h)
  subst hb3
  set b3 := (b2.set a7 (b2.env a6 / b2.env p2KF)).set a8 (b2.env a6 % b2.env p2KF) with hb3
  have g7 : b3.env a7 = rec / Vv % Kk / KF := by simp only [hb3]; vsimp [f6, f2]
  have g4 : b3.env a4 = rec % Vv := by simp only [hb3, hb2]; vsimp [e4]
  have gTH : b3.env pTH = a.env pTH := by simp only [hb3, hb2, hb1]; vsimp []
  have gTL : b3.env pTL = a.env pTL := by simp only [hb3, hb2, hb1]; vsimp []
  have gP : b3.env cPass = a.env cPass := by simp only [hb3, hb2, hb1]; vsimp []
  have g1 : b3.env v1 = 1 := by simp only [hb3, hb2, hb1]; vsimp [hc.one]
  have g2 : b3.env v2 = 2 := by simp only [hb3, hb2, hb1]; vsimp [hc.two]
  have gfr : Fr a b3 testT := by
    intro y hy
    simp only [testT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [hb3, hb2, hb1]
    rw [DS.set_env_ne _ _ hy.2.2.2.2.2.1, DS.set_env_ne _ _ hy.2.2.2.2.1, DS.set_env_ne _ _ hy.2.2.2.1,
      DS.set_env_ne _ _ hy.2.2.1, DS.set_env_ne _ _ hy.2.1, DS.set_env_ne _ _ hy.1]
  -- the two tests
  have T1 : Hs C (.ite (.eq a7 v1) (.ite (.lt a4 pTH) skipS (.op (.zero cPass))) skipS) b3 3
      (fun e => e.env cPass = (if (rec / Vv % Kk / KF = 1 → rec % Vv < a.env pTH) then a.env cPass else 0) ∧
        e.sh = b3.sh ∧ Fr b3 e [cPass, vJ]) := by
    refine Hs.ite (show a7 ≠ v1 by decide) (fun h1 => ?_) (fun h1 => ?_)
    · simp only [Cnd.eval, g7, g1, decide_eq_true_eq] at h1
      refine Hs.ite (show a4 ≠ pTH by decide) (fun h2 => ?_) (fun h2 => ?_)
      · simp only [Cnd.eval, g4, gTH, decide_eq_true_eq] at h2
        refine Hs.mono (skip_spec b3) (by norm_num) ?_
        rintro e rfl
        exact ⟨by vsimp [gP, h1, h2], rfl, Fr.set _ _ (by decide)⟩
      · simp only [Cnd.eval, g4, gTH, decide_eq_false_iff_not] at h2
        refine Hs.mono (hs_zero C cPass b3) (by norm_num) ?_
        rintro e rfl
        exact ⟨by vsimp [h1, h2], rfl, Fr.set _ _ (by decide)⟩
    · simp only [Cnd.eval, g7, g1, decide_eq_false_iff_not] at h1
      refine Hs.mono (skip_spec b3) (by norm_num) ?_
      rintro e rfl
      exact ⟨by vsimp [gP, h1], rfl, Fr.set _ _ (by decide)⟩
  refine Hs.mono (Hs.seq (t1 := 3) (t2 := 3) T1 (fun b4 ⟨h41, h42, h43⟩ => ?_)) (by norm_num) (fun _ h => h)
  have h4v2 : b4.env v2 = 2 := by rw [h43 v2 (by decide), g2]
  have h47 : b4.env a7 = rec / Vv % Kk / KF := by rw [h43 a7 (by decide), g7]
  have h44 : b4.env a4 = rec % Vv := by rw [h43 a4 (by decide), g4]
  have h4L : b4.env pTL = a.env pTL := by rw [h43 pTL (by decide), gTL]
  refine Hs.ite (show a7 ≠ v2 by decide) (fun h1 => ?_) (fun h1 => ?_)
  · simp only [Cnd.eval, h47, h4v2, decide_eq_true_eq] at h1
    refine Hs.ite (show a4 ≠ pTL by decide) (fun h2 => ?_) (fun h2 => ?_)
    · simp only [Cnd.eval, h44, h4L, decide_eq_true_eq] at h2
      refine Hs.mono (skip_spec b4) (by norm_num) ?_
      rintro e rfl
      refine ⟨?_, by simp [h42, hb3, hb2, hb1], Fr.trans gfr (Fr.trans (Fr.weaken h43 (by decide))
        (Fr.set _ _ (by decide)))⟩
      vsimp [h41]
      unfold recOKm
      by_cases hk1 : rec / Vv % Kk / KF = 1
      · simp [hk1] at h1 ⊢
      · simp [hk1, h1, h2]
    · simp only [Cnd.eval, h44, h4L, decide_eq_false_iff_not] at h2
      refine Hs.mono (hs_zero C cPass b4) (by norm_num) ?_
      rintro e rfl
      refine ⟨?_, by simp [h42, hb3, hb2, hb1], Fr.trans gfr (Fr.trans (Fr.weaken h43 (by decide))
        (Fr.set _ _ (by decide)))⟩
      vsimp []
      unfold recOKm
      simp [h1, h2]
  · simp only [Cnd.eval, h47, h4v2, decide_eq_false_iff_not] at h1
    refine Hs.mono (skip_spec b4) (by norm_num) ?_
    rintro e rfl
    refine ⟨?_, by simp [h42, hb3, hb2, hb1], Fr.trans gfr (Fr.trans (Fr.weaken h43 (by decide))
      (Fr.set _ _ (by decide)))⟩
    vsimp [h41]
    unfold recOKm
    simp [h1]

theorem putAt_split (A B : List ℕ) (v : ℕ) : putAt (A ++ B) A.length v = A ++ v :: B.drop 1 := by
  unfold putAt
  cases B with
  | nil => simp
  | cons b B => simp [List.set_append_right]

/-- **One cell's block**: `R` records into store `sCT`, the flag `cPass` = all moment records pass. -/
def blkP : St VV MM :=
  .seq (.op (.zero cPass)) (.seq (.op (.inc cPass)) (.seq (.op (.rwM sCT))
    (forS c2 pR (.seq rdRec (.seq (.op (.wrM sCT t3)) testRec)))))

def blkT : List (Fin VV) := [cPass, c2, t0, t1, t3, a3, a4, a5, a6, a7, a8, vJ]

/-- What `blkP` assumes of the prelude values. -/
structure TestVals (a : DS VV MM) (C : Ctx) : Prop where
  hV : 0 < a.env p2VW
  hK : 0 < a.env p2K
  hKF : 0 < a.env p2KF
  w1 : 2 * a.env p2VW ≤ 2 ^ C.Wd
  w2 : 2 * a.env p2K ≤ 2 ^ C.Wd
  w3 : 2 * a.env p2KF ≤ 2 ^ C.Wd

theorem TestVals.fr {a b : DS VV MM} (h : TestVals a C) (hf : Fr a b blkT) : TestVals b C := by
  have e1 : b.env p2VW = a.env p2VW := hf _ (by decide)
  have e2 : b.env p2K = a.env p2K := hf _ (by decide)
  have e3 : b.env p2KF = a.env p2KF := hf _ (by decide)
  exact ⟨by rw [e1]; exact h.hV, by rw [e2]; exact h.hK, by rw [e3]; exact h.hKF, by rw [e1]; exact h.w1,
    by rw [e2]; exact h.w2, by rw [e3]; exact h.w3⟩

theorem blkP_spec (a : DS VV MM) (hc : Cst a) (htv : TestVals a C) (W : ℕ) (B : List ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = B.flatMap (fun x => RepairOrdinary.frame (binary W x)) ++ rest)
    (hB : ∀ x ∈ B, x < 2 ^ W) (hW : W + 2 ≤ C.Wd) (hR : a.env pR = B.length) (hRW : B.length < 2 ^ C.Wd)
    (hold : (a.ram sCT).length ≤ B.length ∧ a.rc sCT ≤ (a.ram sCT).length) :
    Hs C blkP a (1 + (1 + (a.rc sCT + 1 + (B.length * (12 * W + 12 + 1 + (1 + 1 + 20) + 4) + 4) + 1) + 1) + 1)
      (fun b => b.env cPass = (if B.all (fun x => decide (recOKm (a.env p2VW) (a.env p2K) (a.env p2KF)
          (a.env pTH) (a.env pTL) x)) then 1 else 0) ∧ b.ram = Function.update a.ram sCT B ∧
        b.rc = Function.update a.rc sCT B.length ∧ b.ip = a.ip + B.length * (2 * W + 1) ∧
        b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b blkT) := by
  set ok := fun x => decide (recOKm (a.env p2VW) (a.env p2K) (a.env p2KF) (a.env pTH) (a.env pTL) x) with hok
  have h2 : 1 < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
  refine Hs.seq (hs_zero C cPass a) (fun b1 hb1 => ?_)
  subst hb1
  refine Hs.seq (hs_inc C cPass _ (by vsimp []; omega)) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (hs_rwM C sCT _) (fun b3 hb3 => ?_)
  subst hb3
  set s0 := ((a.set cPass 0).set cPass ((a.set cPass 0).env cPass + 1)).rew sCT with hs0
  set old := a.ram sCT
  let I : ℕ → DS VV MM → Prop := fun k e => e.env cPass = (if (B.take k).all ok then 1 else 0) ∧
    e.ram = Function.update a.ram sCT (B.take k ++ old.drop k) ∧ e.rc = Function.update a.rc sCT k ∧
    e.ip = a.ip + k * (2 * W + 1) ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧
    Fr a e blkT
  have hl := forS_spec' (C := C) c2 pR (by decide) (.seq rdRec (.seq (.op (.wrM sCT t3)) testRec)) s0 B.length hRW I
    (12 * W + 12 + 1 + (1 + 1 + 20))
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, i2, i3, i4, i5,
      i6, i7, i8, Fr.trans i9 (Fr.set e v (by decide))⟩)
    ⟨by simp [s0, DS.rew], by simp [s0, DS.rew, old], by simp [s0, DS.rew], by simp [s0, DS.rew],
      by simp [s0, DS.rew], by simp [s0, DS.rew], by simp [s0, DS.rew], by simp [s0, DS.rew],
      Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩ (by simp only [s0, DS.rew]; vsimp [hR]) ?_
  · refine Hs.mono hl le_rfl ?_
    rintro e ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, _, _⟩
    refine ⟨by rw [i1, List.take_length], by rw [i2, List.take_length, List.drop_eq_nil_of_le hold.1,
      List.append_nil], by rw [i3], i4, i5, i6, i7, i8, i9⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ hek hem
    have hc' : Cst e := Cst.of_fr hc i9 (by decide)
    -- the record
    have hdrop : C.inp.drop e.ip = RepairOrdinary.frame (binary W B[k]) ++
        ((B.drop (k + 1)).flatMap (fun x => RepairOrdinary.frame (binary W x)) ++ rest) := by
      rw [i4, ← List.drop_drop, hcw]
      have hsplit : B = B.take k ++ B[k] :: B.drop (k + 1) := by
        conv_lhs => rw [← List.take_append_drop k B]
        rw [List.drop_eq_getElem_cons hk]
      have hlen : ((B.take k).flatMap fun x => RepairOrdinary.frame (binary W x)).length = k * (2 * W + 1) := by
        rw [List.length_flatMap]
        have : ∀ x ∈ B.take k, (RepairOrdinary.frame (binary W x)).length = 2 * W + 1 := fun x _ => by
          rw [frame_length', binary_length]
        rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_take,
          Nat.min_eq_left hk.le, smul_eq_mul]
      conv_lhs => rw [hsplit]
      rw [List.flatMap_append, List.append_assoc, ← hlen, List.drop_left, List.flatMap_cons, List.append_assoc]
    refine Hs.seq (t1 := 12 * W + 12) (t2 := 1 + 20 + 1) (rdRec_spec e hc' W B[k] _ hdrop (hB _ (List.getElem_mem hk)) hW)
      (fun f ⟨f1, f2, f3, f4⟩ => ?_)
    simp only [Prod.mk.injEq] at f3
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := f3
    have hrc : f.rc sCT ≤ (f.ram sCT).length := by
      rw [g3, g2, i3, i2]; simp; omega
    refine Hs.seq (hs_wrM C sCT t3 f hrc) (fun f2' hf2 => ?_)
    subst hf2
    have hcf : Cst f := Cst.of_fr hc' f4 (by decide)
    have hc2 : Cst (f.put sCT (f.env t3)) := ⟨hcf.z, hcf.one, hcf.two⟩
    have hfr4 : Fr a (f.put sCT (f.env t3)) blkT := Fr.trans i9 (fun y hy => f4 y (fun h => hy (by revert h; simp [blkT]; tauto)))
    have htv2 : TestVals (f.put sCT (f.env t3)) C := TestVals.fr htv hfr4
    refine Hs.mono (testRec_spec _ hc2 htv2.hV htv2.hK htv2.hKF htv2.w1 htv2.w2 htv2.w3) le_rfl ?_
    rintro r ⟨r1, r2, r3⟩
    have hfr : Fr a r blkT := Fr.trans i9 (Fr.trans (Fr.weaken f4 (by decide)) (Fr.weaken r3 (by decide)))
    have hval : ∀ y ∈ [p2VW, p2K, p2KF, pTH, pTL], (f.put sCT (f.env t3)).env y = a.env y := by
      intro y hy
      have := Fr.trans i9 (Fr.weaken f4 (by decide)) y (by revert hy; decide +revert)
      exact this
    have hP : (f.put sCT (f.env t3)).env cPass = (if (B.take k).all ok then 1 else 0) := by
      show f.env cPass = _; rw [f4 cPass (by decide), i1]
    have ht3 : (f.put sCT (f.env t3)).env t3 = B[k] := f1
    simp only [DS.sh, Prod.mk.injEq] at r2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := r2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩, ?_, ?_⟩
    · simp only [hP, ht3, hval p2VW (by simp), hval p2K (by simp), hval p2KF (by simp), hval pTH (by simp),
        hval pTL (by simp)] at r1
      rw [r1, List.take_succ_eq_append_getElem hk, List.all_append]
      by_cases hA : (B.take k).all ok <;> by_cases hb : recOKm (a.env p2VW) (a.env p2K) (a.env p2KF) (a.env pTH)
        (a.env pTL) B[k] <;> simp [hA, hb, hok]
    · rw [q3]; simp only [DS.put]
      rw [g2, i2, g3, i3]
      funext m; by_cases hm : m = sCT
      · subst hm
        simp only [Function.update_self]
        have hlenk : (B.take k).length = k := by simp; omega
        have hput := putAt_split (B.take k) (old.drop k) (f.env t3)
        rw [hlenk] at hput
        rw [hput, f1, List.take_succ_eq_append_getElem hk]
        simp only [List.drop_drop, List.append_assoc, List.singleton_append]
      · simp [Function.update_of_ne hm]
    · rw [q4]; simp only [DS.put]; rw [g3, i3]; funext m; by_cases hm : m = sCT
      · subst hm; simp
      · simp [Function.update_of_ne hm]
    · rw [q1]; simp only [DS.put]; rw [f2, i4]; ring
    · rw [q2]; simp only [DS.put]; rw [g1, i5]
    · rw [q5]; simp only [DS.put]; rw [g4, i6]
    · rw [q6]; simp only [DS.put]; rw [g5, i7]
    · rw [q7]; simp only [DS.put]; rw [g6, i8]
    · rw [r3 c2 (by decide)]; show f.env c2 = k; rw [f4 c2 (by decide)]; exact hek
    · rw [r3 pR (by decide)]; show f.env pR = B.length; rw [f4 pR (by decide)]; exact hem

end NearCubicGates.Close.Cells
