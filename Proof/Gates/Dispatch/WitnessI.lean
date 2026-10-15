import Proof.Gates.Dispatch.WitnessH

/-!
# Fragment (W), part I: printing the coordinates (`natWord k`, then every set bit of the mask in order)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

def coordPrint : St VV :=
  .seq (.op (.copy t3 pK)) (.seq emitNat (.seq (.op (.copy xT vBM)) (.seq (.op (.zero xI))
    (.loop (.lt xI vN) (.seq (.op (.dm xT v2 xQ xR)) (.seq (.ite (.eq xR v1) (.seq (.op (.copy t3 xI)) emitNat) skipS)
      (.seq (.op (.copy xT xQ)) (.op (.inc xI)))))))))

def coordPT : List (Fin VV) := [t3, t5, t6, t7, t8, t9, xT, xI, xQ, xR, vJ]

/-- The set bits below `y`, as words. -/
def maskWords (ml : List Bool) (y : ℕ) : List Bool := ((List.range y).filter fun y' => ml.getD y' false).flatMap natWord

theorem maskWords_succ (ml : List Bool) (y : ℕ) :
    maskWords ml (y + 1) = maskWords ml y ++ (if ml.getD y false then natWord y else []) := by
  unfold maskWords
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  congr 1
  cases h : ml.getD y false
  · simp only [List.filter_cons, List.filter_nil, h, Bool.false_eq_true, if_false, List.flatMap_nil]
  · simp only [List.filter_cons, List.filter_nil, h, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem coordPrint_spec (a : DS VV) (hc : Cst a) (n k : ℕ) (ml : List Bool) (hml : ml.length = n)
    (hk : a.env pK = k) (hn : a.env vN = n) (hBM : a.env vBM = bitsValue ml) (hW : n + 4 ≤ C.Wd)
    (hkW : natBitLength k + 2 < 2 ^ C.Wd) :
    Hs C coordPrint a (40 * natBitLength k + 50 + n * (40 * n + 110) + 10) (fun b =>
      b.out = a.out ++ natWord k ++ maskWords ml n ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Fr a b coordPT) := by
  have hv2 := hc.two
  have hnW : n + 2 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength k + 40 + (n * (40 * n + 110) + 16) + 1)
    (hs_copy C t3 pK a (by decide)) (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  have b3 : (a.set t3 (a.env pK)).env t3 = k := by vsimp [hk]
  have bc : Cst (a.set t3 (a.env pK)) := Cst.of_fr hc (Fr.set a _ (show t3 ∈ [t3] by decide)) (by decide)
    (by vsimp [hc.pos])
  refine Hs.seq (t1 := 40 * natBitLength k + 40) (t2 := n * (40 * n + 110) + 16)
    (Hs.mono (emitNat_spec (C := C) _ bc (by omega) (by rw [b3]; exact hkW)) (by rw [b3]) (fun _ h => h))
    (fun d ⟨d1, d2, d3, d4, d5⟩ => ?_)
  rw [b3] at d1
  have dfr : Fr a d coordPT := Fr.trans (Fr.set a _ (by decide)) (Fr.weaken d5 (by decide))
  let I : ℕ → DS VV → Prop := fun y e => e.env xT = bitsValue (ml.drop y) ∧ e.env xI = y ∧
    e.out = a.out ++ natWord k ++ maskWords ml y ∧ e.cp = a.cp ∧ e.wq = a.wq ∧ Cst e ∧ Fr a e coordPT
  have hn' : ∀ e, Fr a e coordPT → e.env vN = n := fun e he => by rw [he vN (by decide), hn]
  have l := Hs.loopN (C := C) (c := .lt xI vN) (s := .seq (.op (.dm xT v2 xQ xR)) (.seq (.ite (.eq xR v1)
      (.seq (.op (.copy t3 xI)) emitNat) skipS) (.seq (.op (.copy xT xQ)) (.op (.inc xI))))) (show xI ≠ vN by decide)
    I n (40 * n + 100) ?_ ?_
  · refine Hs.mono (Hs.seq (hs_copy C xT vBM d (by decide)) (fun e he => Hs.seq (hs_zero C xI e)
      (fun f hf => l f ?_))) (by
        have := Nat.mul_le_mul_left n (show 40 * n + 100 + 2 ≤ 40 * n + 110 by omega); omega) ?_
    · subst he hf
      refine ⟨by vsimp [dfr vBM (by decide), hBM], by vsimp [], by simp [d1, maskWords], by simp [d2], by simp [d3],
        Cst.of_fr d4 (Fr.trans (Fr.set _ _ (show xT ∈ [xT, xI] by decide)) (Fr.set _ _ (by decide))) (by decide)
          (by vsimp [d4.pos]), Fr.trans dfr (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
    · rintro e ⟨_, _, e3, e4, e5, e6, e7⟩
      exact ⟨e3, e4, e5, e6, e7⟩
  · intro y hy e ⟨e1, e2, e3, e4, e5, e6, e7⟩
    refine ⟨by simp [Cnd.eval, e2, hn' e e7, hy], ?_⟩
    have ev2 : e.env v2 = 2 := e6.two
    have h22 : 2 * 2 ≤ 2 ^ C.Wd := by
      calc 2 * 2 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * n + 98) (hs_dm C xT v2 xQ xR e (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [ev2]; norm_num) (by rw [ev2]; exact h22)) (fun f hf => ?_)) (by omega)
      (fun _ h => h)
    subst hf
    set f := (e.set xQ (e.env xT / e.env v2)).set xR (e.env xT % e.env v2) with hfd
    have hsplit := bitsValue_drop_succ ml y
    have hb1 : (ml.getD y false).toNat ≤ 1 := by cases ml.getD y false <;> simp
    have fR : f.env xR = (ml.getD y false).toNat := by
      have : f.env xR = bitsValue (ml.drop y) % 2 := by vsimp [hfd, e1, ev2]
      rw [this, hsplit]; omega
    have fQ : f.env xQ = bitsValue (ml.drop (y + 1)) := by
      have : f.env xQ = bitsValue (ml.drop y) / 2 := by vsimp [hfd, e1, ev2]
      rw [this, hsplit]; omega
    have ffr : Fr a f coordPT := Fr.trans e7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    have fc : Cst f := Cst.of_fr e6 (Fr.trans (Fr.set _ _ (show xQ ∈ [xQ, xR] by decide)) (Fr.set _ _ (by decide)))
      (by decide) (by vsimp [hfd, e6.pos])
    have fI : f.env xI = y := by vsimp [hfd, e2]
    refine Hs.mono (Hs.seq (t1 := 40 * n + 93) (t2 := 3) (R1 := fun g => g.env xQ = bitsValue (ml.drop (y + 1)) ∧ g.env xI = y ∧
      g.out = a.out ++ natWord k ++ maskWords ml (y + 1) ∧ g.cp = a.cp ∧ g.wq = a.wq ∧ Cst g ∧ Fr a g coordPT)
      (Hs.ite (c := .eq xR v1) (show xR ≠ v1 by decide) (fun he => ?_) (fun he => ?_)) (fun g ⟨g1, g2, g3, g4, g5, g6, g7⟩ => ?_))
      (by omega) (fun _ h => h)
    · have hb : ml.getD y false = true := by
        simp only [Cnd.eval, decide_eq_true_eq] at he; rw [fR, fc.one] at he
        cases h : ml.getD y false <;> simp_all
      refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength y + 40) (hs_copy C t3 xI f (by decide))
        (fun g hg => ?_)) (by
        have := Nat.mul_le_mul_left 40 (show natBitLength y ≤ n by have := natBitLength_le_succ y; omega); omega) (fun _ h => h)
      subst hg
      have gc : Cst (f.set t3 (f.env xI)) := Cst.of_fr fc (Fr.set f _ (show t3 ∈ [t3] by decide)) (by decide)
        (by vsimp [fc.pos])
      have hyW : natBitLength y + 2 < 2 ^ C.Wd := by have := natBitLength_le_succ y; omega
      refine Hs.mono (emitNat_spec (C := C) _ gc (by omega) (by vsimp [fI]; exact hyW)) (by vsimp [fI]) ?_
      rintro g ⟨g1, g2, g3, g4, g5⟩
      refine ⟨by rw [g5 xQ (by decide)]; vsimp [fQ], by rw [g5 xI (by decide)]; vsimp [fI], ?_, by simp [g2, hfd, e4],
        by simp [g3, hfd, e5], g4, Fr.trans ffr (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken g5 (by decide)))⟩
      rw [g1, maskWords_succ, hb]; vsimp [fI, hfd, e3, e2]
    · have hb : ml.getD y false = false := by
        simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [fR, fc.one] at he
        cases h : ml.getD y false <;> simp_all
      refine Hs.mono (skip_spec f) (by omega) ?_
      rintro g rfl
      refine ⟨by vsimp [fQ], by vsimp [fI], by rw [maskWords_succ, hb]; simp [hfd, e3], by simp [hfd, e4], by
        simp [hfd, e5], Cst.of_fr fc (Fr.set f _ (show vJ ∈ [vJ] by decide)) (by decide) (by vsimp [fc.pos]),
        Fr.trans ffr (Fr.set _ _ (by decide))⟩
    · refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C xT xQ g (by decide)) (fun h hh => ?_)
      subst hh
      refine Hs.mono (hs_inc C xI _ (by vsimp [g2]; omega)) le_rfl ?_
      rintro h rfl
      exact ⟨by vsimp [g1], by vsimp [g2], by simp [g3], g4, g5, Cst.of_fr g6 (Fr.trans (Fr.set _ _
        (show xT ∈ [xT, xI] by decide)) (Fr.set _ _ (by decide))) (by decide) (by vsimp [g6.pos]),
        Fr.trans g7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
  · intro e ⟨_, e2, _, _, _, _, e7⟩
    simp [Cnd.eval, e2, hn' e e7]

end NearCubicGates.Close.Dispatch
