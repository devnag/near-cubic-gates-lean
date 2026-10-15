import Proof.Gates.Dispatch.WitnessC

/-!
# Fragment (W), part D: the coordinates

`coordsW`: `p.k` coordinates of `λ_n` bits each (little-endian). A coordinate `x < n` not yet seen sets bit `x` of the
mask `vBM`; a coordinate `≥ n` or a repeated one clears the flag `vWF`.
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

/-- The first `i` coordinates of the witness. -/
def cl (w : List Bool) (lam i : ℕ) : List ℕ := (readBlock w (List.replicate i lam)).1

/-- A valid coordinate list. -/
def goodC (n : ℕ) (xs : List ℕ) : Prop := (∀ x ∈ xs, x < n) ∧ xs.Nodup

instance (n : ℕ) (xs : List ℕ) : Decidable (goodC n xs) := by unfold goodC; infer_instance

theorem cl_succ (w : List Bool) (lam i : ℕ) :
    cl w lam (i + 1) = cl w lam i ++ [bitsValue ((w.drop (i * lam)).take lam)] := readBlock_rep_succ w lam i

theorem goodC_snoc (n : ℕ) (xs : List ℕ) (x : ℕ) : goodC n (xs ++ [x]) ↔ goodC n xs ∧ x < n ∧ x ∉ xs := by
  unfold goodC
  rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨fun y hy => h1 y (Or.inl hy), h3⟩, h1 x (Or.inr rfl), h2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun y hy => hy.elim (h1 y) (fun e => e ▸ h3), h4, h2⟩

/-! ## Bit `x` of the mask -/

def shiftW : St VV :=
  .seq (.op (.copy xT vBM)) (.seq (.op (.copy xP2 v1)) (.seq (.op (.zero xC))
    (.loop (.lt xC xX) (.seq (.op (.half xT)) (.seq (.op (.shl xP2)) (.op (.inc xC)))))))

def shiftT : List (Fin VV) := [xT, xP2, xC, vJ]

theorem shiftW_spec (a : DS VV) (hc : Cst a) (x : ℕ) (hx : a.env xX = x) (hW : x + 2 ≤ C.Wd) :
    Hs C shiftW a (7 * x + 8) (fun b => b.env xT = a.env vBM / 2 ^ x ∧ b.env xP2 = 2 ^ x ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b shiftT) := by
  let I : ℕ → DS VV → Prop := fun j b => b.env xT = a.env vBM / 2 ^ j ∧ b.env xP2 = 2 ^ j ∧ b.env xC = j ∧
    b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b shiftT
  have hx' : ∀ b, Fr a b shiftT → b.env xX = x := fun b hb => by rw [hb xX (by decide), hx]
  have l := Hs.loopN (C := C) (c := .lt xC xX) (s := .seq (.op (.half xT)) (.seq (.op (.shl xP2)) (.op (.inc xC))))
    (show xC ≠ xX by decide) I x 5 ?_ ?_
  · refine Hs.mono (Hs.seq (hs_copy C xT vBM a (by decide)) (fun b hb => Hs.seq (hs_copy C xP2 v1 b (by decide))
      (fun d hd => Hs.seq (hs_zero C xC d) (fun e he => l e ?_)))) (by omega) ?_
    · subst hb hd he
      refine ⟨by vsimp [], by vsimp [hc.one], by vsimp [], rfl, rfl, rfl, ?_⟩
      exact Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    · rintro b ⟨b1, b2, -, b4, b5, b6, b7⟩
      exact ⟨b1, b2, b4, b5, b6, Cst.of_fr hc b7 (by decide) (by rw [b7 vPOS (by decide), hc.pos, b4]), b7⟩
  · intro j hj b ⟨b1, b2, b3, b4, b5, b6, b7⟩
    refine ⟨by simp [Cnd.eval, b3, hx' b b7, hj], ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_half C xT b) (fun d hd => ?_)
    subst hd
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C xP2 _ (by
      vsimp [b2]; have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show j + 2 ≤ C.Wd by omega)
      rw [pow_succ, pow_succ] at h; have := Nat.one_le_two_pow (n := j); nlinarith)) (fun e he => ?_)
    subst he
    refine Hs.mono (hs_inc C xC _ (by vsimp [b3]; have := Nat.lt_two_pow_self (n := C.Wd); omega)) le_rfl ?_
    rintro f rfl
    refine ⟨by vsimp [b1, Nat.div_div_eq_div_mul, pow_succ], by vsimp [b2, pow_succ]; ring, by vsimp [b3], b4, b5, b6,
      ?_⟩
    exact Fr.trans b7 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  · intro b ⟨_, _, b3, _, _, _, b7⟩
    simp [Cnd.eval, b3, hx' b b7]

/-! ## One coordinate -/

def coordStep : St VV :=
  .seq (rdBits pLAM xX)
  (.ite (.lt xX vN)
    (.seq shiftW (.seq (.op (.dm xT v2 xQ xR)) (.ite (.eq xR v1) (.op (.zero vWF)) (.op (.add vBM xP2)))))
    (.op (.zero vWF)))

def coordT : List (Fin VV) := [xX, xP, xC, xB, vJ, xT, xP2, xQ, xR, vWF, vBM]

theorem coordStep_spec (a : DS VV) (hc : Cst a) (n lam i : ℕ) (ml : List Bool) (hml : ml.length = n)
    (hq : a.wq = min (i * lam) C.wit.length) (hlam : a.env pLAM = lam) (hn : a.env vN = n)
    (hBM : a.env vBM = bitsValue ml) (hWF : a.env vWF = bnat (goodC n (cl C.wit lam i)))
    (hgood : goodC n (cl C.wit lam i) → ml = maskOf n (cl C.wit lam i))
    (hW : lam + 2 ≤ C.Wd) (hnW : n + 2 ≤ C.Wd) :
    Hs C coordStep a (10 * lam + 7 * n + 40) (fun b => ∃ ml' : List Bool, ml'.length = n ∧
      b.env vBM = bitsValue ml' ∧ b.env vWF = bnat (goodC n (cl C.wit lam (i + 1))) ∧
      (goodC n (cl C.wit lam (i + 1)) → ml' = maskOf n (cl C.wit lam (i + 1))) ∧
      b.wq = min ((i + 1) * lam) C.wit.length ∧ b.cp = a.cp ∧ b.out = a.out ∧ Cst b ∧ Fr a b coordT) := by
  refine Hs.seq (t1 := 10 * lam + 10) (t2 := 7 * n + 29) (rdBits_spec pLAM xX (Or.inl ⟨rfl, rfl⟩) a hc (i * lam) lam hq
    hlam (by omega)) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_) |>.mono (by omega) (fun _ h => h)
  set x := bitsValue ((C.wit.drop (i * lam)).take lam) with hxd
  have hcl : cl C.wit lam (i + 1) = cl C.wit lam i ++ [x] := cl_succ C.wit lam i
  have hwq : b.wq = min ((i + 1) * lam) C.wit.length := by rw [b2]; congr 1; ring
  have bN : b.env vN = n := by rw [b6 vN (by decide), hn]
  have bBM : b.env vBM = bitsValue ml := by rw [b6 vBM (by decide), hBM]
  have bWF : b.env vWF = bnat (goodC n (cl C.wit lam i)) := by rw [b6 vWF (by decide), hWF]
  have hmlt : bitsValue ml < 2 ^ n := by rw [← hml]; exact bitsValue_lt ml
  refine Hs.ite (c := .lt xX vN) (show xX ≠ vN by decide) (fun he => ?_) (fun he => ?_)
  · have hxn : x < n := by simp only [Cnd.eval, decide_eq_true_eq] at he; rw [b1, bN] at he; exact he
    refine Hs.seq (t1 := 7 * x + 8) (t2 := 7 * n - 7 * x + 19) (shiftW_spec b b5 x b1 (by omega))
      (fun d ⟨d1, d2, d3, d4, d5, d6, d7⟩ => ?_) |>.mono (by omega) (fun _ h => h)
    have dv2 : d.env v2 = 2 := d6.two
    have dbit : d.env xT % 2 = (ml.getD x false).toNat := by
      rw [d1, bBM, bitsValue_div_mod]
    have h22 : 2 * 2 ≤ 2 ^ C.Wd := by
      calc 2 * 2 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 2) (hs_dm C xT v2 xQ xR d (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [dv2]; norm_num) (by rw [dv2]; exact h22)) (fun e he => ?_)) (by omega)
      (fun _ h => h)
    subst he
    have eR : ((d.set xQ (d.env xT / d.env v2)).set xR (d.env xT % d.env v2)).env xR = (ml.getD x false).toNat := by
      vsimp [dv2, dbit]
    have eFr : Fr a ((d.set xQ (d.env xT / d.env v2)).set xR (d.env xT % d.env v2)) coordT :=
      Fr.trans (Fr.weaken b6 (by decide)) (Fr.trans (Fr.weaken d7 (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
    have ec : Cst ((d.set xQ (d.env xT / d.env v2)).set xR (d.env xT % d.env v2)) :=
      Cst.of_fr hc eFr (by decide) (by vsimp [d6.pos])
    have e1 : ((d.set xQ (d.env xT / d.env v2)).set xR (d.env xT % d.env v2)).env v1 = 1 := ec.one
    refine Hs.ite (c := .eq xR v1) (show xR ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · -- a repeated coordinate
      have hbit : ml.getD x false = true := by
        simp only [Cnd.eval, decide_eq_true_eq] at he; rw [eR, e1] at he
        cases h : ml.getD x false <;> simp_all
      refine Hs.mono (hs_zero C vWF _) le_rfl ?_
      rintro f rfl
      have hng : ¬ goodC n (cl C.wit lam (i + 1)) := by
        rw [hcl, goodC_snoc]
        rintro ⟨hg, -, hnot⟩
        rw [hgood hg, maskOf_getD] at hbit
        simp at hbit; exact hnot hbit.2
      refine ⟨ml, hml, by vsimp [d7 vBM (by decide), bBM], by vsimp [bnat, hng], fun h => absurd h hng, by
        simp [d4, hwq], by simp [d3, b3], by simp [d5, b4], ?_, Fr.trans eFr (Fr.set _ _ (by decide))⟩
      exact Cst.of_fr ec (Fr.set _ _ (show vWF ∈ [vWF] by decide)) (by decide) (by vsimp [d6.pos])
    · -- a new coordinate
      have hbit : ml.getD x false = false := by
        simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [eR, e1] at he
        cases h : ml.getD x false <;> simp_all
      have hset := bitsValue_set_true ml x (by omega) hbit
      refine Hs.mono (hs_add C vBM xP2 _ (by decide) ?_) le_rfl ?_
      · vsimp [d7 vBM (by decide), bBM, d2]
        have := bitsValue_lt (ml.set x true); rw [List.length_set, hml] at this
        have h2 : 2 ^ n ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · rintro f rfl
        refine ⟨ml.set x true, by rw [List.length_set, hml], ?_, ?_, ?_, by simp [d4, hwq], by simp [d3, b3],
          by simp [d5, b4], ?_, Fr.trans eFr (Fr.set _ _ (by decide))⟩
        · vsimp [d7 vBM (by decide), bBM, d2, hset]
        · vsimp [d7 vWF (by decide), bWF]
          unfold bnat; congr 1
          refine decide_eq_decide.mpr ?_
          rw [hcl, goodC_snoc]
          constructor
          · intro hg; refine ⟨hg, hxn, fun hm => ?_⟩
            rw [hgood hg, maskOf_getD] at hbit; simp [hxn, hm] at hbit
          · exact fun h => h.1
        · intro hg
          rw [hcl] at hg ⊢
          rw [maskOf_snoc, ← hgood ((goodC_snoc n _ x).mp hg).1]
        · exact Cst.of_fr ec (Fr.set _ _ (show vBM ∈ [vBM] by decide)) (by decide) (by vsimp [d6.pos])
  · -- a coordinate `≥ n`
    have hxn : ¬ x < n := by simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [b1, bN] at he; exact he
    refine Hs.mono (hs_zero C vWF b) (by omega) ?_
    rintro f rfl
    have hng : ¬ goodC n (cl C.wit lam (i + 1)) := by rw [hcl, goodC_snoc]; exact fun h => hxn h.2.1
    refine ⟨ml, hml, by vsimp [bBM], by vsimp [bnat, hng], fun h => absurd h hng, by simp [hwq], by simp [b3],
      by simp [b4], ?_, Fr.trans (Fr.weaken b6 (by decide)) (Fr.set _ _ (by decide))⟩
    exact Cst.of_fr b5 (Fr.set _ _ (show vWF ∈ [vWF] by decide)) (by decide) (by vsimp [b5.pos])

/-! ## All coordinates -/

def coordsW : St VV := .seq (.op (.zero xI)) (.loop (.lt xI pK) (.seq coordStep (.op (.inc xI))))

def coordsT : List (Fin VV) := [xX, xP, xC, xB, vJ, xT, xP2, xQ, xR, vWF, vBM, xI]

theorem maskOf_nil (n : ℕ) : maskOf n [] = List.replicate n false := by
  apply List.ext_getElem (by simp [maskOf]); intro i h1 h2; simp [maskOf]

theorem bitsValue_replicate_false (n : ℕ) : bitsValue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bitsValue, ih]

theorem coordsW_spec (a : DS VV) (hc : Cst a) (n lam k : ℕ) (hq : a.wq = 0) (hlam : a.env pLAM = lam)
    (hn : a.env vN = n) (hk : a.env pK = k) (hBM : a.env vBM = 0) (hWF : a.env vWF = 1)
    (hW : lam + 2 ≤ C.Wd) (hnW : n + 2 ≤ C.Wd) (hkW : k + 1 < 2 ^ C.Wd) :
    Hs C coordsW a (k * (10 * lam + 7 * n + 45) + 4) (fun b => ∃ ml : List Bool, ml.length = n ∧
      b.env vBM = bitsValue ml ∧ b.env vWF = bnat (goodC n (cl C.wit lam k)) ∧
      (goodC n (cl C.wit lam k) → ml = maskOf n (cl C.wit lam k)) ∧
      b.wq = min (k * lam) C.wit.length ∧ b.cp = a.cp ∧ b.out = a.out ∧ Cst b ∧ Fr a b coordsT) := by
  let I : ℕ → DS VV → Prop := fun i b => (∃ ml : List Bool, ml.length = n ∧
      b.env vBM = bitsValue ml ∧ b.env vWF = bnat (goodC n (cl C.wit lam i)) ∧
      (goodC n (cl C.wit lam i) → ml = maskOf n (cl C.wit lam i))) ∧
      b.wq = min (i * lam) C.wit.length ∧ b.env xI = i ∧ b.cp = a.cp ∧ b.out = a.out ∧ Cst b ∧ Fr a b coordsT
  have l := Hs.loopN (C := C) (c := .lt xI pK) (s := .seq coordStep (.op (.inc xI))) (show xI ≠ pK by decide) I k
    (10 * lam + 7 * n + 42) ?_ ?_
  · refine Hs.mono (Hs.seq (hs_zero C xI a) (fun b hb => l b ?_)) (by
      have := Nat.mul_le_mul_left k (show 10 * lam + 7 * n + 42 + 2 ≤ 10 * lam + 7 * n + 45 by omega); omega) ?_
    · subst hb
      refine ⟨⟨List.replicate n false, by simp, by vsimp [hBM, bitsValue_replicate_false], ?_, ?_⟩, by
        simp [hq], by vsimp [], rfl, rfl, Cst.of_fr hc (Fr.set a _ (show xI ∈ [xI] by decide)) (by decide)
          (by vsimp [hc.pos]), Fr.set a _ (by decide)⟩
      · have : goodC n (cl C.wit lam 0) := by simp [cl, readBlock, goodC]
        vsimp [hWF, bnat, this]
      · intro _; simp [cl, readBlock, maskOf_nil]
    · rintro b ⟨⟨ml, h1, h2, h3, h4⟩, b2, -, b4, b5, b6, b7⟩
      exact ⟨ml, h1, h2, h3, h4, b2, b4, b5, b6, b7⟩
  · intro i hi b ⟨⟨ml, h1, h2, h3, h4⟩, b2, b3, b4, b5, b6, b7⟩
    have bk : b.env pK = k := by rw [b7 pK (by decide), hk]
    refine ⟨by simp [Cnd.eval, b3, bk, hi], ?_⟩
    refine Hs.seq (t1 := 10 * lam + 7 * n + 40) (t2 := 1) (coordStep_spec b b6 n lam i ml h1 b2 (by rw [b7 pLAM (by decide), hlam])
      (by rw [b7 vN (by decide), hn]) h2 h3 h4 hW hnW) (fun d ⟨ml', d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ => ?_)
    refine Hs.mono (hs_inc C xI d (by rw [d9 xI (by decide), b3]; omega)) le_rfl ?_
    rintro e rfl
    refine ⟨⟨ml', d1, by vsimp [d2], by vsimp [d3], d4⟩, by simp [d5], by vsimp [d9 xI (by decide), b3], by
      simp [d6, b4], by simp [d7, b5], Cst.of_fr d8 (Fr.set d _ (show xI ∈ [xI] by decide)) (by decide)
        (by vsimp [d8.pos]), Fr.trans b7 (Fr.trans (Fr.weaken d9 (by decide)) (Fr.set _ _ (by decide)))⟩
  · intro b ⟨_, _, b3, _, _, _, b7⟩
    simp [Cnd.eval, b3, b7 pK (by decide), hk]

end NearCubicGates.Close.Dispatch
