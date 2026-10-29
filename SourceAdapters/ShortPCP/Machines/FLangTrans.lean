import SourceAdapters.ShortPCP.Machines.FLangPost

/-!
# Single-run time, machine layer 20: `Translate`

BCGT13 §12.3.1 (`Translate(I_ℓ, B_L, O_L, r, i)`, the query map of `V_{RS,=}`; proof of `thm:short-pcp-ours`: "Its recursion
roughly halves the dimension of the current affine subspace at each level and does poly(f) field operations per
level"). `Time.translateF` is a right fold of `Lvl.post` over the levels `step^[j] x0`, `j < D = depth`, started at
the last level's point `sel B_D (i − 1) + O_D` (`Time.translateF_iter`). The machine has no stack: it computes `D`
(`lvlP`: the level iteration `iterP` from the first level, counting in `48`), the base point (`baseP`), and then for
`t = 0, …, D − 1` recomputes the level `D − 1 − t` from the first level and applies its post-processing `postP`
(`transP_spec`). The first level is `(DOM, 0, coins)`: the basis words in `19`, `κ = f` (`23`), offset `0`, coin
position `0`. Every sub-verifier of `V0` runs on this domain (`Joins/SingleRun.lean`, `domBasis`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## Depth facts -/

section Depth

variable {F : Type} [Field F]

theorem depth_of_le : ∀ (n : ℕ) (x : Lvl F) (j : ℕ), j ≤ x.depth n → x.depth j = j
  | 0, x, j, h => by simp [Lvl.depth] at h; subst h; simp [Lvl.depth]
  | n + 1, x, j, h => by
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs] at h; subst h; simp [Lvl.depth]
    · rw [Lvl.depth, if_neg hs] at h
      cases j with
      | zero => simp [Lvl.depth]
      | succ j => rw [Lvl.depth, if_neg hs, depth_of_le n x.step j (by omega)]

theorem not_stop_of_lt : ∀ (n : ℕ) (x : Lvl F) (j : ℕ), j < x.depth n → ¬ (Lvl.step^[j] x).stop = true
  | 0, x, j, h => by simp [Lvl.depth] at h
  | n + 1, x, j, h => by
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs] at h
    · rw [Lvl.depth, if_neg hs] at h
      cases j with
      | zero => simpa using hs
      | succ j => rw [Function.iterate_succ_apply]; exact not_stop_of_lt n x.step j (by omega)

theorem length_iterate_le : ∀ (n : ℕ) (x : Lvl F) (j : ℕ), j ≤ x.depth n →
    (Lvl.step^[j] x).B.length ≤ x.B.length
  | 0, x, j, h => by simp [Lvl.depth] at h; subst h; simp
  | n + 1, x, j, h => by
    by_cases hs : x.stop = true
    · simp [Lvl.depth, hs] at h; subst h; simp
    · rw [Lvl.depth, if_neg hs] at h
      cases j with
      | zero => simp
      | succ j =>
        rw [Function.iterate_succ_apply]
        exact (length_iterate_le n x.step j (by omega)).trans (step_length_le x hs)

end Depth

theorem foldr_range'_step {α : Type} (g : ℕ → α → α) (b : α) (D t : ℕ) (ht : t < D) :
    (List.range' (D - (t + 1)) (t + 1)).foldr g b = g (D - 1 - t) ((List.range' (D - t) t).foldr g b) := by
  rw [List.range'_succ, List.foldr_cons, show D - (t + 1) + 1 = D - t by omega, show D - (t + 1) = D - 1 - t by omega]

/-! ## The program -/

/-- The first level `(DOM, 0, coins)`: basis in `19`, `κ = f` (`23`), offset `0`, coin position `0`. -/
def initL : S := .seq (.set 38 (.v 19)) (.seq (.set 39 (.v 23)) (.seq (.set 40 (.k 0)) (.set 41 (.k 0))))

/-- The level after `n` guarded steps from the first level (counter `48` from `0`). -/
def lvlP (n : E) : S := .seq initL (.seq (.set 48 (.k 0)) (iterP n))

/-- The variables `lvlP` writes. -/
def lvlW : List Var := [38, 39, 40, 41, 48] ++ iterW

/-- The base case at the last level: the point `sel B (i − 1) + O` with index `i` (`51`). -/
def baseP : S :=
  .seq (.set 20 (.v 38)) (.seq (.set 21 (.v 39)) (.seq (.set 22 (.sub (.v 51) (.k 1))) (.seq selP
  (.seq (.set 53 (.fadd (.v 24) (.v 40))) (.seq (.set 52 (.k 0)) (.set 54 (.v 51)))))))

/-- One unwinding pass `t` (loop variable `49`, depth `D` in `50`): level `D − 1 − t`, then its post-processing. -/
def unP : S := .seq (lvlP (.sub (.sub (.v 50) (.k 1)) (.v 49))) postP

/-- **`Translate`** of the query index in `51`, from the first level, into `52`–`54`. -/
def transP : S := .seq (lvlP (.v 39)) (.seq (.set 50 (.v 48)) (.seq baseP (.loop 49 (.v 50) unP)))

/-- The variables `transP` writes. -/
def transW : List Var := [49, 50, 52, 53, 54] ++ lvlW ++ postW

/-- The first level. -/
noncomputable def lvl0 {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (l0 : List ℕ) (u : List Bool) : Lvl F :=
  ⟨l0.map (ev φ), 0, u⟩

/-- **The level after `m` guarded steps** (`m = min n N`). -/
theorem lvlP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (l0 : List ℕ) (n : E) (m : ℕ)
    (hm : min (evalE G (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0) n) G.N = m)
    (h19 : s.env 19 = packW s.fl l0) (hl0 : l0.length = s.fl) (hl0w : ∀ a ∈ l0, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length)
    (hok : fieldOk G s.fl s.fp = true) (hK : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K) (hN : s.fl + 1 ≤ G.N)
    (hmf : m ≤ s.fl) :
    let t := evalS G (lvlP n) s
    LRep φ s.fl u t (Lvl.step^[(lvl0 φ l0 u).depth m] (lvl0 φ l0 u)) ∧ t.env 48 = (lvl0 φ l0 u).depth m ∧
      Wr lvlW s t ∧ t.env 41 ≤ m * (s.fl + 2) := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have hs1 : evalS G (.set 48 (.k 0)) (evalS G initL s) =
      ((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0 := by
    simp (config := { decide := true }) only [initL, evalS_seq, evalS_set, evalE, FS.setv_env,
      Function.update_apply, if_false, hc0]
  have hx0 : LRep φ s.fl u ((((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0))
      (lvl0 φ l0 u) := by
    refine ⟨l0, ?_, ?_, hl0w, rfl, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) [Function.update_apply, h19, h23, hl0, lvl0]
  have e1 : s.fl * s.fl ≤ (s.fl + 1) * (8 * s.fl + 16) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (m + 1) * (s.fl + 2) ≤ (s.fl + 1) * (s.fl + 2) := Nat.mul_le_mul_right _ (by omega)
  have e3 : (s.fl + 1) * (s.fl + 2) ≤ (s.fl + 1) * (8 * s.fl + 16) := Nat.mul_le_mul_left _ (by omega)
  have hit := iterP_spec G ((((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0)) φ u
    (lvl0 φ l0 u) n m hm hx0
    (by simp (config := { decide := true }) [Function.update_apply, h23])
    (by simp (config := { decide := true }) [Function.update_apply, h42])
    (by simp (config := { decide := true }) [Function.update_apply, h43]) hok
    (by simp only [lvl0, List.length_map, hl0, FS.setv_fl]; omega) (by simp only [lvl0, List.length_map, hl0]; omega)
    (by simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true, lvl0,
          List.length_map, hl0]; omega)
    (by simp; omega)
  obtain ⟨a, b, c, d⟩ := hit
  have ht : t = evalS G (iterP n) ((((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0)) := by
    show evalS G (lvlP n) s = _
    rw [lvlP, evalS_seq, evalS_seq, hs1]
  rw [ht]
  refine ⟨a, by rw [b]; simp, ?_, le_trans d (le_of_eq (by simp [lvl0, hl0]))⟩
  exact (((((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
    (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans (c.mono (by decide))

/-- **The base point** `eltWithIndex B O i` at the level in `38`–`40`. -/
theorem baseP_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (x : Lvl F) (i : ℕ) (hx : LRep φ s.fl u s x) (h23 : s.env 23 = s.fl) (h51 : s.env 51 = i)
    (hi : i ≤ 2 ^ s.fl) (hok : fieldOk G s.fl s.fp = true) (hκ : x.B.length ≤ s.fl)
    (hK : s.fl * s.fl + 1 ≤ G.K) (hN : s.fl ≤ G.N) :
    let t := evalS G baseP s
    TRep φ s.fl t (.inp (eltWithIndex x.B x.O i) i) ∧ Wr [20, 21, 22, 24, 25, 52, 53, 54] s t := by
  intro t
  obtain ⟨l, h38, h39, hlw, hlm, h40, hO, hr⟩ := hx
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hlκ : l.length = x.B.length := by rw [← hlm, List.length_map]
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hs1 : evalS G (.set 22 (.sub (.v 51) (.k 1))) (evalS G (.set 21 (.v 39)) (evalS G (.set 20 (.v 38)) s)) =
      ((s.setv 20 (packW s.fl l)).setv 21 l.length).setv 22 (i - 1) := by
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false,
      h38, h39, h51, hc1]
  have hcap : l.length * s.fl ≤ G.cap := by
    have := cap_ge G; have := Nat.mul_le_mul_right s.fl (show l.length ≤ s.fl by omega); omega
  obtain ⟨h24, hsel, selW⟩ := selP_at G s (((s.setv 20 (packW s.fl l)).setv 21 l.length).setv 22 (i - 1)) φ rfl rfl
    l hlw (by simp) (by simp) (by simp (config := { decide := true }) [Function.update_apply, h23]) hok hcap
    (by omega)
  generalize ht3 : evalS G selP (((s.setv 20 (packW s.fl l)).setv 21 l.length).setv 22 (i - 1)) = t3 at h24 hsel selW
  have t3W : Wr [20, 21, 22, 24, 25] s t3 :=
    (((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (selW.mono (by decide))
  have f40 : t3.env 40 = s.env 40 := t3W.env 40 (by decide)
  have f51 : t3.env 51 = i := (t3W.env 51 (by decide)).trans h51
  have a53 : evalE G t3 (.fadd (.v 24) (.v 40)) = t3.env 24 ^^^ s.env 40 :=
    eE_fadd rfl f40 (by rw [t3W.fl]; exact h24) (by rw [t3W.fl]; exact h40)
  have hc0 : min 0 G.cap = 0 := min_cap (by omega)
  have ht : t = ((t3.setv 53 (t3.env 24 ^^^ s.env 40)).setv 52 0).setv 54 i := by
    show evalS G baseP s = _
    simp only [baseP, evalS_seq]
    rw [hs1, ht3, show evalS G (.set 53 (.fadd (.v 24) (.v 40))) t3 = t3.setv 53 (t3.env 24 ^^^ s.env 40) by
      rw [evalS_set, a53]]
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false, hc0,
      f51]
  rw [ht]
  refine ⟨⟨by simp (config := { decide := true }) [Function.update_apply], ?_, ?_, by simp, hi⟩, ?_⟩
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    exact Nat.xor_lt_two_pow h24 h40
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]
    rw [ev_xor, hO, hsel, eltWithIndex_eq, ← hlm]
    simp
  · exact ((t3W.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans
      ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _))

theorem cap_big (f K : ℕ) (G : Glob) (hf : 1 ≤ f) (hK : (f + 1) * (8 * f + 16) + 1 ≤ G.K) :
    2 ^ f + (f + 1) * 2 ^ (9 * f + 20) ≤ G.cap := by
  have e1 : (f + 1) * 24 ≤ (f + 1) * (8 * f + 16) := Nat.mul_le_mul_left _ (by omega)
  have h1 := pow_le_cap (G := G) (a := 10 * f + 22) (by omega)
  have h2 : f + 2 ≤ 2 ^ (f + 1) := by
    have := Nat.lt_two_pow_self (n := f + 1); have : 2 ≤ 2 ^ (f + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (f + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : (f + 2) * 2 ^ (9 * f + 20) ≤ 2 ^ (f + 1) * 2 ^ (9 * f + 20) := Nat.mul_le_mul_right _ h2
  have h4 : 2 ^ (f + 1) * 2 ^ (9 * f + 20) = 2 ^ (10 * f + 21) := by rw [← pow_add]; ring_nf
  have h5 : 2 ^ (10 * f + 22) = 2 * 2 ^ (10 * f + 21) := by rw [pow_succ]; ring
  have h6 : 2 ^ f ≤ 2 ^ (9 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : (f + 2) * 2 ^ (9 * f + 20) = (f + 1) * 2 ^ (9 * f + 20) + 2 ^ (9 * f + 20) := by ring
  have h8 : 1 ≤ 2 ^ (10 * f + 21) := Nat.one_le_two_pow
  omega

/-- **`Translate`** (BCGT13 §12.3.1, `Time.translateF`; proof of `thm:short-pcp-ours`) of the query index `i` (`51`) from the first
level `(DOM, 0, coins)`: the result in `52`–`54`. -/
theorem transP_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ) (i : ℕ)
    (h19 : s.env 19 = packW s.fl l0) (hl0 : l0.length = s.fl) (hl0w : ∀ a ∈ l0, a < 2 ^ s.fl)
    (h23 : s.env 23 = s.fl) (h42 : s.env 42 = bitsValue u) (h43 : s.env 43 = u.length) (h51 : s.env 51 = i)
    (hi : i ≤ 2 ^ s.fl) (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp))
    (htb : TblRep s s.fl) (hK : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K) (hN : s.fl + 1 ≤ G.N) :
    let t := evalS G transP s
    TRep φ s.fl t (translateF s.fl (l0.map (ev φ)) 0 u i) ∧ Wr transW s t ∧
      t.env 54 ≤ 2 ^ s.fl + s.fl * 2 ^ (9 * s.fl + 20) := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hcb := cap_big s.fl s.fl G hf1 hK
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have e1 : s.fl * s.fl ≤ (s.fl + 1) * (8 * s.fl + 16) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : (s.fl + 1) * (s.fl + 2) ≤ (s.fl + 1) * (8 * s.fl + 16) := Nat.mul_le_mul_left _ (by omega)
  have hm0 : min (evalE G (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0) (.v 39))
      G.N = s.fl := by
    simp (config := { decide := true }) [evalE, Function.update_apply, h23]; omega
  obtain ⟨D, hD⟩ : ∃ D, (lvl0 φ l0 u).depth s.fl = D := ⟨_, rfl⟩
  have hDf : D ≤ s.fl := hD ▸ depth_le _ _
  obtain ⟨a1, a48, aW, -⟩ := lvlP_spec G s φ u l0 (.v 39) s.fl hm0 h19 hl0 hl0w h23 h42 h43 hok hK hN le_rfl
  rw [hD] at a1 a48
  have ht : t = evalS G (.loop 49 (.v 50) unP) (evalS G baseP ((evalS G (lvlP (.v 39)) s).setv 50 D)) := by
    show evalS G transP s = _
    simp only [transP, evalS_seq, evalS_set]
    rw [show evalE G (evalS G (lvlP (.v 39)) s) (.v 48) = D from a48]
  rw [ht]
  generalize hs1 : evalS G (lvlP (.v 39)) s = s1 at a1 a48 aW ⊢
  obtain ⟨e1', o1, l1, p1, i1, b1⟩ := s1
  obtain rfl : p1 = s.fp := aW.fp
  obtain rfl : l1 = s.fl := aW.fl
  have hlenD : (Lvl.step^[D] (lvl0 φ l0 u)).B.length ≤ s.fl := by
    have := length_iterate_le s.fl (lvl0 φ l0 u) D (by rw [hD]); simpa [lvl0, hl0] using this
  obtain ⟨bR, bW⟩ := baseP_spec G (FS.setv ⟨e1', o1, s.fl, s.fp, i1, b1⟩ 50 D) φ u _ i (a1.setv 50 (by decide) D)
    (by simp; exact (aW.env 23 (by decide)).trans h23) (by simp; exact (aW.env 51 (by decide)).trans h51) hi hok hlenD
    (by show s.fl * s.fl + 1 ≤ G.K; omega) (by show s.fl ≤ G.N; omega)
  generalize hs3 : evalS G baseP (FS.setv ⟨e1', o1, s.fl, s.fp, i1, b1⟩ 50 D) = s3 at bR bW ⊢
  have s3W : Wr transW s s3 :=
    ((aW.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (bW.mono (by decide))
  have s350 : s3.env 50 = D := by rw [bW.env 50 (by decide)]; simp
  -- the loop
  let g : ℕ → TrOut F → TrOut F := fun j res => (Lvl.step^[j] (lvl0 φ l0 u)).post res
  let base : TrOut F := .inp (eltWithIndex (Lvl.step^[D] (lvl0 φ l0 u)).B (Lvl.step^[D] (lvl0 φ l0 u)).O i) i
  have hmin : min (evalE G s3 (.v 50)) G.N = D := by rw [eE_v, s350]; omega
  have hl := loop_inv G (i := 49) (n := .v 50) (body := unP) (s := s3)
    (fun j w => TRep φ s.fl w ((List.range' (D - j) j).foldr g base) ∧
      w.env 54 ≤ 2 ^ s.fl + j * 2 ^ (9 * s.fl + 20) ∧ Wr transW s w ∧ w.env 50 = D)
    ⟨by simpa [base] using bR, by have := bR.2.2.2.1; have := bR.2.2.2.2; omega, s3W, s350⟩ (by
      rw [hmin]
      rintro j hj w ⟨wR, w54, wW, w50⟩
      obtain ⟨we, wo, wl, wp, wi, wb⟩ := w
      obtain rfl : wp = s.fp := wW.fp
      obtain rfl : wl = s.fl := wW.fl
      have q19 : we 19 = s.env 19 := wW.env 19 (by decide)
      have q23 : we 23 = s.env 23 := wW.env 23 (by decide)
      have q42 : we 42 = s.env 42 := wW.env 42 (by decide)
      have q43 : we 43 = s.env 43 := wW.env 43 (by decide)
      have w50' : we 50 = D := w50
      have hmj : min (evalE G (((((((FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j).setv 38
          ((FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j).env 19)).setv 39 ((FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j).env 23)).setv
          40 0).setv 41 0).setv 48 0)) (.sub (.sub (.v 50) (.k 1)) (.v 49))) G.N = D - 1 - j := by
        simp (config := { decide := true }) [evalE, Function.update_apply, w50', hc1]; omega
      obtain ⟨c1, c48, cW, c41⟩ := lvlP_spec G (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j) φ u l0 _ (D - 1 - j) hmj
        (by simp [q19, h19]) hl0 hl0w (by simp [q23, h23]) (by simp [q42, h42]) (by simp [q43, h43]) hok hK hN
        (by show D - 1 - j ≤ s.fl; omega)
      have c1' : LRep φ s.fl u (evalS G (lvlP (.sub (.sub (.v 50) (.k 1)) (.v 49)))
          (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j)) (Lvl.step^[(lvl0 φ l0 u).depth (D - 1 - j)] (lvl0 φ l0 u)) := c1
      have c41' : (evalS G (lvlP (.sub (.sub (.v 50) (.k 1)) (.v 49))) (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j)).env 41 ≤
          (D - 1 - j) * (s.fl + 2) := c41
      clear c1 c41
      rw [depth_of_le s.fl (lvl0 φ l0 u) (D - 1 - j) (by omega)] at c1'
      have hnst := not_stop_of_lt s.fl (lvl0 φ l0 u) (D - 1 - j) (by omega)
      have hlenj : (Lvl.step^[D - 1 - j] (lvl0 φ l0 u)).B.length ≤ s.fl := by
        have := length_iterate_le s.fl (lvl0 φ l0 u) (D - 1 - j) (by omega); simpa [lvl0, hl0] using this
      have hunp : evalS G unP (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j) =
          evalS G postP (evalS G (lvlP (.sub (.sub (.v 50) (.k 1)) (.v 49))) (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j)) :=
        rfl
      rw [hunp]
      generalize hs4 : evalS G (lvlP (.sub (.sub (.v 50) (.k 1)) (.v 49))) (FS.setv ⟨we, wo, s.fl, s.fp, wi, wb⟩ 49 j) = s4
        at c1' c48 cW c41'
      obtain ⟨e4, o4, l4, p4, i4, b4⟩ := s4
      obtain rfl : p4 = s.fp := cW.fp
      obtain rfl : l4 = s.fl := cW.fl
      have r52 : e4 52 = we 52 := cW.env 52 (by decide)
      have r53 : e4 53 = we 53 := cW.env 53 (by decide)
      have r54 : e4 54 = we 54 := cW.env 54 (by decide)
      have hsW : Wr transW s (⟨e4, o4, s.fl, s.fp, i4, b4⟩ : FS) :=
        (wW.trans (Wr.setv _ (by decide) _)).trans (cW.mono (by decide))
      have hm41 : (D - 1 - j) * (s.fl + 2) ≤ s.fl * (s.fl + 2) := Nat.mul_le_mul_right _ (by omega)
      have hm41' : s.fl * (s.fl + 2) + (s.fl + 2) = (s.fl + 1) * (s.fl + 2) := by ring
      obtain ⟨d1, d2, d3⟩ := postP_spec G ⟨e4, o4, s.fl, s.fp, i4, b4⟩ φ u _ _ c1'
        ((cW.env 23 (by decide)).trans (by simp [q23, h23]))
        ((cW.env 42 (by decide)).trans (by simp [q42, h42]))
        ((cW.env 43 (by decide)).trans (by simp [q43, h43])) hok hirr hnst hlenj
        (htb.of_wr hsW (by decide) (by decide))
        (wR.congr (by show e4 52 = _; rw [r52]) (by show e4 53 = _; rw [r53]) (by show e4 54 = _; rw [r54]))
        hK hN (by have c41'' : e4 41 ≤ (D - 1 - j) * (s.fl + 2) := c41'
                  show e4 41 + _ + 2 ≤ _; omega) (by
          show e4 54 + 2 ^ (9 * s.fl + 20) ≤ G.cap
          rw [r54]
          have w54' : we 54 ≤ 2 ^ s.fl + j * 2 ^ (9 * s.fl + 20) := w54
          calc we 54 + 2 ^ (9 * s.fl + 20) ≤ 2 ^ s.fl + j * 2 ^ (9 * s.fl + 20) + 2 ^ (9 * s.fl + 20) := by omega
            _ = 2 ^ s.fl + (j + 1) * 2 ^ (9 * s.fl + 20) := by ring
            _ ≤ 2 ^ s.fl + (s.fl + 1) * 2 ^ (9 * s.fl + 20) := by
              have := Nat.mul_le_mul_right (2 ^ (9 * s.fl + 20)) (show j + 1 ≤ s.fl + 1 by omega); omega
            _ ≤ G.cap := hcb)
      refine ⟨?_, ?_, hsW.trans (d2.mono (by decide)), ?_⟩
      · rw [foldr_range'_step g base D j (by omega)]; exact d1
      · have e5 : (j + 1) * 2 ^ (9 * s.fl + 20) = j * 2 ^ (9 * s.fl + 20) + 2 ^ (9 * s.fl + 20) := by ring
        have w54' : we 54 ≤ 2 ^ s.fl + j * 2 ^ (9 * s.fl + 20) := w54
        have := d3; simp only at this; rw [r54] at this; omega
      · rw [d2.env 50 (by decide), cW.env 50 (by decide)]; simpa using w50)
  rw [hmin] at hl
  obtain ⟨fR, f54, fW, -⟩ := hl
  refine ⟨?_, fW, f54.trans (by have := Nat.mul_le_mul_right (2 ^ (9 * s.fl + 20)) hDf; omega)⟩
  have e : translateF s.fl (l0.map (ev φ)) 0 u i = (List.range D).foldr g base := by
    have := translateF_iter s.fl (lvl0 φ l0 u) i; rw [hD] at this; exact this
  rw [e, List.range_eq_range']
  rw [Nat.sub_self] at fR
  exact fR

end NearCubicGates.Adapters.ShortPCP.Machines.FL
