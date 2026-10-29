import SourceAdapters.ShortPCP.Machines.FLangQOut
import SourceAdapters.ShortPCP.Machines.FLangDeq
import SourceAdapters.ShortPCP.Machines.FLangZf

/-!
# Single-run time, machine layer 26: the decisions of `V_RS` (base case, `<`, `=`)

BCGT13 Algorithm 13 (`V_RS` dispatches on the degree), Lemma 12.16 (`D_{RS,=}`), Algorithm 15 (`D_{RS,<}`: two runs
of `D_{RS,=}`, the second on the answers multiplied by `x^{d_{κ,η} − d}`), and the base case (`κ ≤ η`: the degree test
on all `2^κ` answers); proof of `thm:short-pcp-ours` ("A single run of V_RS or V_VRS takes poly(f) field operations"). Each machine
multiplies the verdict in `2` by its decision bit (`V0` "rejects whenever one of its steps rejects", proof of `thm:short-pcp-ours`); the
answers are the packed words in `11` (`ans i = ev (ansl.getD i 0)`), the degree is in `6`, the coins in `42`/`43`, the
first level is `(DOM, 0, u)` (`19`, `23`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## The domain `DOM` -/

section Dom

variable {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) {l0 : List ℕ} {f : ℕ}

theorem dom_elt (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ f)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 2 ^ f) :
    eltWithIndex (l0.map (ev φ)) 0 j = ev φ (j - 1) := by
  rw [eltWithIndex_eq, hdom, add_zero, Nat.mod_eq_of_lt (by omega)]

theorem dom_rand (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ f)) (r : List Bool) :
    getRandElt (l0.map (ev φ)) 0 r = ev φ (bitsValue r % 2 ^ f) := by
  rw [getRandElt_eq, hdom, add_zero]

end Dom

theorem degreeTestF_min {F : Type} [Field F] [DecidableEq F] (B : List F) (O : F) (d : ℕ) (ans : ℕ → F) :
    degreeTestF B O d ans = degreeTestF B O (min d (2 ^ B.length)) ans := by
  by_cases h : d ≤ 2 ^ B.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega)]; unfold degreeTestF; rw [if_pos (by omega), if_pos (by omega)]

/-! ## The first level and the verdict -/

/-- The first level `(DOM, 0, u)` in `38`–`41`, `48 := 0`. -/
def lvlI : S := .seq initL (.set 48 (.k 0))

/-- `2 := 2 · 7`. -/
def andR : S := .set 2 (.mul (.v 2) (.v 7))

/-- The variables the decision machines write. -/
def dW : List Var := [2, 5, 6, 7, 8, 9, 11, 12, 13, 14] ++ deqW ++ trW

theorem lvlI_eq (s : FS) :
    evalS G lvlI s = ((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0 := by
  have hc0 : min 0 G.cap = 0 := Nat.zero_min _
  simp (config := { decide := true }) only [lvlI, initL, evalS_seq, evalS_set, evalE, FS.setv_env,
    Function.update_apply, if_false, hc0]

variable {G}

theorem QC.lvl {s : FS} {l0 : List ℕ} {u : List Bool} (c : QC G s l0 u) :
    QC G (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0) l0 u :=
  ((((c.setv 38 _).setv 39 _).setv 40 _).setv 41 _).setv 48 _

theorem lvl_rep {F : Type} [Field F] {s : FS} (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) {l0 : List ℕ} {u : List Bool}
    (c : QC G s l0 u) :
    LRep φ s.fl u (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0)
      ⟨l0.map (ev φ), 0, u⟩ := by
  refine ⟨l0, ?_, ?_, c.hl0w, rfl, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) [Function.update_apply, c.h19, c.h23, c.hl0]

variable (G)

theorem andR_eval (t : FS) (b : Bool) (h7 : t.env 7 = if b then 1 else 0) (h2 : t.env 2 ≤ 1) (hc : 1 ≤ G.cap) :
    evalS G andR t = t.setv 2 (t.env 2 * if b then 1 else 0) := by
  rw [andR, evalS_set, eE_mul (eE_v 2) (h7 ▸ eE_v 7) (by split_ifs <;> omega)]

theorem mul_ite_le (a : ℕ) (b : Bool) (h : a ≤ 1) : a * (if b then 1 else 0) ≤ 1 := by
  split_ifs <;> omega

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-! ## Base case and `D_{RS,=}` -/

/-- The base case: the degree test on all `2^f` answers (degree clamped at `2^f`, `degreeTestF_min`). -/
def baseD : S :=
  .seq lvlI (.seq (.ite (.lt (.v 6) nSE) (.set 12 (.v 6)) (.set 12 nSE)) (.seq dtP andR))

theorem baseD_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ) (d : ℕ)
    (c : QC G s l0 u) (hind : Indep (l0.map (ev φ))) (h6 : s.env 6 = d) (h11 : s.env 11 = packW s.fl ansl)
    (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1) (hf2 : s.fl ≤ 2) :
    let t := evalS G baseD s
    t.env 2 = s.env 2 * (if degreeTestF (l0.map (ev φ)) 0 d (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ Wr dW s t := by
  intro t
  have c1 := c.lvl
  have A1 : Atoms G (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0) s.fl :=
    c1.atoms
  set s1 := ((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0 with hs1
  have hK := c.K
  have hN := c.N
  have hf1 := (fl_bounds c.ok).1
  have hp4 : 2 ^ s.fl ≤ 4 := le_trans (Nat.pow_le_pow_right (by norm_num) hf2) (by norm_num)
  have hK16 : 16 + s.fl ≤ (s.fl + 1) * (8 * s.fl + 16) := by nlinarith
  set d' := min d (2 ^ s.fl) with hd'
  have hd12 : evalS G (.ite (.lt (.v 6) nSE) (.set 12 (.v 6)) (.set 12 nSE)) s1 = s1.setv 12 d' := by
    rw [evalS_ite, eE_lt (show evalE G s1 (.v 6) = d by simp [hs1, evalE, h6]) A1.n]
    by_cases h : d < 2 ^ s.fl
    · rw [if_pos h, if_neg one_ne_zero, evalS_set, show evalE G s1 (.v 6) = d by simp [hs1, evalE, h6], hd',
        min_eq_left h.le]
    · rw [if_neg h, if_pos rfl, evalS_set, A1.n, hd', min_eq_right (by omega)]
  have hl0 := c.hl0
  have hdd : d' ≤ 2 ^ s.fl := min_le_right _ _
  obtain ⟨q7, qw⟩ := dtP_spec G (s1.setv 12 d') φ l0 ansl d' c.hl0w haw (by simp [hs1, c.h19])
    (by simp [hs1, c.h23, hl0]) (by simp [hs1]) (by simp [hs1, h11]) (by simp) (by simp [hs1, c.h23])
    c.ok c.irr hind (show 2 ^ l0.length * s.fl + s.fl + 1 ≤ G.K by
      rw [hl0]; have : 2 ^ s.fl * s.fl ≤ 4 * 2 := Nat.mul_le_mul hp4 hf2; omega)
    (show 2 ^ l0.length ≤ G.N by rw [hl0]; omega) (by omega)
  generalize ht1 : evalS G dtP (s1.setv 12 d') = t1 at q7 qw
  replace q7 : t1.env 7 = if degreeTestF (l0.map (ev φ)) 0 d' (fun i => ev φ (ansl.getD i 0)) then 1 else 0 := by
    rw [q7, show (s1.setv 12 d').env 40 = 0 by simp [hs1], ev_zero]; rfl
  have t2 : t1.env 2 = s.env 2 := by rw [qw.env 2 (by decide)]; simp [hs1]
  have ht : t = t1.setv 2 (t1.env 2 * if degreeTestF (l0.map (ev φ)) 0 d' (fun i => ev φ (ansl.getD i 0)) then 1
      else 0) := by
    show evalS G baseD s = _
    rw [baseD, evalS_seq, lvlI_eq, ← hs1, evalS_seq, hd12, evalS_seq, ht1, andR_eval G t1 _ q7 (t2 ▸ h2) A1.c1]
  have hdt : degreeTestF (l0.map (ev φ)) 0 d (fun i => ev φ (ansl.getD i 0)) =
      degreeTestF (l0.map (ev φ)) 0 d' (fun i => ev φ (ansl.getD i 0)) := by
    rw [degreeTestF_min, List.length_map, hl0]
  rw [ht, hdt]
  refine ⟨by simp [t2], by simp only [FS.setv_env, Function.update_self, t2]; exact mul_ite_le _ _ h2, ?_⟩
  have w1 : Wr dW s s1 := by
    rw [hs1]
    exact ((((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  exact ((w1.trans (Wr.setv _ (by decide) _)).trans (qw.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-- **`D_{RS,=}`** on the first level, answers in `11`. -/
def eqD : S := .seq lvlI (.seq deqP andR)

theorem eqD_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ)
    (c : QC G s l0 u) (hind : Indep (l0.map (ev φ))) (h11 : s.env 11 = packW s.fl ansl)
    (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1) :
    let t := evalS G eqD s
    t.env 2 = s.env 2 * (if dEqR (l0.map (ev φ)) 0 u (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ Wr (2 :: deqW) s t := by
  intro t
  have c1 := c.lvl
  have A1 : Atoms G (((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0) s.fl :=
    c1.atoms
  set s1 := ((((s.setv 38 (s.env 19)).setv 39 (s.env 23)).setv 40 0).setv 41 0).setv 48 0 with hs1
  have hK := c.K
  have hN := c.N
  have hl0 := c.hl0
  have e1 : s.fl * s.fl + 17 * s.fl + 1 ≤ G.K := by nlinarith
  have e2 : (s.fl + 1) * (s.fl + 2) ≤ G.K := by nlinarith
  obtain ⟨q7, qw⟩ := deqP_spec G s1 φ u ⟨l0.map (ev φ), 0, u⟩ ansl (lvl_rep φ c) hind haw (by simp [hs1, h11])
    (by simp [hs1, c.h23]) (by simp [hs1, c.h42]) (by simp [hs1, c.h43]) c.ok c.irr
    (show s.fl * (l0.map (ev φ)).length + 17 * s.fl + 1 ≤ G.K by rw [List.length_map, hl0]; exact e1)
    (show (l0.map (ev φ)).length + 16 ≤ G.N by rw [List.length_map, hl0]; exact hN)
    (show s1.env 41 + ((l0.map (ev φ)).length + 1) * ((l0.map (ev φ)).length + 2) ≤ G.K by
      rw [List.length_map, hl0]; simp [hs1]; exact e2)
    (show s1.env 48 + (l0.map (ev φ)).length ≤ G.K by rw [List.length_map, hl0]; simp [hs1]; omega)
  generalize ht1 : evalS G deqP s1 = t1 at q7 qw
  replace q7 : t1.env 7 = if dEqR (l0.map (ev φ)) 0 u (fun i => ev φ (ansl.getD i 0)) then 1 else 0 := q7
  have t2 : t1.env 2 = s.env 2 := by rw [qw.env 2 (by decide)]; simp [hs1]
  have ht : t = t1.setv 2 (t1.env 2 * if dEqR (l0.map (ev φ)) 0 u (fun i => ev φ (ansl.getD i 0)) then 1
      else 0) := by
    show evalS G eqD s = _
    rw [eqD, evalS_seq, lvlI_eq, ← hs1, evalS_seq, ht1, andR_eval G t1 _ q7 (t2 ▸ h2) A1.c1]
  rw [ht]
  refine ⟨by simp [t2], by simp only [FS.setv_env, Function.update_self, t2]; exact mul_ite_le _ _ h2, ?_⟩
  have w1 : Wr (2 :: deqW) s s1 := by
    rw [hs1]
    exact ((((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  exact (w1.trans (qw.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-! ## `D_{RS,<}` -/

/-- One entry of the second answer list of `D_{RS,<}` (index `12 + 1`, degree in `6`). -/
def lt2Body : S :=
  .seq (trQ (.add (.v 12) (.k 1)))
    (.ite (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1))))
      (.set 13 (.fmul (.fpow (.sub (.v 9) (.k 1)) (.sub dKEE (.v 6))) (getW 11 (.add qEE (.add (.v 12) (.k 1))))))
      (.set 13 (getW 11 (.add qEE (.add (.v 12) (.k 1))))))

/-- **`D_{RS,<}`** (Algorithm 15). -/
def dLtP : S :=
  .seq eqD (.seq (.set 7 qEE) (.seq (genP 7 12 13 14 23 lt2Body) (.seq (.set 11 (.shl (.v 14) (.v 23))) eqD)))

/-- The entry `j` of the second answer list (`J` the index `Translate` returns at `j + 1`). -/
noncomputable def ans2W (p f d qE : ℕ) (J : ℕ → ℕ) (ansl : List ℕ) (j : ℕ) : ℕ :=
  if 0 < J (j + 1) ∧ J (j + 1) ≤ 2 ^ f then
    mulW p f (powW p f (J (j + 1) - 1) (dKE f 2 - d)) (ansl.getD (qE + (j + 1)) 0)
  else ansl.getD (qE + (j + 1)) 0

theorem dLtP_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ) (d : ℕ)
    (c : QC G s l0 u) (hind : Indep (l0.map (ev φ))) (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ s.fl))
    (h6 : s.env 6 = d) (h11 : s.env 11 = packW s.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1) :
    let t := evalS G dLtP s
    t.env 2 = s.env 2 * (if (vLtF (l0.map (ev φ)) 0 d).D u (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ Wr dW s t := by
  intro t
  have A := c.atoms
  have hK := c.K
  have hN := c.N
  have hl0 := c.hl0
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hq := queryEq_le16 s.fl
  have hq1 : 1 ≤ queryEq T0 s.fl := by rw [queryEq_eq]; exact Nat.one_le_two_pow
  have hqf : queryEq T0 s.fl ≤ 2 ^ s.fl := by
    rw [queryEq_eq]; exact Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have hK1 : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K := by omega
  have hN1 : s.fl + 1 ≤ G.N := by omega
  have hB : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, hl0]
  have hc64 : 64 ≤ G.cap :=
    le_trans (le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 6 ≤ 8 * s.fl + 20 by omega)))
      A.big
  -- the first run of `D_{RS,=}`
  obtain ⟨e2, e2b, ew⟩ := eqD_spec G s φ u l0 ansl c hind h11 haw h2
  generalize ht1 : evalS G eqD s = t1 at e2 e2b ew
  have c1 : QC G t1 l0 u := c.wr ew (by decide) ew.fp
  have t11 : t1.env 11 = packW s.fl ansl := by rw [ew.env 11 (by decide), h11]
  have t16 : t1.env 6 = d := by rw [ew.env 6 (by decide), h6]
  have tfl : t1.fl = s.fl := ew.fl
  have tfp : t1.fp = s.fp := ew.fp
  -- the second answer list
  set J : ℕ → ℕ := fun i => trIdx (translateF s.fl (l0.map (ev φ)) 0 u i) with hJ
  set g := ans2W s.fp s.fl d (queryEq T0 s.fl) J ansl with hg
  have hgw : ∀ j, g j < 2 ^ s.fl := by
    intro j; simp only [hg, ans2W]; split_ifs
    · exact mulW_lt _ _ _ _
    · rcases Nat.lt_or_ge (queryEq T0 s.fl + (j + 1)) ansl.length with h | h
      · exact haw _ (List.getD_eq_getElem _ _ h ▸ List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]; exact Nat.two_pow_pos _
  have c2 : QC G (t1.setv 7 (queryEq T0 s.fl)) l0 u := c1.setv 7 _
  obtain ⟨g14, gw⟩ := genP_spec G 7 12 13 14 23 lt2Body (13 :: trW) (t1.setv 7 (queryEq T0 s.fl))
    (queryEq T0 s.fl) s.fl g (by simp; omega) (by simp [c1.h23, tfl]) (by nlinarith) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t w hj12
      obtain ⟨env, out, fl, fp, ip, bad⟩ := t
      have wfp := w.fp; have wfl := w.fl
      simp only [FS.setv_fp, FS.setv_fl] at wfp wfl
      obtain rfl : fp = s.fp := wfp.trans tfp
      obtain rfl : fl = s.fl := wfl.trans tfl
      set t0 : FS := ⟨env, out, s.fl, s.fp, ip, bad⟩ with ht0
      have c3 : QC G t0 l0 u := c2.wr w (by decide) tfp.symm
      have A3 : Atoms G t0 s.fl := c3.atoms
      have e11 : t0.env 11 = packW s.fl ansl := by rw [w.env 11 (by decide)]; simpa using t11
      have e6 : t0.env 6 = d := by rw [w.env 6 (by decide)]; simpa using t16
      have ei : evalE G t0 (.add (.v 12) (.k 1)) = j + 1 :=
        eE_add (eE_v 12 |>.trans hj12) (eE_k A3.c1) (by have := A3.big; have := Nat.lt_two_pow_self (n := 8 * s.fl + 20); omega)
      obtain ⟨q1, q8, q9, qw⟩ := trQ_spec G t0 φ u l0 _ (j + 1) c3.h19 c3.hl0 c3.hl0w c3.h23 c3.h42 c3.h43 ei
        (show j + 1 ≤ 2 ^ s.fl by omega) c3.ok c3.irr c3.tb hK1 hN1
      generalize ht5 : evalS G (trQ (.add (.v 12) (.k 1))) t0 = t5 at q1 q8 q9 qw
      replace q1 : qEqF (l0.map (ev φ)) 0 u (j + 1) = some (t5.env 9) := q1
      have hJ5 : J (j + 1) = t5.env 9 := by
        rw [qEqF_eq_idx, hB] at q1; exact Option.some.inj q1
      have c5 : QC G t5 l0 u := c3.wr qw (by decide) qw.fp
      have A5 : Atoms G t5 s.fl := by have := c5.atoms; rwa [qw.fl] at this
      have f11 : t5.env 11 = packW s.fl ansl := by rw [qw.env 11 (by decide), e11]
      have f6 : t5.env 6 = d := by rw [qw.env 6 (by decide), e6]
      have f12 : t5.env 12 = j := by rw [qw.env 12 (by decide)]; exact hj12
      have hfl5 : t5.fl = s.fl := qw.fl
      have hfp5 : t5.fp = s.fp := qw.fp
      have hcap := A5.big
      have hkk : 2 ^ (8 * s.fl + 20) ≤ G.cap := hcap
      have hgw' : evalE G t5 (getW 11 (.add qEE (.add (.v 12) (.k 1)))) = ansl.getD (queryEq T0 s.fl + (j + 1)) 0 := by
        have h23' : t5.env 23 = s.fl := c5.h23.trans hfl5
        have hc8 : 8 * s.fl + 20 < 2 ^ (8 * s.fl + 20) := Nat.lt_two_pow_self
        refine getW_eval G t5 11 _ s.fl _ ansl haw f11 h23' (eE_add A5.q (eE_add (eE_v 12 |>.trans f12)
          (eE_k A5.c1) (by omega)) (by omega)) ?_ (by omega)
        have : (queryEq T0 s.fl + (j + 1)) * s.fl ≤ 32 * s.fl := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      have hcnd : evalE G t5 (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1)))) =
          if 0 < J (j + 1) ∧ J (j + 1) ≤ 2 ^ s.fl then 1 else 0 := by
        rw [hJ5, eE_mul (eE_lt (eE_k (by omega)) (eE_v 9)) (eE_lt (eE_v 9) (eE_add A5.n (eE_k A5.c1)
          (by have : 2 ^ s.fl < 2 ^ (8 * s.fl + 20) := Nat.pow_lt_pow_right (by norm_num) (by omega)
              omega))) (by split_ifs <;> omega)]
        by_cases a : 0 < t5.env 9 <;> by_cases b : t5.env 9 < 2 ^ s.fl + 1 <;> simp [a, b] <;> omega
      have hW5 : ∀ v, Wr (13 :: trW) t0 (t5.setv 13 v) := fun v => (qw.mono (by decide)).trans (Wr.setv _ (by decide) _)
      have hpre : evalS G lt2Body t0 = evalS G (.ite (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1))))
          (.set 13 (.fmul (.fpow (.sub (.v 9) (.k 1)) (.sub dKEE (.v 6))) (getW 11 (.add qEE (.add (.v 12) (.k 1))))))
          (.set 13 (getW 11 (.add qEE (.add (.v 12) (.k 1)))))) t5 := by rw [lt2Body, evalS_seq, ht5]
      rw [hpre, evalS_ite, hcnd]
      by_cases hc : 0 < J (j + 1) ∧ J (j + 1) ≤ 2 ^ s.fl
      · rw [if_pos hc, if_neg one_ne_zero, evalS_set]
        have ha : ansl.getD (queryEq T0 s.fl + (j + 1)) 0 < 2 ^ s.fl := by
          rcases Nat.lt_or_ge (queryEq T0 s.fl + (j + 1)) ansl.length with h | h
          · exact haw _ (List.getD_eq_getElem _ _ h ▸ List.getElem_mem h)
          · rw [List.getD_eq_default _ _ h]; exact Nat.two_pow_pos _
        have hv : evalE G t5 (.fmul (.fpow (.sub (.v 9) (.k 1)) (.sub dKEE (.v 6)))
            (getW 11 (.add qEE (.add (.v 12) (.k 1))))) = g j := by
          have e1 : evalE G t5 (.sub (.v 9) (.k 1)) = J (j + 1) - 1 := eE_sub (eE_v 9 |>.trans hJ5.symm) (eE_k A5.c1)
          have e2 : evalE G t5 (.sub dKEE (.v 6)) = dKE s.fl 2 - d := eE_sub A5.k (eE_v 6 |>.trans f6)
          have e3 : evalE G t5 (.fpow (.sub (.v 9) (.k 1)) (.sub dKEE (.v 6))) =
              powW s.fp s.fl (J (j + 1) - 1) (dKE s.fl 2 - d) := by
            show powW t5.fp t5.fl (evalE G t5 _ % 2 ^ t5.fl) (evalE G t5 _) = _
            rw [e1, e2, hfl5, hfp5, Nat.mod_eq_of_lt (show J (j + 1) - 1 < 2 ^ s.fl by omega)]
          show mulW t5.fp t5.fl (evalE G t5 _ % 2 ^ t5.fl) (evalE G t5 _ % 2 ^ t5.fl) = _
          rw [e3, hgw', hfl5, hfp5, Nat.mod_eq_of_lt (powW_lt _ _ _ _), Nat.mod_eq_of_lt ha]
          simp only [hg, ans2W, if_pos hc]
        refine ⟨by simp [hv], hgw j, hW5 _⟩
      · rw [if_neg hc, if_pos rfl, evalS_set, hgw']
        refine ⟨by simp [hg, ans2W, if_neg hc], hgw j, hW5 _⟩)
  generalize ht3 : evalS G (genP 7 12 13 14 23 lt2Body) (t1.setv 7 (queryEq T0 s.fl)) = t3 at g14 gw
  have c3' : QC G t3 l0 u := c2.wr gw (by decide) gw.fp
  have h3fp : t3.fp = s.fp := gw.fp.trans tfp
  have h3fl : t3.fl = s.fl := gw.fl.trans tfl
  obtain ⟨env3, out3, fl3, fp3, ip3, bad3⟩ := t3
  obtain rfl : fp3 = s.fp := h3fp
  obtain rfl : fl3 = s.fl := h3fl
  set t3 : FS := ⟨env3, out3, s.fl, s.fp, ip3, bad3⟩ with ht3d
  have c3 : QC G t3 l0 u := c3'
  set L := (List.range (queryEq T0 s.fl)).map g with hL
  have hLw : ∀ a ∈ (0 :: L), a < 2 ^ s.fl := by
    intro a ha; simp only [List.mem_cons, hL, List.mem_map] at ha
    rcases ha with rfl | ⟨j, -, rfl⟩
    · exact Nat.two_pow_pos _
    · exact hgw j
  have hpk : packW s.fl (0 :: L) < 2 ^ (s.fl * (0 :: L).length) := packW_lt _ _ hLw
  have hLl : (0 :: L).length = queryEq T0 s.fl + 1 := by simp [hL]
  have hcapL : 2 ^ (s.fl * (0 :: L).length) ≤ G.cap + 1 := by
    rw [hLl]; refine pow_le_cap ?_
    have : s.fl * (queryEq T0 s.fl + 1) ≤ s.fl * 17 := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have e11 : evalE G t3 (.shl (.v 14) (.v 23)) = packW s.fl (0 :: L) := by
    have h0 : packW s.fl (0 :: L) = packW s.fl L * 2 ^ s.fl := by simp [packW]; ring
    show min (t3.env 14 * 2 ^ t3.env 23) G.cap = _
    rw [g14, c3.h23, ← h0]; exact min_eq_left (by omega)
  have hqE : evalE G t1 qEE = queryEq T0 s.fl := by have := c1.atoms.q; rwa [tfl] at this
  have c4 : QC G (t3.setv 11 (packW s.fl (0 :: L))) l0 u := c3.setv 11 _
  have t32 : t3.env 2 = t1.env 2 := by rw [gw.env 2 (by decide)]; simp
  obtain ⟨f2, f2b, fw⟩ := eqD_spec G (t3.setv 11 (packW s.fl (0 :: L))) φ u l0 (0 :: L) c4 hind
    (by simp [gw.fl, tfl]) (by simpa [gw.fl, tfl] using hLw) (by simp [t32]; exact e2b)
  have ht : t = evalS G eqD (t3.setv 11 (packW s.fl (0 :: L))) := by
    show evalS G dLtP s = _
    rw [dLtP, evalS_seq, ht1, evalS_seq, evalS_set, hqE, evalS_seq, ht3, evalS_seq, evalS_set, e11]
  rw [ht]
  generalize ht6 : evalS G eqD (t3.setv 11 (packW s.fl (0 :: L))) = t6 at f2 f2b fw
  have hag : AgreeOn (queryEq T0 (l0.map (ev φ)).length) (fun i => ev φ ((0 :: L).getD i 0))
      (fun i => match qEqF (l0.map (ev φ)) 0 u i with
        | some j' => if 0 < j' ∧ j' ≤ 2 ^ (l0.map (ev φ)).length then
            eltWithIndex (l0.map (ev φ)) 0 j' ^ (dKE (l0.map (ev φ)).length T0.η - d) *
              ev φ (ansl.getD (queryEq T0 (l0.map (ev φ)).length + i) 0)
          else ev φ (ansl.getD (queryEq T0 (l0.map (ev φ)).length + i) 0)
        | none => ev φ (ansl.getD (queryEq T0 (l0.map (ev φ)).length + i) 0)) := by
    intro i h1 h2
    rw [hB] at h2 ⊢
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hgk : (0 :: L).getD (k + 1) 0 = g k := by
      simp only [List.getD_cons_succ, hL]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    simp only [hgk, qEqF_eq_idx, hB, T0_η]
    show ev φ (ans2W s.fp s.fl d (queryEq T0 s.fl) J ansl k) = _
    unfold ans2W
    by_cases hc : 0 < J (k + 1) ∧ J (k + 1) ≤ 2 ^ s.fl
    · rw [if_pos hc, if_pos hc, ev_mulW φ _ _ _ hmod, ev_powW φ _ _ _ hmod, dom_elt φ hdom _ hc.1 hc.2]
    · rw [if_neg hc, if_neg hc]
  have hD : (vLtF (l0.map (ev φ)) 0 d).D u (fun i => ev φ (ansl.getD i 0)) =
      (dEqR (l0.map (ev φ)) 0 u (fun i => ev φ (ansl.getD i 0)) &&
        dEqR (l0.map (ev φ)) 0 u (fun i => ev φ ((0 :: L).getD i 0))) := by
    simp only [vLtF]
    congr 1
    exact (dEqR_congr _ _ _ hag).symm
  replace f2 : t6.env 2 = t1.env 2 * (if dEqR (l0.map (ev φ)) 0 u (fun i => ev φ ((0 :: L).getD i 0)) then 1
    else 0) := by rw [f2]; simp [t32]
  rw [hD, f2, e2]
  refine ⟨?_, by rw [← e2, ← f2]; exact f2b, ?_⟩
  · cases dEqR (l0.map (ev φ)) 0 u (fun i => ev φ (ansl.getD i 0)) <;>
      cases dEqR (l0.map (ev φ)) 0 u (fun i => ev φ ((0 :: L).getD i 0)) <;> simp
  · exact ((((ew.mono (by decide)).trans (Wr.setv _ (by decide) _)).trans (gw.mono (by decide))).trans
      (Wr.setv _ (by decide) _)).trans (fw.mono (by decide))

end NearCubicGates.Adapters.ShortPCP.Machines.FL
