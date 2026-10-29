import SourceAdapters.ShortPCP.Machines.FLangQGt

/-!
# Single-run time, machine layer 25: the query map of a sub-verifier run at its effective positions

BCGT13 Algorithm 13 (`V_RS`: base case, `<`, `=`, `>`) and Algorithm 12 (`V_VRS`: the queries of `V_RS`, shifted past
the first `2^f` entries of its proof, then the two queries of the `Z_H` test); proof of `thm:short-pcp-ours`.
`qRSP` dispatches `Q_RS` at the index in `5` for the degree in `6` (`qRSP_spec`); `qOutP v` computes the query at the
effective position `14 + 1` of `TimeBlocks.outV` (`qOutP_spec`); `kindP` classifies the answer source of a query
(implicit input, proof, none) and its element index in the oracle's tables (`kindP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-- **`Q_RS`** at the index in `5`, degree in `6`. -/
def qRSP : S :=
  .ite smallE (.seq (.set 8 (.k 1)) (.set 9 (.v 5)))
    (.ite (.lt (.v 6) dKEE) qLtP (.ite (.eq (.v 6) dKEE) (trQ (.v 5)) qGtP))

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

theorem qRS_le (f dv : ℕ) : qRS f dv + 2 ≤ (dv + 4) * 2 ^ (8 * f + 20) := by
  have h1 := mKED_le f dv
  have h2 := queryEq_le16 f
  have h3 : 16 ≤ 2 ^ (8 * f + 20) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : mKED f 2 dv * queryEq T0 f ≤ (dv + 1) * 16 := Nat.mul_le_mul h1 h2
  have h5 : (dv + 4) * 16 ≤ (dv + 4) * 2 ^ (8 * f + 20) := Nat.mul_le_mul_left _ h3
  have h6 : 2 ^ f + 2 ≤ 4 * 2 ^ (8 * f + 20) := by
    have := pf_le f; have : 1 ≤ 2 ^ (8 * f + 20) := Nat.one_le_two_pow; omega
  have h7 : 4 * 2 ^ (8 * f + 20) ≤ (dv + 4) * 2 ^ (8 * f + 20) := Nat.mul_le_mul_right _ (by omega)
  unfold qRS; split_ifs <;> omega

theorem jB_ge (f : ℕ) : 2 ^ (10 * f + 21) ≤ jB f := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **`Q_RS`** at a non-trivial degree, `1 ≤ i ≤ query`. -/
theorem qRSP_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ) (d i : ℕ)
    (c : QC G s l0 u) (h5 : s.env 5 = i) (h6 : s.env 6 = d) (hi1 : 1 ≤ i) (hiq : i ≤ qRS s.fl d)
    (hnt : trivB s.fl d = false) :
    let t := evalS G qRSP s
    (vRSF (l0.map (ev φ)) 0 d).Q u i = optOf t ∧ t.env 9 < jB s.fl ∧ Wr qW s t := by
  intro t
  have A := c.atoms
  have hjb := c.jb
  have hK2 : 2 * ((s.fl + 1) * (8 * s.fl + 16)) + 1 ≤ G.K := c.K
  have hN2 : s.fl + 16 ≤ G.N := c.N
  have hK1 : (s.fl + 1) * (8 * s.fl + 16) + 1 ≤ G.K := by omega
  have hN1 : s.fl + 1 ≤ G.N := by omega
  have hlen : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, c.hl0]
  have hk := dKE_lt s.fl
  have hq := queryEq_le16 s.fl
  have hqf : queryEq T0 s.fl ≤ 2 ^ s.fl := by
    rw [queryEq_eq]; exact Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have hl := lengthEq_lt s.fl
  have htr := trQ_le s.fl
  have hj := jB_ge s.fl
  have hl2 : 2 ^ (8 * s.fl + 16) ≤ 2 ^ (10 * s.fl + 21) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ s.fl ≤ 2 ^ (10 * s.fl + 21) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hjb2 : 4 * 2 ^ (10 * s.fl + 21) ≤ jB s.fl := by
    have : 2 ^ (10 * s.fl + 23) ≤ 2 ^ (10 * s.fl + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold jB; rw [show 10 * s.fl + 23 = 10 * s.fl + 21 + 2 by omega, pow_add] at this; omega
  have hs : evalE G s smallE = if s.fl < 3 then 1 else 0 :=
    eE_lt (eE_v 23 |>.trans c.h23) (eE_k (by have := A.big; have := Nat.lt_two_pow_self (n := 8 * s.fl + 20); omega))
  have h6' : evalE G s (.v 6) = d := h6
  by_cases h1 : s.fl ≤ 2
  · have ht : t = (s.setv 8 1).setv 9 i := by
      show evalS G qRSP s = _
      rw [qRSP, evalS_ite, hs, if_pos (show s.fl < 3 by omega), if_neg one_ne_zero, evalS_seq, evalS_set, evalS_set,
        eE_k A.c1]
      simp [evalE, h5]
    have hi2 : i ≤ 2 ^ s.fl := by unfold qRS at hiq; rw [if_pos h1] at hiq; exact hiq
    rw [ht]
    refine ⟨?_, by simp; omega, (Wr.setv (W := qW) s (by decide) _).trans (Wr.setv _ (by decide) _)⟩
    simp only [vRSF, hlen, T0_η, if_pos h1, optOf]; simp
  have hbr : ∀ X : S, evalS G (.ite smallE (.seq (.set 8 (.k 1)) (.set 9 (.v 5))) X) s = evalS G X s := by
    intro X; rw [evalS_ite, hs, if_neg (show ¬ s.fl < 3 by omega), if_pos rfl]
  by_cases h2 : d < dKE s.fl 2
  · have ht : t = evalS G qLtP s := by
      show evalS G qRSP s = _
      rw [qRSP, hbr, evalS_ite, eE_lt h6' A.k, if_pos h2, if_neg one_ne_zero]
    have hi2 : i ≤ 2 * queryEq T0 s.fl := by unfold qRS at hiq; rw [if_neg h1, if_pos h2] at hiq; exact hiq
    obtain ⟨q1, q8, q9, qw⟩ := qLtP_spec G s φ u l0 d i c.h19 c.hl0 c.hl0w c.h23 c.h42 c.h43 h5 hi1 hi2 c.ok c.irr c.tb
      hK1 hN1
    rw [ht]
    refine ⟨?_, by omega, qw.mono (by decide)⟩
    simp only [vRSF, hlen, T0_η, if_neg h1, if_pos h2, optOf, q8, one_ne_zero, if_false]
    exact q1
  by_cases h3 : d = dKE s.fl 2
  · have ht : t = evalS G (trQ (.v 5)) s := by
      show evalS G qRSP s = _
      rw [qRSP, hbr, evalS_ite, eE_lt h6' A.k, if_neg h2, if_pos rfl, evalS_ite, eE_eq h6' A.k, if_pos h3,
        if_neg one_ne_zero]
    have hi2 : i ≤ queryEq T0 s.fl := by unfold qRS at hiq; rw [if_neg h1, if_neg h2, if_pos h3] at hiq; exact hiq
    obtain ⟨q1, q8, q9, qw⟩ := trQ_spec G s φ u l0 (.v 5) i c.h19 c.hl0 c.hl0w c.h23 c.h42 c.h43 h5 (by omega) c.ok
      c.irr c.tb hK1 hN1
    rw [ht]
    refine ⟨?_, by omega, qw.mono (by decide)⟩
    simp only [vRSF, vEqF, hlen, T0_η, if_neg h1, if_neg h2, if_pos h3, optOf, q8, one_ne_zero, if_false]
    exact q1
  · have ht : t = evalS G qGtP s := by
      show evalS G qRSP s = _
      rw [qRSP, hbr, evalS_ite, eE_lt h6' A.k, if_neg h2, if_pos rfl, evalS_ite, eE_eq h6' A.k, if_neg h3, if_pos rfl]
    have hdn : d < 2 ^ s.fl := by
      simp only [trivB, decide_eq_false_iff_not, not_and, not_le] at hnt; exact hnt (by omega)
    obtain ⟨q1, q9, qw⟩ := qGtP_spec G s φ u l0 d i c h5 h6 hi1 hiq (by omega) (by omega) hdn
    rw [ht]
    refine ⟨?_, q9, qw⟩
    simp only [vRSF, hlen, T0_η, if_neg h1, if_neg h2, if_neg h3]
    exact q1

/-! ## The query at an effective position -/

/-- **The query of the outer verifier** at the effective position `14 + 1` (degree of the `V_RS` part in `6`). -/
def qOutP (v : Bool) : S :=
  .ite (.lt (.v 14) (qcIE (.v 6)))
    (.seq (.set 5 (.add (.v 14) (.k 1))) (.seq qRSP (if v then .set 9 (.add nSE (.v 9)) else .skip)))
    (.seq (.set 8 (.k 1)) (.set 9 (.add (.mul (.eq (.v 14) (.add (qcIE (.v 6)) (.k 1))) nSE) gamE)))

theorem qOutP_spec (v : Bool) (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ)
    (BH : List F) (OH : F) (d k : ℕ) (c : QC G s l0 u) (h14 : s.env 14 + 1 = k)
    (h6 : s.env 6 = innD v BH.length d) (hk : k ≤ qcO v s.fl (innD v BH.length d))
    (hbd : (innD v BH.length d + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap) :
    let t := evalS G (qOutP v) s
    (outV v (l0.map (ev φ)) 0 BH OH d).Q u (idxO s.fl (innD v BH.length d) k) = optOf t ∧
      t.env 9 < 2 * jB s.fl ∧ Wr qW s t := by
  intro t
  have A := c.atoms
  have hjb := c.jb
  have hlen : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, c.hl0]
  have heff := outV_Q_eff v (l0.map (ev φ)) 0 BH OH d u k (by omega) (by rw [hlen]; exact hk)
  rw [hlen] at heff
  generalize hdi : innD v BH.length d = di at h6 hk hbd heff ⊢
  have h6' : evalE G s (.v 6) = di := h6
  have hq := qcIE_eval c.h23 A h6' hbd
  have hj := jB_ge s.fl
  have hp2 : 2 ^ s.fl ≤ 2 ^ (10 * s.fl + 21) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [heff]
  have hc : evalE G s (.lt (.v 14) (qcIE (.v 6))) = if s.env 14 < qcI s.fl di then 1 else 0 := eE_lt rfl hq
  have hqb := qRS_le s.fl di
  have hqc : qcI s.fl di ≤ qRS s.fl di := by unfold qcI; split_ifs <;> omega
  have hbig := A.big
  have hγ : ∀ t' : FS, Atoms G t' s.fl → t'.env 42 = bitsValue u → evalE G t' gamE = 1 + bitsValue (u.take s.fl) := by
    intro t' At h42
    rw [bitsValue_take, gamE, eE_add (eE_k At.c1) (eE_md (show evalE G t' (.v 42) = bitsValue u from h42) At.n)]
    have : bitsValue u % 2 ^ s.fl < 2 ^ s.fl := Nat.mod_lt _ (by positivity)
    have := pf_le s.fl; omega
  have hγb : 1 + bitsValue (u.take s.fl) ≤ 2 ^ s.fl := by
    rw [bitsValue_take]; have : bitsValue u % 2 ^ s.fl < 2 ^ s.fl := Nat.mod_lt _ (by positivity); omega
  by_cases hkI : k ≤ qcI s.fl di
  · have hnt : trivB s.fl di = false := by
      by_contra h; simp only [Bool.not_eq_false] at h; simp only [qcI, h, if_true] at hkI; omega
    have hqI : qcI s.fl di = qRS s.fl di := by simp [qcI, hnt]
    have c1 := c.setv 5 k
    have e5 : evalE G s (.add (.v 14) (.k 1)) = k := (eE_add (eE_v 14) (eE_k A.c1) (by omega)).trans h14
    obtain ⟨q1, q9, qw⟩ := qRSP_spec G (s.setv 5 k) φ u l0 di k c1 (by simp) (by simp [h6]) (by omega) (by
      show k ≤ qRS s.fl di; omega) hnt
    generalize ht1 : evalS G qRSP (s.setv 5 k) = t1 at q1 q9 qw
    replace q1 : (vRSF (l0.map (ev φ)) 0 di).Q u k = optOf t1 := q1
    replace q9 : t1.env 9 < jB s.fl := q9
    have ht : t = evalS G (if v then .set 9 (.add nSE (.v 9)) else .skip) t1 := by
      show evalS G (qOutP v) s = _
      rw [qOutP, evalS_ite, hc, if_pos (show s.env 14 < qcI s.fl di by omega), if_neg one_ne_zero, evalS_seq,
        evalS_set, e5, evalS_seq, ht1]
    rw [if_pos hkI, q1, ht]
    have hW1 : Wr qW s t1 := (Wr.setv (W := qW) s (by decide) _).trans qw
    cases v with
    | false =>
      refine ⟨?_, by simp; omega, hW1⟩
      simp only [optOf, Bool.false_eq_true, if_false, evalS_skip]; split_ifs <;> simp
    | true =>
      have c2 : QC G t1 l0 u := c1.wr qw (by decide) qw.fp
      have A2 : Atoms G t1 s.fl := by have := c2.atoms; rwa [qw.fl] at this
      try simp only [↓reduceIte]
      rw [evalS_set, eE_add A2.n (eE_v 9) (by omega)]
      refine ⟨?_, by simp; omega, hW1.trans (Wr.setv _ (by decide) _)⟩
      simp only [optOf, if_true, FS.setv_env, Function.update_apply]
      split_ifs <;> simp_all
  · have hv : v = true := by
      cases v
      · simp only [qcO, Bool.false_eq_true, if_false] at hk; omega
      · rfl
    subst hv
    simp only [qcO, if_true] at hk
    have c1 := c.setv 8 1
    have A1 : Atoms G (s.setv 8 1) s.fl := c1.atoms
    have hq1 : evalE G (s.setv 8 1) (qcIE (.v 6)) = qcI s.fl di := qcIE_eval c1.h23 A1 (show evalE G (s.setv 8 1) (.v 6) = di by simp [evalE, h6]) hbd
    have hee : evalE G (s.setv 8 1) (.eq (.v 14) (.add (qcIE (.v 6)) (.k 1))) =
        if s.env 14 = qcI s.fl di + 1 then 1 else 0 :=
      eE_eq (show evalE G (s.setv 8 1) (.v 14) = s.env 14 by simp [evalE]) (eE_add hq1 (eE_k A.c1) (by omega))
    have hval : evalE G (s.setv 8 1) (.add (.mul (.eq (.v 14) (.add (qcIE (.v 6)) (.k 1))) nSE) gamE) =
        (if k = qcI s.fl di + 2 then 2 ^ s.fl else 0) + (1 + bitsValue (u.take s.fl)) := by
      rw [eE_add (eE_mul hee A1.n (by split_ifs <;> omega)) (hγ _ A1 (by simp [c.h42])) (by split_ifs <;> omega)]
      split_ifs <;> first | rfl | omega
    have ht : t = (s.setv 8 1).setv 9 ((if k = qcI s.fl di + 2 then 2 ^ s.fl else 0) + (1 + bitsValue (u.take s.fl))) := by
      show evalS G (qOutP true) s = _
      rw [qOutP, evalS_ite, hc, if_neg (show ¬ s.env 14 < qcI s.fl di by omega), if_pos rfl, evalS_seq, evalS_set,
        evalS_set, eE_k A.c1, hval]
    rw [if_neg hkI, ht]
    have hle : (if k = qcI s.fl di + 2 then 2 ^ s.fl else 0) ≤ 2 ^ s.fl := by split_ifs <;> omega
    have hlt : 2 ^ s.fl < 2 ^ (10 * s.fl + 21) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    refine ⟨by simp [optOf], by simp only [FS.setv_env, Function.update_self]; omega, ?_⟩
    exact (Wr.setv (W := qW) s (by decide) _).trans (Wr.setv _ (by decide) _)

/-! ## The source of an answer -/

/-- The source of the answer to a query (`answersN`): `1` the implicit input, `2` the proof, `0` none. -/
def kindOf (o : Option ℕ) (nS len : ℕ) : ℕ :=
  match o with
  | none => 0
  | some j => if 1 ≤ j ∧ j ≤ nS then 1 else if j - nS - 1 < len ∧ nS < j then 2 else 0

/-- The element of the oracle's tables the answer is read from (`0` for none): implicit-input entry `j` is
element `pB + j − 1` (the domain's element of word `j − 1`), proof entry `j − nS − 1` is element `πB + j − nS − 1`. -/
def elemOf (o : Option ℕ) (nS len pB πB : ℕ) : ℕ :=
  match o with
  | none => 0
  | some j => if 1 ≤ j ∧ j ≤ nS then pB + (j - 1) else if j - nS - 1 < len ∧ nS < j then πB + (j - nS - 1) else 0

/-- **The source and the element** of the query in `8`/`9` (`12 :=` kind, `13 :=` element). -/
def kindP (lenE pBE πBE : E) : S :=
  .ite (.mul (.lt (.k 0) (.v 8)) (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1)))))
    (.seq (.set 13 (.add pBE (.sub (.v 9) (.k 1)))) (.set 12 (.k 1)))
    (.ite (.mul (.lt (.k 0) (.v 8)) (.mul (.lt nSE (.v 9)) (.lt (.sub (.sub (.v 9) nSE) (.k 1)) lenE)))
      (.seq (.set 13 (.add πBE (.sub (.sub (.v 9) nSE) (.k 1)))) (.set 12 (.k 2)))
      (.seq (.set 13 (.k 0)) (.set 12 (.k 0))))

theorem kindP_spec (lenE pBE πBE : E) (s : FS) (f len pB πB : ℕ) (h23 : s.env 23 = f) (hf : f + 2 ≤ G.K)
    (hl : evalE G s lenE = len) (hp : evalE G s pBE = pB) (hπ : evalE G s πBE = πB)
    (h9 : s.env 9 + 2 ^ f ≤ G.cap) (hpb : pB + 2 ^ f ≤ G.cap) (hπb : πB + len ≤ G.cap)
    (hcf : 2 * 2 ^ f ≤ G.cap) :
    let t := evalS G (kindP lenE pBE πBE) s
    t.env 12 = kindOf (optOf s) (2 ^ f) len ∧ t.env 13 = elemOf (optOf s) (2 ^ f) len pB πB ∧
      Wr [12, 13] s t := by
  intro t
  have hc := cap_ge G
  have hn : evalE G s nSE = 2 ^ f := nSE_eval G h23 (by omega)
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hW : ∀ a b, Wr [12, 13] s ((s.setv 13 a).setv 12 b) := fun a b =>
    (Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)
  have hc1 : evalE G s (.mul (.lt (.k 0) (.v 8)) (.mul (.lt (.k 0) (.v 9)) (.lt (.v 9) (.add nSE (.k 1))))) =
      if s.env 8 ≠ 0 ∧ 1 ≤ s.env 9 ∧ s.env 9 ≤ 2 ^ f then 1 else 0 := by
    rw [eE_mul (eE_lt (eE_k (by omega)) (eE_v 8)) (eE_mul (eE_lt (eE_k (by omega)) (eE_v 9))
      (eE_lt (eE_v 9) (eE_add hn (eE_k (by omega)) (by omega))) (by split_ifs <;> omega)) (by split_ifs <;> omega)]
    by_cases a : 0 < s.env 8 <;> by_cases b : 0 < s.env 9 <;> by_cases c : s.env 9 < 2 ^ f + 1 <;>
      simp [a, b, c] <;> omega
  have hc2 : evalE G s (.mul (.lt (.k 0) (.v 8)) (.mul (.lt nSE (.v 9)) (.lt (.sub (.sub (.v 9) nSE) (.k 1)) lenE))) =
      if s.env 8 ≠ 0 ∧ s.env 9 - 2 ^ f - 1 < len ∧ 2 ^ f < s.env 9 then 1 else 0 := by
    rw [eE_mul (eE_lt (eE_k (by omega)) (eE_v 8)) (eE_mul (eE_lt hn (eE_v 9))
      (eE_lt (eE_sub (eE_sub (eE_v 9) hn) (eE_k (by omega))) hl) (by split_ifs <;> omega)) (by split_ifs <;> omega)]
    by_cases a : 0 < s.env 8 <;> by_cases b : 2 ^ f < s.env 9 <;> by_cases c : s.env 9 - 2 ^ f - 1 < len <;>
      simp [a, b, c] <;> omega
  by_cases g1 : s.env 8 ≠ 0 ∧ 1 ≤ s.env 9 ∧ s.env 9 ≤ 2 ^ f
  · have ht : t = (s.setv 13 (pB + (s.env 9 - 1))).setv 12 1 := by
      show evalS G (kindP lenE pBE πBE) s = _
      rw [kindP, evalS_ite, hc1, if_pos g1, if_neg one_ne_zero, evalS_seq, evalS_set, evalS_set,
        eE_add hp (eE_sub (eE_v 9) (eE_k (by omega))) (by omega), eE_k (by omega)]
    rw [ht]
    refine ⟨?_, ?_, hW _ _⟩ <;> simp [optOf, kindOf, elemOf, g1.1, g1.2]
  by_cases g2 : s.env 8 ≠ 0 ∧ s.env 9 - 2 ^ f - 1 < len ∧ 2 ^ f < s.env 9
  · have ht : t = (s.setv 13 (πB + (s.env 9 - 2 ^ f - 1))).setv 12 2 := by
      show evalS G (kindP lenE pBE πBE) s = _
      rw [kindP, evalS_ite, hc1, if_neg g1, if_pos rfl, evalS_ite, hc2, if_pos g2, if_neg one_ne_zero, evalS_seq,
        evalS_set, evalS_set, eE_add hπ (eE_sub (eE_sub (eE_v 9) hn) (eE_k (by omega))) (by omega),
        eE_k (by omega)]
    rw [ht]
    have g3 : ¬ (1 ≤ s.env 9 ∧ s.env 9 ≤ 2 ^ f) := fun h => g1 ⟨g2.1, h⟩
    refine ⟨?_, ?_, hW _ _⟩ <;> simp [optOf, kindOf, elemOf, g2.1, g3, g2.2]
  · have ht : t = (s.setv 13 0).setv 12 0 := by
      show evalS G (kindP lenE pBE πBE) s = _
      rw [kindP, evalS_ite, hc1, if_neg g1, if_pos rfl, evalS_ite, hc2, if_neg g2, if_pos rfl, evalS_seq,
        evalS_set, evalS_set, eE_k (by omega), eE_k (by omega)]
    rw [ht]
    by_cases g8 : s.env 8 = 0
    · refine ⟨?_, ?_, hW _ _⟩ <;> simp [optOf, kindOf, elemOf, g8]
    · have g3 : ¬ (1 ≤ s.env 9 ∧ s.env 9 ≤ 2 ^ f) := fun h => g1 ⟨g8, h⟩
      have g4 : ¬ (s.env 9 - 2 ^ f - 1 < len ∧ 2 ^ f < s.env 9) := fun h => g2 ⟨g8, h⟩
      refine ⟨?_, ?_, hW _ _⟩ <;> simp [optOf, kindOf, elemOf, g8, g3, g4]

end NearCubicGates.Adapters.ShortPCP.Machines.FL
