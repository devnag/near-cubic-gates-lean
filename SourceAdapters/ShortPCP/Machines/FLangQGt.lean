import SourceAdapters.ShortPCP.Machines.FLangParams

/-!
# Single-run time, machine layer 24: the query map of `V_{RS,>}`

BCGT13 Algorithm 14 (`Q_{RS,>}`: `m` runs of `Q_{RS,=}` on consecutive blocks, the run of `Q_{RS,<}` for the
remainder degree, and the `2^η + 1` queries of the combination test at the random point `γ`); proof of `thm:short-pcp-ours` ("A
single run of V_RS or V_VRS takes poly(f) field operations"), proof of `thm:short-pcp-ours` ("The queries of V0 are computed from the
random string alone"). `qGtP` computes `Q_{RS,>}` at the index in `5` for the degree in `6` (`qGtP_spec`), in the
non-trivial case `d < 2^f` (for `d ≥ 2^f` the verifier asks nothing, `TimeBlocks.vRSF_triv`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-- The query a state holds: `8 = 0` none, else `some 9`. -/
def optOf (t : FS) : Option ℕ := if t.env 8 = 0 then none else some (t.env 9)

/-- The context of a query or decision run on the first level `(DOM, 0, u)`. -/
structure QC (s : FS) (l0 : List ℕ) (u : List Bool) : Prop where
  h19 : s.env 19 = packW s.fl l0
  hl0 : l0.length = s.fl
  hl0w : ∀ a ∈ l0, a < 2 ^ s.fl
  h23 : s.env 23 = s.fl
  h42 : s.env 42 = bitsValue u
  h43 : s.env 43 = u.length
  ok : fieldOk G s.fl s.fp = true
  irr : Irreducible (GF.toPoly s.fp)
  tb : TblRep s s.fl
  K : 2 * ((s.fl + 1) * (8 * s.fl + 16)) + 1 ≤ G.K
  N : s.fl + 16 ≤ G.N

section QCL
variable {G}

theorem QC.setv {s : FS} {l0 : List ℕ} {u : List Bool} (c : QC G s l0 u) (i : Var) (v : ℕ)
    (hi : i ∉ ([17, 18, 19, 23, 42, 43] : List Var) := by decide) : QC G (s.setv i v) l0 u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
  obtain ⟨a, b, c', d, e, f⟩ := hi
  exact ⟨by simp [Function.update_of_ne (Ne.symm c'), c.h19], c.hl0, c.hl0w, by simp [Function.update_of_ne (Ne.symm d), c.h23],
    by simp [Function.update_of_ne (Ne.symm e), c.h42], by simp [Function.update_of_ne (Ne.symm f), c.h43], c.ok, c.irr,
    c.tb.congr (by simp [Function.update_of_ne (Ne.symm a)]) (by simp [Function.update_of_ne (Ne.symm b)]), c.K, c.N⟩

theorem QC.wr {s t : FS} {l0 : List ℕ} {u : List Bool} {W : List Var} (c : QC G s l0 u) (w : Wr W s t)
    (hW : ∀ x ∈ ([17, 18, 19, 23, 42, 43] : List Var), x ∉ W := by decide) (hfp : t.fp = s.fp) : QC G t l0 u := by
  have hfl := w.fl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w.env 19 (hW 19 (by simp)), hfl]; exact c.h19
  · rw [hfl]; exact c.hl0
  · rw [hfl]; exact c.hl0w
  · rw [w.env 23 (hW 23 (by simp)), hfl]; exact c.h23
  · rw [w.env 42 (hW 42 (by simp))]; exact c.h42
  · rw [w.env 43 (hW 43 (by simp))]; exact c.h43
  · rw [hfl, hfp]; exact c.ok
  · rw [hfp]; exact c.irr
  · rw [hfl]; exact c.tb.of_wr w (hW 17 (by simp)) (hW 18 (by simp))
  · rw [hfl]; exact c.K
  · rw [hfl]; exact c.N

theorem QC.atoms {s : FS} {l0 : List ℕ} {u : List Bool} (c : QC G s l0 u) : Atoms G s s.fl :=
  FL.atoms c.h23 c.tb (fl_bounds c.ok).1 c.K

/-- The bound of query indices. -/
def jB (f : ℕ) : ℕ := 2 ^ (10 * f + 30)

theorem QC.jb {s : FS} {l0 : List ℕ} {u : List Bool} (c : QC G s l0 u) : 2 * jB s.fl ≤ G.cap := by
  have hK := c.K
  have e : 10 * s.fl + 32 ≤ 2 * ((s.fl + 1) * (8 * s.fl + 16)) := by nlinarith
  have := pow_le_cap (G := G) (a := 10 * s.fl + 32) (by omega)
  rw [show 10 * s.fl + 32 = (10 * s.fl + 30) + 2 by ring, pow_add] at this
  unfold jB; omega

end QCL

theorem trQ_le (f : ℕ) : 2 ^ f + f * 2 ^ (9 * f + 20) ≤ 2 ^ (10 * f + 21) := by
  have h1 : f * 2 ^ (9 * f + 20) ≤ 2 ^ f * 2 ^ (9 * f + 20) := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le
  have h2 : 2 ^ f * 2 ^ (9 * f + 20) = 2 ^ (10 * f + 20) := by rw [← pow_add]; ring_nf
  have h3 : 2 ^ f ≤ 2 ^ (10 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ (10 * f + 21) = 2 * 2 ^ (10 * f + 20) := by rw [pow_succ]; ring
  omega

/-- `γ`'s index: `1 + (coins mod 2^f)`. -/
def gamE : E := .add (.k 1) (.md (.v 42) nSE)

theorem bitsValue_take (u : List Bool) (f : ℕ) : bitsValue (u.take f) = bitsValue u % 2 ^ f := by
  have := bitsValue_window u 0 f; simpa using this

/-! ## `Q_{RS,>}` -/

/-- **`Q_{RS,>}`** (Algorithm 14) at the index in `5`, degree in `6` (temporary `13`). -/
def qGtP : S :=
  .ite (.lt (.v 5) (.add (.mul (mE (.v 6)) qEE) (.k 1)))
    (.seq (.set 13 (.div (.sub (.v 5) (.k 1)) qEE))
      (.seq (trQ (.sub (.v 5) (.mul (.v 13) qEE)))
        (.set 9 (.add (.add nSE (.mul (.v 13) (.add nSE lEE))) (.v 9)))))
    (.ite (.mul (oneE (.v 6)) (.lt (.sub (.v 5) (.mul (mE (.v 6)) qEE)) (.add (.mul (.k 2) qEE) (.k 1))))
      (.seq (.set 13 (.add nSE (.mul (mE (.v 6)) (.add nSE lEE))))
        (.seq (.set 5 (.sub (.v 5) (.mul (mE (.v 6)) qEE))) (.seq qLtP (.set 9 (.add (.v 13) (.v 9))))))
      (.seq (.set 13 (.sub (.v 5) (.add (.mul (mE (.v 6)) qEE) (.mul (oneE (.v 6)) (.mul (.k 2) qEE)))))
        (.seq (.set 8 (.k 1))
          (.ite (.eq (.v 13) (.k 1)) (.set 9 gamE)
            (.ite (.mul (.lt (.k 1) (.v 13)) (.lt (.v 13) (.add (mE (.v 6)) (.k 2))))
              (.set 9 (.add (.add nSE (.mul (.sub (.v 13) (.k 2)) (.add nSE lEE))) gamE))
              (.ite (.mul (oneE (.v 6)) (.eq (.v 13) (.add (mE (.v 6)) (.k 2))))
                (.set 9 (.add (.add nSE (.mul (mE (.v 6)) (.add nSE lEE))) gamE))
                (.seq (.set 8 (.k 0)) (.set 9 (.k 0)))))))))

/-- The variables the query machines write. -/
def qW : List Var := [5, 13] ++ trW

theorem dKE_succ {f : ℕ} (hf : 2 ≤ f) : dKE f 2 + 1 = 2 ^ (f - 2) ∧ 2 ^ f = 4 * 2 ^ (f - 2) := by
  have h : 2 ^ f = 2 ^ (f - 2) * 2 ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hf]
  have h1 : 1 ≤ 2 ^ (f - 2) := Nat.one_le_two_pow
  unfold dKE
  rw [h, Nat.mul_div_cancel _ (by norm_num)]
  constructor <;> omega

theorem mKED_le4 {f d : ℕ} (hf : 2 ≤ f) (hd : d < 2 ^ f) : mKED f 2 d ≤ 4 := by
  obtain ⟨h1, h2⟩ := dKE_succ hf
  unfold mKED; rw [h1]
  exact Nat.div_le_of_le_mul (by omega)

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

omit [CharP F 2] in
theorem vLtF_query (B : List F) (O : F) (d : ℕ) : (vLtF B O d).query = 2 * queryEq T0 B.length := rfl

/-- **`Q_{RS,>}`** for `2 < f`, `d_{f,2} < d < 2^f`, `1 ≤ i ≤ query`. -/
theorem qGtP_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 : List ℕ) (d i : ℕ)
    (c : QC G s l0 u) (h5 : s.env 5 = i) (h6 : s.env 6 = d) (hi1 : 1 ≤ i) (hiq : i ≤ qRS s.fl d)
    (hf : 2 < s.fl) (hdk : dKE s.fl 2 < d) (hdn : d < 2 ^ s.fl) :
    let t := evalS G qGtP s
    (vGtF (l0.map (ev φ)) 0 d).Q u i = optOf t ∧ t.env 9 < jB s.fl ∧ Wr qW s t := by
  intro t
  have A := c.atoms
  have hjb := c.jb
  have h64 : 128 ≤ G.cap :=
    le_trans (le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 7 ≤ 8 * s.fl + 20 by omega)))
      A.big
  have hlen : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, c.hl0]
  set f := s.fl with hfdef
  have hbig : (d + 4) * 2 ^ (8 * f + 20) ≤ G.cap := by
    have e1 : (d + 4) * 2 ^ (8 * f + 20) ≤ (2 ^ f + 4) * 2 ^ (8 * f + 20) := Nat.mul_le_mul_right _ (by omega)
    have e2 : (2 ^ f + 4) * 2 ^ (8 * f + 20) ≤ 2 ^ (10 * f + 30) := by
      have : 2 ^ f + 4 ≤ 2 ^ (2 * f + 10) := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show f ≤ 2 * f + 9 by omega)
        have : 2 ^ (2 * f + 10) = 2 * 2 ^ (2 * f + 9) := by rw [pow_succ]; ring
        have : 4 ≤ 2 ^ (2 * f + 9) := le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num)
          (show 2 ≤ 2 * f + 9 by omega))
        omega
      calc (2 ^ f + 4) * 2 ^ (8 * f + 20) ≤ 2 ^ (2 * f + 10) * 2 ^ (8 * f + 20) := Nat.mul_le_mul_right _ this
        _ = 2 ^ (10 * f + 30) := by rw [← pow_add]; ring_nf
    unfold jB at hjb; omega
  have h6' : evalE G s (.v 6) = d := h6
  have hm := mE_eval A h6' hbig
  have ho := oneE_eval A h6' hbig
  have hm4 : mKED f 2 d ≤ 4 := mKED_le4 (by omega) hdn
  have hq := queryEq_le16 f
  have hq1 : 1 ≤ queryEq T0 f := by rw [queryEq_eq]; exact Nat.one_le_two_pow
  have hqf : queryEq T0 f ≤ 2 ^ f := by
    rw [queryEq_eq]; exact Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have hl := lengthEq_lt f
  have hnl := nl_le f
  have h18 : 2 ^ (8 * f + 18) ≤ 2 ^ (10 * f + 21) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h21 : 4 * 2 ^ (10 * f + 21) ≤ jB f := by
    have : 2 ^ (10 * f + 23) ≤ 2 ^ (10 * f + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold jB; rw [show 10 * f + 23 = 10 * f + 21 + 2 by omega, pow_add] at this; omega
  have hpq : 2 ^ f ≤ 2 ^ (10 * f + 21) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlq : lengthEq T0 f ≤ 2 ^ (10 * f + 21) := by omega
  have htr := trQ_le f
  have hmb : mKED f 2 d * (2 ^ f + lengthEq T0 f) ≤ 4 * 2 ^ (8 * f + 18) :=
    Nat.mul_le_mul hm4 (by omega)
  have h22 : 4 * 2 ^ (8 * f + 18) ≤ 2 ^ (10 * f + 21) := by
    have h4 : 4 ≤ 2 ^ (2 * f + 3) := le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have e : 2 ^ (10 * f + 21) = 2 ^ (8 * f + 18) * 2 ^ (2 * f + 3) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_comm]; exact Nat.mul_le_mul_left _ h4
  have hcap1 : 1 ≤ G.cap := A.c1
  -- the math side
  have hQ : (vGtF (l0.map (ev φ)) 0 d).Q u i =
      if 1 ≤ i ∧ i ≤ mKED f 2 d * queryEq T0 f then
        (qEqF (l0.map (ev φ)) 0 u (i - (i - 1) / queryEq T0 f * queryEq T0 f)).map
          fun j' => 2 ^ f + (i - 1) / queryEq T0 f * (2 ^ f + lengthEq T0 f) + j'
      else if gtOne f d = true ∧ 1 ≤ i - mKED f 2 d * queryEq T0 f ∧
          i - mKED f 2 d * queryEq T0 f ≤ (if gtOne f d = true then 2 * queryEq T0 f else 0) then
        ((vLtF (l0.map (ev φ)) 0 (d - mKED f 2 d * (dKE f 2 + 1))).Q u (i - mKED f 2 d * queryEq T0 f)).map
          fun j' => 2 ^ f + mKED f 2 d * (2 ^ f + lengthEq T0 f) + j'
      else
        if i - (mKED f 2 d * queryEq T0 f + (if gtOne f d = true then 2 * queryEq T0 f else 0)) = 1 then
          some (1 + bitsValue (u.take f))
        else if 1 < i - (mKED f 2 d * queryEq T0 f + (if gtOne f d = true then 2 * queryEq T0 f else 0)) ∧
            i - (mKED f 2 d * queryEq T0 f + (if gtOne f d = true then 2 * queryEq T0 f else 0)) ≤
              mKED f 2 d + 1 then
          some (2 ^ f + (i - (mKED f 2 d * queryEq T0 f + (if gtOne f d = true then 2 * queryEq T0 f else 0)) - 2) *
            (2 ^ f + lengthEq T0 f) + (1 + bitsValue (u.take f)))
        else if gtOne f d = true ∧
            i - (mKED f 2 d * queryEq T0 f + (if gtOne f d = true then 2 * queryEq T0 f else 0)) = mKED f 2 d + 2 then
          some (2 ^ f + mKED f 2 d * (2 ^ f + lengthEq T0 f) + (1 + bitsValue (u.take f)))
        else none := by
    simp only [vGtF, T0_η, vLtF_query, hlen, if_neg (show ¬ d ≥ 2 ^ f by omega), gtOne]
    rfl
  have hγ : evalE G s gamE = 1 + bitsValue (u.take f) := by
    rw [bitsValue_take, gamE, eE_add (eE_k (by omega)) (eE_md (eE_v 42 |>.trans c.h42) A.n)]
    have : bitsValue u % 2 ^ f < 2 ^ f := Nat.mod_lt _ (by positivity)
    have := pf_le f; omega
  have hK2 : 2 * ((f + 1) * (8 * f + 16)) + 1 ≤ G.K := c.K
  have hN2 : f + 16 ≤ G.N := c.N
  have hK1 : (f + 1) * (8 * f + 16) + 1 ≤ G.K := by omega
  have hN1 : f + 1 ≤ G.N := by omega
  have e2q : ∀ t : FS, Atoms G t f → evalE G t (.mul (.k 2) qEE) = 2 * queryEq T0 f :=
    fun t At => eE_mul (eE_k (by omega)) At.q (by omega)
  have hmq : ∀ t : FS, Atoms G t f → t.env 6 = d → evalE G t (.mul (mE (.v 6)) qEE) = mKED f 2 d * queryEq T0 f :=
    fun t At h6t => eE_mul (mE_eval At h6t hbig) At.q (by
      have : mKED f 2 d * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul hm4 hq
      omega)
  have hc1 : evalE G s (.lt (.v 5) (.add (.mul (mE (.v 6)) qEE) (.k 1))) =
      if i < mKED f 2 d * queryEq T0 f + 1 then 1 else 0 :=
    eE_lt (eE_v 5 |>.trans h5) (eE_add (hmq s A h6) (eE_k (by omega)) (by
      have : mKED f 2 d * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul hm4 hq
      omega))
  by_cases hb1 : i ≤ mKED f 2 d * queryEq T0 f
  · -- the `m` runs of `Q_{RS,=}`
    set zz := (i - 1) / queryEq T0 f with hzz
    have hz1 : zz * queryEq T0 f ≤ i - 1 := Nat.div_mul_le_self _ _
    have hz2 : i - 1 < zz * queryEq T0 f + queryEq T0 f := by
      have := Nat.lt_div_mul_add (a := i - 1) hq1; rw [← hzz] at this; omega
    have hzm : zz < mKED f 2 d := by
      by_contra hc
      have : mKED f 2 d * queryEq T0 f ≤ zz * queryEq T0 f := Nat.mul_le_mul_right _ (by omega)
      omega
    have ev13 : evalE G s (.div (.sub (.v 5) (.k 1)) qEE) = zz := eE_div (eE_sub (eE_v 5 |>.trans h5) (eE_k (by omega))) A.q
    have c1 := c.setv 13 zz
    have A1 : Atoms G (s.setv 13 zz) f := c1.atoms
    have he : evalE G (s.setv 13 zz) (.sub (.v 5) (.mul (.v 13) qEE)) = i - zz * queryEq T0 f :=
      eE_sub ((eE_v 5).trans (by simp [h5])) (eE_mul ((eE_v 13).trans (by simp)) A1.q (by
        have : zz * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul (by omega) hq
        omega))
    obtain ⟨q1, q8, q9, qw⟩ := trQ_spec G (s.setv 13 zz) φ u l0 _ (i - zz * queryEq T0 f) c1.h19 c1.hl0 c1.hl0w
      c1.h23 c1.h42 c1.h43 he (show i - zz * queryEq T0 f ≤ 2 ^ f by omega) c1.ok c1.irr c1.tb hK1 hN1
    generalize ht1 : evalS G (trQ (.sub (.v 5) (.mul (.v 13) qEE))) (s.setv 13 zz) = t1 at q1 q8 q9 qw
    have c2 := c1.wr qw (by decide) qw.fp
    have A2 := c2.atoms
    have t13 : t1.env 13 = zz := by rw [qw.env 13 (by decide)]; simp
    have hfl : t1.fl = f := qw.fl
    rw [hfl] at A2
    replace q9 : t1.env 9 ≤ 2 ^ f + f * 2 ^ (9 * f + 20) := q9
    replace q1 : qEqF (l0.map (ev φ)) 0 u (i - zz * queryEq T0 f) = some (t1.env 9) := q1
    have hzb : zz * (2 ^ f + lengthEq T0 f) ≤ 4 * 2 ^ (8 * f + 18) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hv : evalE G t1 (.add (.add nSE (.mul (.v 13) (.add nSE lEE))) (.v 9)) =
        2 ^ f + zz * (2 ^ f + lengthEq T0 f) + t1.env 9 :=
      eE_add (eE_add A2.n (eE_mul t13 (eE_add A2.n A2.l (by omega)) (by omega)) (by omega)) rfl (by omega)
    have ht : t = t1.setv 9 (2 ^ f + zz * (2 ^ f + lengthEq T0 f) + t1.env 9) := by
      show evalS G qGtP s = _
      rw [qGtP, evalS_ite, hc1, if_pos (show i < mKED f 2 d * queryEq T0 f + 1 by omega), if_neg one_ne_zero, evalS_seq, evalS_set, ev13, evalS_seq, ht1,
        evalS_set, hv]
    rw [ht, hQ, if_pos ⟨hi1, hb1⟩, q1]
    refine ⟨by simp [optOf, Function.update_apply, q8], by simp; omega, ?_⟩
    exact ((Wr.setv (W := qW) s (by decide) _).trans (qw.mono (by decide))).trans (Wr.setv _ (by decide) _)
  have hc2 : evalE G s (.mul (oneE (.v 6)) (.lt (.sub (.v 5) (.mul (mE (.v 6)) qEE))
      (.add (.mul (.k 2) qEE) (.k 1)))) =
      if gtOne f d = true ∧ i - mKED f 2 d * queryEq T0 f < 2 * queryEq T0 f + 1 then 1 else 0 := by
    rw [eE_mul ho (eE_lt (eE_sub (eE_v 5 |>.trans h5) (hmq s A h6)) (eE_add (e2q s A) (eE_k (by omega)) (by omega)))
      (by split_ifs <;> omega)]
    by_cases a : gtOne f d = true <;> by_cases b : i - mKED f 2 d * queryEq T0 f < 2 * queryEq T0 f + 1 <;>
      simp [a, b]
  by_cases hb2 : gtOne f d = true ∧ i - mKED f 2 d * queryEq T0 f ≤ 2 * queryEq T0 f
  · -- the run of `Q_{RS,<}`
    set B2 := 2 ^ f + mKED f 2 d * (2 ^ f + lengthEq T0 f) with hB2
    set i' := i - mKED f 2 d * queryEq T0 f with hi'
    have ev13 : evalE G s (.add nSE (.mul (mE (.v 6)) (.add nSE lEE))) = B2 :=
      eE_add A.n (eE_mul hm (eE_add A.n A.l (by omega)) (by omega)) (by omega)
    have c1 := c.setv 13 B2
    have A1 : Atoms G (s.setv 13 B2) f := c1.atoms
    have ev5 : evalE G (s.setv 13 B2) (.sub (.v 5) (.mul (mE (.v 6)) qEE)) = i' :=
      eE_sub ((eE_v 5).trans (by simp [h5])) (hmq _ A1 (by simp [h6]))
    have c2 := c1.setv 5 i'
    obtain ⟨q1, q8, q9, qw⟩ := qLtP_spec G ((s.setv 13 B2).setv 5 i') φ u l0 (d - mKED f 2 d * (dKE f 2 + 1)) i'
      c2.h19 c2.hl0 c2.hl0w c2.h23 c2.h42 c2.h43 (by simp) (by omega) (show i' ≤ 2 * queryEq T0 f by omega) c2.ok c2.irr c2.tb
      hK1 hN1
    generalize ht1 : evalS G qLtP ((s.setv 13 B2).setv 5 i') = t1 at q1 q8 q9 qw
    have t13 : t1.env 13 = B2 := by rw [qw.env 13 (by decide)]; simp
    replace q9 : t1.env 9 ≤ lengthEq T0 f + 2 ^ f + f * 2 ^ (9 * f + 20) := q9
    replace q1 : (vLtF (l0.map (ev φ)) 0 (d - mKED f 2 d * (dKE f 2 + 1))).Q u i' = some (t1.env 9) := q1
    have hv : evalE G t1 (.add (.v 13) (.v 9)) = B2 + t1.env 9 := eE_add t13 rfl (by omega)
    have ht : t = t1.setv 9 (B2 + t1.env 9) := by
      show evalS G qGtP s = _
      rw [qGtP, evalS_ite, hc1, if_neg (show ¬ i < mKED f 2 d * queryEq T0 f + 1 by omega), if_pos rfl, evalS_ite, hc2,
        if_pos (show gtOne f d = true ∧ i - mKED f 2 d * queryEq T0 f < 2 * queryEq T0 f + 1 from ⟨hb2.1, by omega⟩),
        if_neg one_ne_zero, evalS_seq, evalS_set, ev13, evalS_seq, evalS_set, ev5, evalS_seq, ht1, evalS_set, hv]
    rw [ht, hQ, if_neg (by omega), if_pos ⟨hb2.1, by omega, by rw [if_pos hb2.1]; exact hb2.2⟩, q1]
    refine ⟨by simp [optOf, Function.update_apply, q8], by simp; omega, ?_⟩
    exact (((Wr.setv (W := qW) s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (qw.mono (by decide))).trans
      (Wr.setv _ (by decide) _)
  · -- the combination test
    set qL := if gtOne f d = true then 2 * queryEq T0 f else 0 with hqL
    set i0 := i - (mKED f 2 d * queryEq T0 f + qL) with hi0
    have hqL' : evalE G s (.mul (oneE (.v 6)) (.mul (.k 2) qEE)) = qL := by
      rw [eE_mul ho (e2q s A) (by split_ifs <;> omega), hqL]; split_ifs <;> simp
    have ev13 : evalE G s (.sub (.v 5) (.add (.mul (mE (.v 6)) qEE) (.mul (oneE (.v 6)) (.mul (.k 2) qEE)))) = i0 :=
      eE_sub (eE_v 5 |>.trans h5) (eE_add (hmq s A h6) hqL' (by
        have : mKED f 2 d * queryEq T0 f ≤ 4 * 16 := Nat.mul_le_mul hm4 hq
        split_ifs at hqL <;> omega))
    have hi0q : i0 ≤ 5 := by
      have hr : qRS f d = mKED f 2 d * queryEq T0 f + qL + 1 + 4 := by
        rw [hqL]; unfold qRS; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      omega
    have c1 := (c.setv 13 i0).setv 8 1
    have A1 : Atoms G ((s.setv 13 i0).setv 8 1) f := c1.atoms
    have e13 : evalE G ((s.setv 13 i0).setv 8 1) (.v 13) = i0 := (eE_v 13).trans (by simp)
    have h6' : evalE G ((s.setv 13 i0).setv 8 1) (.v 6) = d := (eE_v 6).trans (by simp [h6])
    have hm1 := mE_eval A1 h6' hbig
    have ho1 := oneE_eval A1 h6' hbig
    have hg1 : evalE G ((s.setv 13 i0).setv 8 1) gamE = 1 + bitsValue (u.take f) := by
      rw [bitsValue_take, gamE, eE_add (eE_k (by omega)) (eE_md (show evalE G ((s.setv 13 i0).setv 8 1) (.v 42) =
        bitsValue u by simp [evalE, c.h42]) A1.n)]
      have : bitsValue u % 2 ^ f < 2 ^ f := Nat.mod_lt _ (by positivity)
      have := pf_le f; omega
    have hgb : 1 + bitsValue (u.take f) ≤ 2 ^ f := by
      rw [bitsValue_take]; have : bitsValue u % 2 ^ f < 2 ^ f := Nat.mod_lt _ (by positivity); omega
    have hpre : ∀ X : S, evalS G (.seq (.set 13 (.sub (.v 5) (.add (.mul (mE (.v 6)) qEE)
        (.mul (oneE (.v 6)) (.mul (.k 2) qEE))))) (.seq (.set 8 (.k 1)) X)) s =
        evalS G X ((s.setv 13 i0).setv 8 1) := by
      intro X; rw [evalS_seq, evalS_set, ev13, evalS_seq, evalS_set, eE_k (by omega)]
    have ht0 : t = evalS G (.ite (.eq (.v 13) (.k 1)) (.set 9 gamE)
            (.ite (.mul (.lt (.k 1) (.v 13)) (.lt (.v 13) (.add (mE (.v 6)) (.k 2))))
              (.set 9 (.add (.add nSE (.mul (.sub (.v 13) (.k 2)) (.add nSE lEE))) gamE))
              (.ite (.mul (oneE (.v 6)) (.eq (.v 13) (.add (mE (.v 6)) (.k 2))))
                (.set 9 (.add (.add nSE (.mul (mE (.v 6)) (.add nSE lEE))) gamE))
                (.seq (.set 8 (.k 0)) (.set 9 (.k 0)))))) ((s.setv 13 i0).setv 8 1) := by
      show evalS G qGtP s = _
      rw [qGtP, evalS_ite, hc1, if_neg (show ¬ i < mKED f 2 d * queryEq T0 f + 1 by omega), if_pos rfl, evalS_ite, hc2,
        if_neg (show ¬ (gtOne f d = true ∧ i - mKED f 2 d * queryEq T0 f < 2 * queryEq T0 f + 1) by
        intro h; exact hb2 ⟨h.1, by omega⟩), if_pos rfl, hpre]
    have hW : ∀ v, Wr qW s (((s.setv 13 i0).setv 8 1).setv 9 v) := fun v =>
      ((Wr.setv (W := qW) s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
    rw [hQ, if_neg (by omega), if_neg (by
      intro h; refine hb2 ⟨h.1, ?_⟩; have h2 := h.2.2; rw [hqL, if_pos h.1] at h2; exact h2), ht0]
    rw [evalS_ite, eE_eq e13 (eE_k (by omega))]
    by_cases g1 : i0 = 1
    · rw [if_pos g1, if_pos g1, if_neg one_ne_zero, evalS_set, hg1]
      exact ⟨by simp [optOf], by simp; omega, hW _⟩
    rw [if_neg g1, if_neg g1, if_pos rfl, evalS_ite, eE_mul (eE_lt (eE_k (by omega)) e13)
      (eE_lt e13 (eE_add hm1 (eE_k (by omega)) (by omega))) (by split_ifs <;> omega)]
    by_cases g2 : 1 < i0 ∧ i0 ≤ mKED f 2 d + 1
    · have hp : (if 1 < i0 then 1 else 0) * (if i0 < mKED f 2 d + 2 then 1 else 0) = 1 := by
        rw [if_pos g2.1, if_pos (by omega)]
      rw [if_pos g2, hp, if_neg one_ne_zero, evalS_set]
      have hb : (i0 - 2) * (2 ^ f + lengthEq T0 f) ≤ 4 * 2 ^ (8 * f + 18) := Nat.mul_le_mul (by omega) (by omega)
      rw [eE_add (eE_add A1.n (eE_mul (eE_sub e13 (eE_k (by omega))) (eE_add A1.n A1.l (by omega)) (by omega))
        (by omega)) hg1 (by omega)]
      exact ⟨by simp [optOf], by simp; omega, hW _⟩
    have hz : (if 1 < i0 then 1 else 0) * (if i0 < mKED f 2 d + 2 then 1 else 0) = 0 := by
      by_cases a : 1 < i0 <;> by_cases b : i0 < mKED f 2 d + 2 <;> simp [a, b] <;> omega
    rw [if_neg g2, hz, if_pos rfl, evalS_ite, eE_mul ho1 (eE_eq e13 (eE_add hm1 (eE_k (by omega)) (by omega)))
      (by split_ifs <;> omega)]
    by_cases g3 : gtOne f d = true ∧ i0 = mKED f 2 d + 2
    · have hp : (if gtOne f d = true then 1 else 0) * (if i0 = mKED f 2 d + 2 then 1 else 0) = 1 := by
        rw [if_pos g3.1, if_pos g3.2]
      rw [if_pos g3, hp, if_neg one_ne_zero, evalS_set,
        eE_add (eE_add A1.n (eE_mul hm1 (eE_add A1.n A1.l (by omega)) (by omega)) (by omega)) hg1 (by omega)]
      exact ⟨by simp [optOf], by simp; omega, hW _⟩
    have hz3 : (if gtOne f d = true then 1 else 0) * (if i0 = mKED f 2 d + 2 then 1 else 0) = 0 := by
      by_cases a : gtOne f d = true <;> by_cases b : i0 = mKED f 2 d + 2 <;> simp [a, b] <;> exact g3 ⟨a, b⟩
    rw [if_neg g3, hz3, if_pos rfl, evalS_seq, evalS_set, evalS_set, eE_k (by omega), eE_k (by omega)]
    refine ⟨by simp [optOf], by simp [jB], ?_⟩
    exact (((Wr.setv (W := qW) s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)

end NearCubicGates.Adapters.ShortPCP.Machines.FL
