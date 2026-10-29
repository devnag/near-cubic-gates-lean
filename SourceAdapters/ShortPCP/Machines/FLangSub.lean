import SourceAdapters.ShortPCP.TimeXs

/-!
# Single-run time, machine layer 29: one sub-verifier run of the decision half

proof of `thm:short-pcp-ours` (`V0` runs the RS and VRS verifiers once each, every run reading a prefix of the random string) and
proof of `thm:short-pcp-ours` (time): the decision of one run of the outer verifier `outV v DOM 0 BH OH d` (`TimeBlocks`) on coins
`c`. `subD` sets `6 :=` the inner degree, the coins `42/43 :=` the prefix of `c` of length `rand`, reads the answers
of the effective queries from the answer bits (`ansLoop`), and multiplies the verdict `2` by the decision
(`dOutP`). `subD_spec`: the factor is the join's `acceptsN` of the run on the tables the oracle encodes, given that
the answer blocks are the elements the run reads (`hW`, stated for any field `F0`: the queries do not depend on the
field, since `qOutP_spec` computes them for every field at the same state, `Q_transport`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable (G : Glob)

/-! ## The domain and the decision context -/

/-- The domain basis words `2^0, …, 2^(f−1)`. -/
def domW (f : ℕ) : List ℕ := (List.range f).map (2 ^ ·)

theorem domW_length (f : ℕ) : (domW f).length = f := by simp [domW]

theorem domW_lt (f : ℕ) : ∀ a ∈ domW f, a < 2 ^ f := by
  intro a ha; simp only [domW, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha; exact Nat.pow_lt_pow_right (by norm_num) hj

theorem domW_map (q : Request) {F : Type} [Field F] (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) :
    (domW q.code.f).map (ev φ) = q.domBasis φ := by
  simp only [domW, Request.domBasis, List.map_map]; rfl

/-- The global state of the decision half after the prologue. -/
structure DCtx (q : Request) (s : FS) : Prop where
  pc : PCtx G q (s.env 10)
  h15 : s.env 15 = packW (G.K / 16) (parseRec q)
  h19 : s.env 19 = packW q.code.f (domW q.code.f)
  h23 : s.env 23 = q.code.f
  fl : s.fl = q.code.f
  fp : s.fp = q.code.irr
  ok : fieldOk G q.code.f q.code.irr = true
  irr : Irreducible (GF.toPoly q.code.irr)
  tb : TblRep s q.code.f
  K : 2 * ((q.code.f + 1) * (8 * q.code.f + 16)) + 1 ≤ G.K
  N : q.code.f + 103 ≤ G.N

variable {G}

theorem DCtx.wr {q : Request} {s t : FS} {W : List Var} (c : DCtx G q s) (w : Wr W s t)
    (hW : ∀ x ∈ ([10, 15, 17, 18, 19, 23] : List Var), x ∉ W := by decide) : DCtx G q t := by
  refine ⟨?_, ?_, ?_, ?_, w.fl.trans c.fl, w.fp.trans c.fp, c.ok, c.irr, ?_, c.K, c.N⟩
  · rw [w.env 10 (hW 10 (by simp))]; exact c.pc
  · rw [w.env 15 (hW 15 (by simp))]; exact c.h15
  · rw [w.env 19 (hW 19 (by simp))]; exact c.h19
  · rw [w.env 23 (hW 23 (by simp))]; exact c.h23
  · exact c.tb.congr (w.env 17 (hW 17 (by simp))) (w.env 18 (hW 18 (by simp)))

theorem DCtx.setv {q : Request} {s : FS} (c : DCtx G q s) (i : Var) (v : ℕ)
    (hi : i ∉ ([10, 15, 17, 18, 19, 23] : List Var) := by decide) : DCtx G q (s.setv i v) :=
  c.wr (Wr.setv (W := [i]) s (by simp) v) (fun x hx h => by simp at h; subst h; exact hi hx)

theorem DCtx.qc {q : Request} {s : FS} (c : DCtx G q s) (u : List Bool) (h42 : s.env 42 = bitsValue u)
    (h43 : s.env 43 = u.length) : QC G s (domW q.code.f) u := by
  refine ⟨by rw [c.h19, c.fl], by rw [domW_length, c.fl], by rw [c.fl]; exact domW_lt _, by rw [c.h23, c.fl], h42, h43,
    by rw [c.fl, c.fp]; exact c.ok, by rw [c.fp]; exact c.irr, by rw [c.fl]; exact c.tb, by rw [c.fl]; exact c.K,
    by rw [c.fl]; have := c.N; omega⟩

theorem DCtx.atoms {q : Request} {s : FS} (c : DCtx G q s) : Atoms G s q.code.f :=
  FL.atoms c.h23 c.tb (fl_bounds c.ok).1 c.K

/-! ## Parameter expressions of the outer verifier (inner degree in `6`) -/

/-- `qcO v f d`. -/
def qcOE (v : Bool) : E := .add (qcIE (.v 6)) (.k (if v then 2 else 0))
/-- `outLen v f d`. -/
def lenOE (v : Bool) : E := if v then .add nSE (lRSE (.v 6)) else lRSE (.v 6)
/-- `outRand v f d`. -/
def randOE (v : Bool) : E := if v then iteE (.lt (rRSE (.v 6)) (.v 23)) (.v 23) (rRSE (.v 6)) else rRSE (.v 6)

theorem lRS_le (f d : ℕ) : lRS f d ≤ (d + 4) * 2 ^ (8 * f + 20) := by
  have g := gt_le f d
  have hn := nl_le f
  have h3 : 2 ^ (8 * f + 18) ≤ (d + 4) * 2 ^ (8 * f + 20) := by
    have : 2 ^ (8 * f + 18) ≤ 2 ^ (8 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (8 * f + 20) ≤ (d + 4) * 2 ^ (8 * f + 20) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h4 : 0 < 2 ^ f := by positivity
  unfold lRS; split_ifs <;> omega

theorem outLen_le (v : Bool) (f d : ℕ) : outLen v f d ≤ (d + 5) * 2 ^ (8 * f + 20) := by
  have := lRS_le f d
  have := pf_le f
  have e : (d + 5) * 2 ^ (8 * f + 20) = (d + 4) * 2 ^ (8 * f + 20) + 2 ^ (8 * f + 20) := by ring
  have : 0 < 2 ^ f := by positivity
  have : 0 < 2 ^ (8 * f + 20) := by positivity
  unfold outLen; split_ifs <;> omega

theorem rRS_le (f d : ℕ) : rRS f d ≤ 5 * f := by
  have := randEq_le f
  unfold rRS; split_ifs <;> simp <;> omega

theorem outRand_le (v : Bool) (f d : ℕ) : outRand v f d ≤ 5 * f := by
  have := rRS_le f d
  unfold outRand; split_ifs <;> simp <;> omega

section Eval

variable {s : FS} {f di : ℕ} (h23 : s.env 23 = f) (A : Atoms G s f) (h6 : s.env 6 = di)
  (hb : (di + 5) * 2 ^ (8 * f + 20) ≤ G.cap)
include h23 A h6 hb

omit h23 A h6 in
theorem hb4_of : (di + 4) * 2 ^ (8 * f + 20) ≤ G.cap :=
  le_trans (Nat.mul_le_mul_right _ (by omega)) hb

theorem qcOE_eval (v : Bool) : evalE G s (qcOE v) = qcO v f di := by
  have hb4 := hb4_of hb
  have hq := qcIE_eval h23 A (show evalE G s (.v 6) = di from h6) hb4
  have := qcO_le v f di
  have := dv_le hb4
  have := A.big
  have : 2 ^ 20 ≤ 2 ^ (8 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold qcOE
  rw [eE_add hq (eE_k (by split_ifs <;> omega)) (by unfold qcO at *; split_ifs at * <;> omega)]
  rfl

theorem lenOE_eval (v : Bool) : evalE G s (lenOE v) = outLen v f di := by
  have hb4 := hb4_of hb
  have hl := lRSE_eval h23 A (show evalE G s (.v 6) = di from h6) hb4
  have := outLen_le true f di
  cases v
  · simp [lenOE, outLen, hl]
  · simp only [lenOE, outLen, if_true] at this ⊢
    rw [eE_add A.n hl (by omega)]

theorem randOE_eval (v : Bool) : evalE G s (randOE v) = outRand v f di := by
  have hb4 := hb4_of hb
  have hr := rRSE_eval h23 A (show evalE G s (.v 6) = di from h6) hb4
  have := rRS_le f di
  have := dv_le hb4
  have hfK : 5 * f + 2 ≤ G.cap := by
    have := A.big; have : 8 * f + 20 < 2 ^ (8 * f + 20) := Nat.lt_two_pow_self; omega
  cases v
  · simp [randOE, outRand, hr]
  · simp only [randOE, outRand, if_true]
    by_cases h : rRS f di < f
    · rw [iteE_pos A.c1 (by rw [eE_lt hr (eE_v 23 |>.trans h23), if_pos h]) (eE_v 23 |>.trans h23) (by omega)]
      rw [max_eq_right h.le]
    · rw [iteE_neg A.c1 (by rw [eE_lt hr (eE_v 23 |>.trans h23), if_neg h]) hr (by omega)]
      rw [max_eq_left (by omega)]

end Eval

/-! ## One run -/

/-- **One run of the outer verifier in the decision half**: inner degree, coins, answers, decision. -/
def subD (v : Bool) (pxS : Option S) (dE bhE lhE ohE : E) : S :=
  .seq (.set 6 dE) (.seq (.set 43 (randOE v)) (.seq (.set 42 (.md (.v 4) (.shl (.k 1) (.v 43))))
    (.seq (.set 7 (lenOE v)) (.seq (ansLoop v pxS (.v 7) (.k 0) (.k 0) (qcOE v)) (dOutP v bhE lhE ohE)))))

/-- The variables `subD` writes. -/
def subW : List Var := [6, 42, 43] ++ ansW ++ dW

/-- **The queries at the effective positions do not depend on the field** (both equal the query `qOutP`
computes at the same state). -/
theorem Q_transport {F F0 : Type} [Field F] [CharP F 2] [DecidableEq F] [Field F0] [CharP F0 2] [DecidableEq F0]
    (v : Bool) (s : FS) (u : List Bool) (l0 : List ℕ) (c : QC G s l0 u)
    (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (φ0 : AdjoinRoot (GF.toPoly s.fp) →+* F0)
    (BH : List F) (OH : F) (BH0 : List F0) (OH0 : F0) (d : ℕ) (hl : BH0.length = BH.length)
    (h6 : s.env 6 = innD v BH.length d) (hbd : (innD v BH.length d + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ qcO v s.fl (innD v BH.length d)) :
    (outV v (l0.map (ev φ0)) 0 BH0 OH0 d).Q u (idxO s.fl (innD v BH0.length d) k) =
      (outV v (l0.map (ev φ)) 0 BH OH d).Q u (idxO s.fl (innD v BH.length d) k) := by
  have a := (qOutP_spec G v (s.setv 14 (k - 1)) φ u l0 BH OH d k (c.setv 14 _) (by simp; omega) (by simp [h6]) hk
    hbd).1
  have b := (qOutP_spec G v (s.setv 14 (k - 1)) φ0 u l0 BH0 OH0 d k (c.setv 14 _) (by simp; omega)
    (by simp [h6, hl]) (by rw [hl]; exact hk) (by rw [hl]; exact hbd)).1
  exact b.trans a.symm

variable {F : Type} [Field F] [DecidableEq F]

/-- **One sub-verifier run of the decision half** (proof of `thm:short-pcp-ours`): the verdict `2` is multiplied by
`acceptsN` of the run on the tables the oracle encodes (`p a = elt (wordAt o (pB + wordOf a)) + pxF a`,
`πN t = elt (wordAt o (πB + t))`), given that the answer blocks `b0, b0 + 1, …` of `16` are the elements the run
reads (`hW`, over any field `F0`). -/
theorem subD_spec (v : Bool) (pxS : Option S) (dE bhE lhE ohE : E) (q : Request) (hv : q.Valid)
    (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (hφ : Function.Bijective φ)
    {F0 : Type} [Field F0] [DecidableEq F0] (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F0)
    (s : FS) (c : DCtx G q s) (o cn : ℕ → Bool) (x d pB πB b0 W ohw : ℕ) (bhw : List ℕ) (pxF : F → F)
    (hd6 : evalE G s dE = innD v bhw.length d)
    (h4 : s.env 4 = x) (hx : ∀ i, x / 2 ^ i % 2 = (cn i).toNat)
    (h16 : s.env 16 = W) (h3 : s.env 3 = b0) (h2 : s.env 2 ≤ 1)
    (hdb : (innD v bhw.length d + 5) * 2 ^ (8 * q.code.f + 20) ≤ G.cap)
    (hbK : (b0 + 105) * q.code.f + 1 ≤ G.K)
    (hW : ∀ k, 1 ≤ k → k ≤ qcO v q.code.f (innD v bhw.length d) →
      W / 2 ^ ((b0 + (k - 1)) * q.code.f) % 2 ^ q.code.f = q.wordAt o (elemOf
        ((outV v (q.domBasis φ0) 0 (bhw.map (q.elt φ0)) (q.elt φ0 ohw) d).Q
          ((List.range (outRand v q.code.f (innD v bhw.length d))).map cn) (idxO q.code.f (innD v bhw.length d) k))
        (2 ^ q.code.f) (outLen v q.code.f (innD v bhw.length d)) pB πB))
    (hpx : (pxS = none ∧ ∀ a, pxF a = 0) ∨ (pxS = some pxP ∧ pxF = pxN q φ))
    (hbh : v = true → (∀ a ∈ bhw, a < 2 ^ q.code.f) ∧ ohw < 2 ^ q.code.f ∧
      (∀ t : FS, Wr subW s t → evalE G t bhE = packW q.code.f bhw) ∧
      (∀ t : FS, Wr subW s t → evalE G t lhE = bhw.length) ∧
      (∀ t : FS, Wr subW s t → evalE G t ohE = ohw) ∧
      q.code.f * (bhw.length + 1) + 1 ≤ G.K ∧ bhw.length + 1 ≤ G.N) :
    let t := evalS G (subD v pxS dE bhE lhE ohE) s
    t.env 2 = s.env 2 * (if acceptsN (outV v (q.domBasis φ) 0 (bhw.map (q.elt φ)) (q.elt φ ohw) d) (q.domBasis φ) 0
        (fun a => q.elt φ (q.wordAt o (pB + q.wordOf φ a)) + pxF a) (fun t => q.elt φ (q.wordAt o (πB + t))) cn
        then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ t.env 3 = b0 + qcO v q.code.f (innD v bhw.length d) ∧ Wr subW s t := by
  intro t
  haveI := charP_two q φ
  haveI := charP_two q φ0
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fl = q.code.f := c.fl
  obtain rfl : fp = q.code.irr := c.fp
  set s : FS := ⟨env, out, q.code.f, q.code.irr, ip, bad⟩ with hs
  have hmod : GF.ModulusOk q.code.irr q.code.f := (fl_bounds c.ok).2.2.1
  have hf1 : 1 ≤ q.code.f := (fl_bounds c.ok).1
  have hcK := cap_ge G
  have hb4 := hb4_of hdb
  have hrand := outRand_le v q.code.f (innD v bhw.length d)
  have hqc := qcO_le v q.code.f (innD v bhw.length d)
  have hKf : 2 * ((q.code.f + 1) * (8 * q.code.f + 16)) + 1 ≤ G.K := c.K
  have h5f : 5 * q.code.f + 1 ≤ G.K := by nlinarith
  -- the setup
  generalize hdi : innD v bhw.length d = di at hd6 hdb hb4 hW hrand hqc
  set rand := outRand v q.code.f di with hrd
  set u := (List.range rand).map cn with hu
  have hbu : bitsValue u = x % 2 ^ rand := bv_coins cn x rand hx
  have e6 : evalS G (.set 6 dE) s = s.setv 6 di := by rw [evalS_set, hd6]
  have c1 : DCtx G q (s.setv 6 di) := c.setv 6 _
  have e43 : evalE G (s.setv 6 di) (randOE v) = rand := randOE_eval c1.h23 c1.atoms (by simp) hdb v
  have e42 : evalE G ((s.setv 6 di).setv 43 rand) (.md (.v 4) (.shl (.k 1) (.v 43))) = x % 2 ^ rand :=
    eE_md (by simp [evalE, h4]) (eE_pow (by simp [evalE]) (by omega))
  have c2' : DCtx G q (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)) := (c1.setv 43 _).setv 42 _
  have e7 : evalE G (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)) (lenOE v) = outLen v q.code.f di :=
    lenOE_eval c2'.h23 c2'.atoms (by simp) hdb v
  set s3 := (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)).setv 7 (outLen v q.code.f di) with hs3
  have c3 : DCtx G q s3 := c2'.setv 7 _
  have q3 : QC G s3 (domW q.code.f) u := c3.qc u (by simp [s3, hbu]) (by simp [s3, u])
  have w3 : Wr subW s s3 :=
    (((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
      (Wr.setv _ (by decide) _)
  have e36 : s3.env 6 = di := by simp [s3]
  have ht : t = evalS G (dOutP v bhE lhE ohE) (evalS G (ansLoop v pxS (.v 7) (.k 0) (.k 0) (qcOE v)) s3) := by
    show evalS G (subD v pxS dE bhE lhE ohE) s = _
    simp only [subD, evalS_seq, evalS_set]; rw [hd6, e43, e42, e7]
  -- the answers
  have hlB : (bhw.map (q.elt φ)).length = bhw.length := List.length_map _
  have hpx' : ∀ P, pxS = some P → ∀ t' : FS, QC G t' (domW q.code.f) u → Wr ansW s3 t' → t'.env 52 < 2 ^ s3.fl →
      (evalS G P t').env 53 < 2 ^ s3.fl ∧ ev φ ((evalS G P t').env 53) = (fun j => pxF (q.elt φ j)) (t'.env 52) ∧
        Wr pxW t' (evalS G P t') := by
    intro P hP t' ct' wt' h52
    rcases hpx with ⟨h0, -⟩ | ⟨h1, hF⟩
    · rw [h0] at hP; cases hP
    · rw [h1] at hP; cases hP
      obtain ⟨env', out', fl', fp', ip', bad'⟩ := t'
      obtain rfl : fp' = q.code.irr := wt'.fp
      obtain rfl : fl' = q.code.f := wt'.fl
      obtain ⟨-, hind, hxl⟩ := valid_px q hv φ hφ
      have e15 : env' 15 = packW (G.K / 16) (parseRec q) := (wt'.env 15 (by decide)).trans c3.h15
      have e23 : env' 23 = q.code.f := (wt'.env 23 (by decide)).trans c3.h23
      have r := pxP_spec G ⟨env', out', q.code.f, q.code.irr, ip', bad'⟩ φ q c.pc e15 e23 rfl c.ok c.irr hind hxl h52
      refine ⟨r.1, ?_, r.2.2⟩
      rw [r.2.1, hF]; rfl
  have hle0 : min 0 G.cap = 0 := Nat.zero_min _
  obtain ⟨⟨ansl, a11, alt, aev⟩, a3, a6, afp, afl, aw⟩ := ansLoop_spec G v pxS (.v 7) (.k 0) (.k 0) (qcOE v) s3 φ
    u (domW q.code.f) (bhw.map (q.elt φ)) (q.elt φ ohw) d (outLen v q.code.f di) 0 0 W b0
    (fun j => pxF (q.elt φ j)) q3 (by rw [hlB, hdi]; exact e36)
    (by rw [hlB, hdi]; exact qcOE_eval (by simp [s3, c.h23]) (c3.setv 11 0).atoms (by simp [s3]) hdb v)
    (by rw [hlB, hdi]; show qcO v q.code.f di ≤ G.N; have := c.N; omega) (by rw [hlB, hdi]; exact hb4) (by simp [s3, h16]) (by simp [s3, h3])
    (fun t' w' => by rw [eE_v, w'.env 7 (by decide)]; simp [s3])
    (fun t' w' => hle0) (fun t' w' => hle0)
    (by have := pow_le_cap (G := G) (a := q.code.f + 1) (by omega); rw [pow_succ] at this
        show 0 + 2 ^ q.code.f ≤ G.cap; omega)
    (by have := outLen_le v q.code.f di; show 0 + outLen v q.code.f di ≤ G.cap; omega)
    (by rw [hlB, hdi]; show (b0 + qcO v q.code.f di) * q.code.f ≤ G.cap
        exact le_trans (Nat.mul_le_mul_right q.code.f (show b0 + qcO v q.code.f di ≤ b0 + 105 by omega)) (by omega))
    (by rw [hlB, hdi]; show 2 ^ ((qcO v q.code.f di + 1) * q.code.f) ≤ G.cap + 1
        exact pow_le_cap (le_trans (Nat.mul_le_mul_right q.code.f (show qcO v q.code.f di + 1 ≤ b0 + 105 by omega))
          (by omega)))
    hpx'
  rw [hlB, hdi] at aev a3 a6
  replace aev : ∀ k, 1 ≤ k → k ≤ qcO v q.code.f di → ev φ (ansl.getD k 0) = ansAt φ v (domW q.code.f)
      (bhw.map (q.elt φ)) (q.elt φ ohw) d q.code.f (outLen v q.code.f di) W b0 u (fun j => pxF (q.elt φ j))
      pxS.isSome k := by
    intro k h1 h2; exact aev k h1 h2
  generalize ht1 : evalS G (ansLoop v pxS (.v 7) (.k 0) (.k 0) (qcOE v)) s3 = t1 at a11 a3 a6 afp afl aw ht
  have w1 : Wr subW s t1 := w3.trans (aw.mono (by decide))
  obtain ⟨env1, out1, fl1, fp1, ip1, bad1⟩ := t1
  obtain rfl : fp1 = q.code.irr := afp
  obtain rfl : fl1 = q.code.f := afl
  set t1 : FS := ⟨env1, out1, q.code.f, q.code.irr, ip1, bad1⟩ with ht1d
  have q1 : QC G t1 (domW q.code.f) u := q3.wr aw (by decide) rfl
  have hind : Indep ((domW q.code.f).map (ev φ)) := by rw [domW_map]; exact indep_domBasis q φ hv hφ
  have hdom : ∀ w, sel ((domW q.code.f).map (ev φ)) w = ev φ (w % 2 ^ t1.fl) := by
    intro w; rw [domW_map]; exact sel_domList q φ hφ q.code.f w
  have e12 : t1.env 2 = s.env 2 := by rw [aw.env 2 (by decide)]; simp [s3]
  obtain ⟨d2, d2le, dw⟩ := dOutP_spec G v bhE lhE ohE t1 φ u (domW q.code.f) ansl bhw ohw di q1 hind hdom a6 a11
    alt (by rw [e12]; exact h2) (fun hvt => by
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := hbh hvt
      refine ⟨hb4, b1, b2, fun t' w' => b3 t' (w1.trans (w'.mono (by decide))),
        fun t' w' => b4 t' (w1.trans (w'.mono (by decide))), fun t' w' => b5 t' (w1.trans (w'.mono (by decide))),
        b6, b7, ?_⟩
      have : qcI q.code.f di ≤ 101 := by have := qcO_le true q.code.f di; unfold qcO at this; simp at this; omega
      show (qcI q.code.f di + 3) * q.code.f ≤ G.K
      exact le_trans (Nat.mul_le_mul_right q.code.f (show qcI q.code.f di + 3 ≤ b0 + 105 by omega)) (by omega))
  rw [← ht] at d2 d2le dw
  replace d2 : t.env 2 = s.env 2 * (if outD v (q.domBasis φ) 0 (bhw.map (q.elt φ)) (q.elt φ ohw) di u
      (fun i => ev φ (ansl.getD i 0)) then 1 else 0) := by
    rw [← e12, ← domW_map]; exact d2
  -- the math: the decision is `acceptsN`
  have hB : (q.domBasis φ).length = q.code.f := domBasis_length q φ
  have hpar := outV_params v (q.domBasis φ) 0 (bhw.map (q.elt φ)) (q.elt φ ohw) d
  rw [hB, hlB, hdi] at hpar
  have key := acceptsN_out v (q.domBasis φ) 0 (bhw.map (q.elt φ)) (q.elt φ ohw) d
    (fun a => q.elt φ (q.wordAt o (pB + q.wordOf φ a)) + pxF a) (fun t => q.elt φ (q.wordAt o (πB + t))) cn
    (fun i => ev φ (ansl.getD i 0)) (by
      intro k hk1 hk
      rw [hB, hlB, hdi] at hk
      rw [hB, hlB, hdi, hpar.2, aev k hk1 hk]
      unfold ansAt
      rw [hlB, hdi, hW k hk1 hk]
      have htr : (outV v (q.domBasis φ0) 0 (bhw.map (q.elt φ0)) (q.elt φ0 ohw) d).Q u (idxO q.code.f di k) =
          (outV v (q.domBasis φ) 0 (bhw.map (q.elt φ)) (q.elt φ ohw) d).Q u (idxO q.code.f di k) := by
        have := Q_transport v s3 u (domW q.code.f) q3 φ φ0 (bhw.map (q.elt φ)) (q.elt φ ohw)
          (bhw.map (q.elt φ0)) (q.elt φ0 ohw) d (by simp) (by rw [hlB, hdi]; exact e36)
          (by rw [hlB, hdi]; exact hb4) k hk1 (by rw [hlB, hdi]; exact hk)
        rw [List.length_map, hdi, hlB, hdi] at this
        rw [← domW_map q φ0, ← domW_map q φ]; exact this
      rw [htr]
      rw [← domW_map q φ, ← hpar.1, domW_map]
      exact ansVal_eq_answersN q φ hφ hmod _ o u _ pB πB pxF pxS.isSome (by
        intro h a; rcases hpx with ⟨-, h0⟩ | ⟨h1, -⟩
        · exact h0 a
        · rw [h1] at h; cases h))
  rw [hlB, hdi, hpar.2] at key
  refine ⟨?_, d2le, ?_, w1.trans (dw.mono (by decide))⟩
  · rw [d2, key]
  · rw [dw.env 3 (by decide)]; exact a3

end NearCubicGates.Adapters.ShortPCP.Machines.FL
