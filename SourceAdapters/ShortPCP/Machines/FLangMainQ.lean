import SourceAdapters.ShortPCP.Machines.FLangEmit

/-!
# Single-run time, machine layer 34: the query half

proof of `thm:short-pcp-ours`, Step 2, "The instance" ("The queries of V0 are computed from the random string alone") and proof of `thm:short-pcp-ours` (the proof bits are
read at addresses below `L_π`): the `FL` program of stage 2 of `Time.singleRunTime_of_stages`. For each mask and
each sub-verifier run it computes the effective queries (`qOutP`), their elements (`kindP`) and emits the `f`
address entries of each element (`emitX`); the consistency test's elements come from `cqP` (`consQ`). The emitted
blocks are `Time.blocks`, i.e. the addresses are `Time.xsOf`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)

variable {G : Glob}

theorem QC.em {s t : FS} {l0 : List ℕ} {u : List Bool} {W : List Var} {w : List Bool} (c : QC G s l0 u)
    (e : Em W s t w) (hW : ∀ x ∈ ([17, 18, 19, 23, 42, 43] : List Var), x ∉ W := by decide) : QC G t l0 u := by
  obtain ⟨a, b, c', d, e', f, g, h, i, j, k⟩ := c.wr (t := { t with out := s.out }) ⟨e.env, rfl, e.fl, e.fp, e.bad⟩ hW e.fp
  exact ⟨a, b, c', d, e', f, g, h, i, j, k⟩

theorem DCtx.em {q : Request} {s t : FS} {W : List Var} {w : List Bool} (c : DCtx G q s) (e : Em W s t w)
    (hW : ∀ x ∈ ([10, 15, 17, 18, 19, 23] : List Var), x ∉ W := by decide) : DCtx G q t := by
  obtain ⟨a, b, c', d, e', f, g, h, i, j, k⟩ := c.wr (t := { t with out := s.out }) ⟨e.env, rfl, e.fl, e.fp, e.bad⟩ hW
  exact ⟨a, b, c', d, e', f, g, h, i, j, k⟩

theorem em_of_wr {p : S} {W : List Var} {s : FS} (hp : rdFree p = true) (w : Wr W s (evalS G p s)) :
    Em W s (evalS G p s) [] :=
  ⟨w.env, by rw [w.out]; simp [dbl], w.fl, w.fp, ip_rdFree G p s hp, w.bad⟩

theorem elemOf_le (o : Option ℕ) (nS len pB πB : ℕ) (h : 1 ≤ nS) : elemOf o nS len pB πB < pB + nS + πB + len + 1 := by
  cases o with
  | none => simp [elemOf]
  | some j => simp only [elemOf]; split_ifs <;> omega

/-! ## One sub-verifier run -/

/-- The entries of the effective queries of one run (loop variable `14`). -/
def emitX (v : Bool) (lenE pBE πBE : E) : S :=
  .loop 14 (qcOE v) (.seq (qOutP v) (.seq (kindP lenE pBE πBE) elemE))

/-- The variables `emitX` writes. -/
def emitXW : List Var := [14, 12, 13, 5, 8] ++ qW

variable {F0 : Type} [Field F0] [CharP F0 2] [DecidableEq F0]

theorem emitX_spec (v : Bool) (lenE pBE πBE : E) (s : FS) (φ0 : AdjoinRoot (GF.toPoly s.fp) →+* F0) (u : List Bool)
    (l0 : List ℕ) (BH : List F0) (OH : F0) (d L pB πB : ℕ) (c : QC G s l0 u) (h6 : s.env 6 = innD v BH.length d)
    (h2 : s.env 2 = L) (hdb : (innD v BH.length d + 5) * 2 ^ (8 * s.fl + 20) ≤ G.cap)
    (hpB : ∀ t : FS, (∀ j, j ∉ emitXW → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t pBE = pB)
    (hπB : ∀ t : FS, (∀ j, j ∉ emitXW → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t πBE = πB)
    (hlE : ∀ t : FS, (∀ j, j ∉ emitXW → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp →
      evalE G t lenE = outLen v s.fl (innD v BH.length d))
    (hB : (pB + 2 ^ s.fl + πB + outLen v s.fl (innD v BH.length d) + 2) * s.fl ≤ G.cap) (hL : L ≤ G.N)
    (hN : 103 ≤ G.N) :
    Em emitXW s (evalS G (emitX v lenE pBE πBE) s)
      ((blkX v (l0.map (ev φ0)) BH OH d (outLen v s.fl (innD v BH.length d)) pB πB u).flatMap (elemW L s.fl)) := by
  have hlen : (l0.map (ev φ0)).length = s.fl := by rw [List.length_map, c.hl0]
  have A := c.atoms
  obtain ⟨hf1, hfK, -, -⟩ := fl_bounds c.ok
  have hcK := cap_ge G
  have hjb := c.jb4
  have hNf := c.N
  generalize hdi : innD v BH.length d = di at h6 hdb hB hlE ⊢
  have hb4 := hb4_of hdb
  have hqc := qcOE_eval c.h23 A h6 hdb v
  have hqle := qcO_le v s.fl di
  have hol := outLen_le v s.fl di
  have h2c : 2 ≤ G.cap := by omega
  have hm : min (evalE G s (qcOE v)) G.N = qcO v s.fl di := by rw [hqc]; exact min_eq_left (by omega)
  have key := Em_loop 14 (qcOE v) (.seq (qOutP v) (.seq (kindP lenE pBE πBE) elemE)) emitXW (by decide) s
    (qcO v s.fl di) hm (fun _ => True) trivial
    (fun j => elemW L s.fl (elemOf ((outV v (l0.map (ev φ0)) 0 BH OH d).Q u (idxO s.fl di (j + 1))) (2 ^ s.fl)
      (outLen v s.fl di) pB πB)) (by
      intro j hj t _ te
      refine ⟨trivial, ?_⟩
      obtain ⟨tenv, tout, tfl, tfp, tip, tbad⟩ := t
      obtain rfl : tfp = s.fp := te.fp
      obtain rfl : tfl = s.fl := te.fl
      set t : FS := ⟨tenv, tout, s.fl, s.fp, tip, tbad⟩ with htd
      have ct : QC G (t.setv 14 j) l0 u := (c.em te).setv 14 j
      have e6 : (t.setv 14 j).env 6 = innD v BH.length d := by simp; rw [te.env 6 (by decide), h6, hdi]
      obtain ⟨q1, q9, qw⟩ := qOutP_spec G v (t.setv 14 j) φ0 u l0 BH OH d (j + 1) ct (by simp) e6
        (by rw [hdi]; exact (by omega : j + 1 ≤ qcO v s.fl di)) (by rw [hdi]; exact hb4)
      have e1 := em_of_wr (by cases v <;> decide) qw
      rw [hdi] at q1
      replace q1 : (outV v (l0.map (ev φ0)) 0 BH OH d).Q u (idxO s.fl di (j + 1)) = optOf (evalS G (qOutP v) (t.setv 14 j)) := q1
      generalize ht1 : evalS G (qOutP v) (t.setv 14 j) = t1 at q1 q9 qw e1
      have hfl1 : t1.fl = s.fl := by rw [qw.fl, te.fl]; rfl
      have hfp1 : t1.fp = s.fp := by rw [qw.fp, te.fp]; rfl
      have hW1 : ∀ x, x ∉ emitXW → t1.env x = s.env x := by
        intro x hx; rw [qw.env x (fun h => hx (by simp [emitXW, h]))]; simp
        rw [Function.update_of_ne (fun h => hx (by simp [h, emitXW]))]; exact te.env x hx
      have e23 : t1.env 23 = s.fl := by rw [hW1 23 (by decide)]; exact c.h23
      have e6' : t1.env 6 = di := by rw [hW1 6 (by decide), h6]
      have A1 : Atoms G t1 s.fl := by
        have := (ct.wr qw (by decide) qw.fp).atoms; rwa [qw.fl] at this
      have hB1 : pB + 2 ^ s.fl ≤ G.cap ∧ πB + outLen v s.fl di ≤ G.cap := by
        have : (pB + 2 ^ s.fl + πB + outLen v s.fl di + 2) * 1 ≤ (pB + 2 ^ s.fl + πB + outLen v s.fl di + 2) * s.fl :=
          Nat.mul_le_mul le_rfl hf1
        omega
      have q9' : t1.env 9 < 2 * jB s.fl := q9
      have h9 : t1.env 9 + 2 ^ s.fl ≤ G.cap := by have := hjb; omega
      have hcf : 2 * 2 ^ s.fl ≤ G.cap := by have := hjb; omega
      obtain ⟨k12, k13, kw⟩ := kindP_spec G lenE pBE πBE t1 s.fl (outLen v s.fl di) pB πB e23 hfK
        (hlE t1 hW1 hfl1 hfp1) (hpB t1 hW1 hfl1 hfp1) (hπB t1 hW1 hfl1 hfp1) h9 hB1.1 hB1.2 hcf
      have e2 := em_of_wr (by simp [kindP, rdFree]) kw
      generalize ht2 : evalS G (kindP lenE pBE πBE) t1 = t2 at k12 k13 kw e2
      have hkl := elemOf_le (optOf t1) (2 ^ s.fl) (outLen v s.fl di) pB πB Nat.one_le_two_pow
      have f2 : t2.env 2 = L := by
        rw [kw.env 2 (by decide), qw.env 2 (by decide)]; simp only [FS.setv_env]
        rw [Function.update_of_ne (by decide), te.env 2 (by decide), h2]
      have f23 : t2.env 23 = s.fl := by rw [kw.env 23 (by decide), e23]
      have hk1 : (elemOf (optOf t1) (2 ^ s.fl) (outLen v s.fl di) pB πB + 1) * s.fl ≤ G.cap :=
        le_trans (Nat.mul_le_mul_right _ (by omega)) hB
      have ee := elemE_spec (G := G) t2 L s.fl _ f2 k13 f23 hL (by omega) hk1 h2c
      have ht : evalS G (.seq (qOutP v) (.seq (kindP lenE pBE πBE) elemE)) (t.setv 14 j) =
          evalS G elemE t2 := by simp only [evalS_seq]; rw [ht1, ht2]
      rw [ht, q1]
      have := ((e1.mono (W' := emitXW) (by decide)).trans (e2.mono (W' := emitXW) (by decide))).trans
        (ee.mono (W' := emitXW) (by decide))
      simpa using this)
  have hw := key.2
  unfold blkX
  rw [hlen, hdi, List.flatMap_map]
  exact hw

/-! ## The consistency test's elements -/

/-- Word `14` of the packed list `37`. -/
def getE : E := .md (.shr (.v 37) (.mul (.v 14) (.v 23))) nSE

/-- The elements of the consistency test: `p0` at the neighbours (`cqP`), then `p1` at `α` (`7 = |π0|`). -/
def consQ : S :=
  .seq (.set 42 (.v 4)) (.seq cqP (.seq (.loop 14 (recE 5) (.seq (.set 13 getE) elemE))
    (.seq (.set 13 (.add (.add nSE (.v 7)) (.v 36))) elemE)))

/-- The variables `consQ` writes. -/
def consQW : List Var := [42, 13, 14, 5, 8] ++ cqW

theorem consQ_spec (q : Request) (hv : q.Valid) {F1 : Type} [Field F1] (φ1 : AdjoinRoot (GF.toPoly q.code.irr) →+* F1)
    (s : FS) (c : DCtx G q s) (cn : ℕ → Bool) (x L : ℕ) (h4 : s.env 4 = x)
    (hx : ∀ i, x / 2 ^ i % 2 = (cn i).toNat) (h7 : s.env 7 = lenR q) (h2 : s.env 2 = L) (hL : L ≤ G.N)
    (hB : (4 * 2 ^ q.code.f + lenR q + 2) * q.code.f ≤ G.cap) (hcN : q.code.cN ≤ G.N)
    (hcf : q.code.cN * q.code.f ≤ G.cap) :
    Em consQW s (evalS G consQ s) ((blkC q cn).flatMap (elemW L q.code.f)) := by
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fl = q.code.f := c.fl
  obtain rfl : fp = q.code.irr := c.fp
  set s : FS := ⟨env, out, q.code.f, q.code.irr, ip, bad⟩ with hs
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hcK := cap_ge G
  have hp1 : 1 ≤ 2 ^ q.code.f := Nat.one_le_two_pow
  have h2c : 2 ≤ G.cap := by
    have : (1 + 2) * 1 ≤ (4 * 2 ^ q.code.f + lenR q + 2) * q.code.f := Nat.mul_le_mul (by omega) hf1
    omega
  set a := x % 2 ^ q.code.f with ha
  have hal : a < 2 ^ q.code.f := Nat.mod_lt _ (by positivity)
  have hB1 : 4 * 2 ^ q.code.f + lenR q + 2 ≤ G.cap := le_trans (Nat.le_mul_of_pos_right _ hf1) hB
  have c1 : DCtx G q (s.setv 42 x) := c.setv 42 x
  obtain ⟨k36, k37, kw⟩ := cqP_spec G (s.setv 42 x) φ1 q c1.pc c1.h15 c1.h23 rfl c.ok
  simp only [FS.setv_env, Function.update_self] at k36 k37
  have e1 : Em consQW s (evalS G cqP (s.setv 42 x)) [] := by
    have a1 : Em consQW s (s.setv 42 x) [] := Em.setv s (W := consQW) (i := 42) (by decide) x
    have a2 : Em cqW (s.setv 42 x) (evalS G cqP (s.setv 42 x)) [] := em_of_wr (by decide) kw
    simpa using a1.trans (a2.mono (W' := consQW) (by decide))
  generalize hs2 : evalS G cqP (s.setv 42 x) = s2 at k36 k37 kw e1
  have c2 : DCtx G q s2 := c.em e1
  have hnb : ∀ i, nbW q q.code.irr a i < 2 ^ q.code.f := fun i => (nbW_spec q φ1 hmod hv.1 a i hal).1
  have hm : min (evalE G s2 (recE 5)) G.N = q.code.cN := by
    rw [recE_parse G s2 q c2.pc c2.h15 5 (by norm_num)]; exact min_eq_left hcN
  have f2 : s2.env 2 = L := by rw [e1.env 2 (by decide), h2]
  have f7 : s2.env 7 = lenR q := by rw [e1.env 7 (by decide), h7]
  have hl := Em_loop 14 (recE 5) (.seq (.set 13 getE) elemE) [13, 14, 5, 8] (by decide) s2 q.code.cN hm
    (fun _ => True) trivial (fun i => elemW L q.code.f (nbW q q.code.irr a i)) (by
      intro j hj t _ te
      refine ⟨trivial, ?_⟩
      have hg : evalE G (t.setv 14 j) getE = nbW q q.code.irr a j := by
        have e37 : (t.setv 14 j).env 37 = packW q.code.f ((List.range q.code.cN).map (nbW q q.code.irr a)) := by
          simp; rw [te.env 37 (by decide), k37]; rfl
        have e23 : (t.setv 14 j).env 23 = q.code.f := by simp; rw [te.env 23 (by decide), c2.h23]
        have hjf : j * q.code.f ≤ G.cap := le_trans (Nat.mul_le_mul_right _ hj.le) hcf
        rw [getE, eE_md (eE_shr (eE_v 37 |>.trans e37) (eE_mul (by simp [evalE]) (eE_v 23 |>.trans e23) hjf))
          (nSE_eval G e23 (by omega)), packW_get _ _ (by
            intro b hb; simp only [List.mem_map] at hb; obtain ⟨i, -, rfl⟩ := hb; exact hnb i)]
        rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp
      have g2 : ((t.setv 14 j).setv 13 (nbW q q.code.irr a j)).env 2 = L := by simp; rw [te.env 2 (by decide), f2]
      have g23 : ((t.setv 14 j).setv 13 (nbW q q.code.irr a j)).env 23 = q.code.f := by
        simp; rw [te.env 23 (by decide), c2.h23]
      have ee := elemE_spec (G := G) ((t.setv 14 j).setv 13 (nbW q q.code.irr a j)) L q.code.f
        (nbW q q.code.irr a j) g2 (by simp) g23 hL
        (by have := c.N; omega) (le_trans (Nat.mul_le_mul_right _ (by have := hnb j; omega)) hB) h2c
      have := (Em.setv (t.setv 14 j) (W := [13, 14, 5, 8]) (i := 13) (by decide) (nbW q q.code.irr a j)).trans
        (ee.mono (by decide))
      simp only [evalS_seq, evalS_set, hg]
      simpa using this)
  generalize hs3 : evalS G (.loop 14 (recE 5) (.seq (.set 13 getE) elemE)) s2 = s3 at hl
  have e3 := hl.2
  have g3 : evalE G s3 (.add (.add nSE (.v 7)) (.v 36)) = 2 ^ q.code.f + lenR q + a := by
    have e23 : s3.env 23 = q.code.f := by rw [e3.env 23 (by decide), c2.h23]
    have := nSE_eval G e23 (by omega)
    rw [eE_add (eE_add this (eE_v 7 |>.trans (by rw [e3.env 7 (by decide), f7])) (by omega))
      (eE_v 36 |>.trans (by rw [e3.env 36 (by decide), k36])) (by omega)]
  have ee := elemE_spec (G := G) (s3.setv 13 (2 ^ q.code.f + lenR q + a)) L q.code.f (2 ^ q.code.f + lenR q + a)
    (by simp; rw [e3.env 2 (by decide), f2]) (by simp) (by simp; rw [e3.env 23 (by decide), c2.h23]) hL
    (by have := c.N; omega) (le_trans (Nat.mul_le_mul_right _ (by omega)) hB) h2c
  have ht : evalS G consQ s = evalS G elemE (s3.setv 13 (2 ^ q.code.f + lenR q + a)) := by
    show evalS G (.seq _ _) s = _
    simp only [evalS_seq]
    rw [show evalS G (.set 42 (.v 4)) s = s.setv 42 x by rw [evalS_set, eE_v, h4], hs2, hs3, evalS_set, g3]
  rw [ht]
  have := e1.trans ((e3.mono (W' := consQW) (by decide)).trans
    ((Em.setv s3 (W := consQW) (i := 13) (by decide) _).trans (ee.mono (by decide))))
  have hα : alphaW q cn = a := bv_coins cn x _ hx
  simpa [blkC, hα, List.flatMap_append, List.flatMap_map] using this

/-! ## One run, one mask -/

/-- One run of the query half: inner degree, coins, the entries of its effective queries. -/
def subQ (v : Bool) (dE pBE πBE : E) : S :=
  .seq (.set 6 dE) (.seq (.set 43 (randOE v)) (.seq (.set 42 (.md (.v 4) (.shl (.k 1) (.v 43))))
    (.seq (.set 3 (lenOE v)) (emitX v (.v 3) pBE πBE))))

/-- The variables `subQ` writes. -/
def subQW : List Var := [6, 42, 43, 3] ++ emitXW

theorem subQ_spec (v : Bool) (dE pBE πBE : E) (q : Request) (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F0)
    (s : FS) (c : DCtx G q s) (cn : ℕ → Bool) (x d pB πB L ohw : ℕ) (bhw : List ℕ)
    (hd6 : evalE G s dE = innD v bhw.length d) (h4 : s.env 4 = x) (hx : ∀ i, x / 2 ^ i % 2 = (cn i).toNat)
    (h2 : s.env 2 = L) (hdb : (innD v bhw.length d + 5) * 2 ^ (8 * q.code.f + 20) ≤ G.cap)
    (hpB : ∀ t : FS, (∀ j, j ∉ subQW → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t pBE = pB)
    (hπB : ∀ t : FS, (∀ j, j ∉ subQW → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t πBE = πB)
    (hB : (pB + 2 ^ q.code.f + πB + outLen v q.code.f (innD v bhw.length d) + 2) * q.code.f ≤ G.cap) (hL : L ≤ G.N) :
    Em subQW s (evalS G (subQ v dE pBE πBE) s)
      ((blkX v (q.domBasis φ0) (bhw.map (q.elt φ0)) (q.elt φ0 ohw) d (outLen v q.code.f (innD v bhw.length d)) pB πB
        ((List.range (outRand v q.code.f (innD v bhw.length d))).map cn)).flatMap (elemW L q.code.f)) := by
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fl = q.code.f := c.fl
  obtain rfl : fp = q.code.irr := c.fp
  set s : FS := ⟨env, out, q.code.f, q.code.irr, ip, bad⟩ with hs
  have hKf : 2 * ((q.code.f + 1) * (8 * q.code.f + 16)) + 1 ≤ G.K := c.K
  have h5f : 5 * q.code.f + 1 ≤ G.K := by nlinarith
  generalize hdi : innD v bhw.length d = di at hd6 hdb hB ⊢
  set rand := outRand v q.code.f di with hrd
  have hrand := outRand_le v q.code.f di
  set u := (List.range rand).map cn with hu
  have hbu : bitsValue u = x % 2 ^ rand := bv_coins cn x rand hx
  have c1 : DCtx G q (s.setv 6 di) := c.setv 6 _
  have e43 : evalE G (s.setv 6 di) (randOE v) = rand := randOE_eval c1.h23 c1.atoms (by simp) hdb v
  have e42 : evalE G ((s.setv 6 di).setv 43 rand) (.md (.v 4) (.shl (.k 1) (.v 43))) = x % 2 ^ rand :=
    eE_md (by simp [evalE, h4]) (eE_pow (by simp [evalE]) (by omega))
  have c2' : DCtx G q (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)) := (c1.setv 43 _).setv 42 _
  have e3 : evalE G (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)) (lenOE v) = outLen v q.code.f di :=
    lenOE_eval c2'.h23 c2'.atoms (by simp) hdb v
  set s3 := (((s.setv 6 di).setv 43 rand).setv 42 (x % 2 ^ rand)).setv 3 (outLen v q.code.f di) with hs3
  have c3 : DCtx G q s3 := c2'.setv 3 _
  have q3 : QC G s3 (domW q.code.f) u := c3.qc u (by simp [s3, hbu]) (by simp [s3, u])
  have w3 : Em subQW s s3 [] := by
    have := (((Em.setv s (W := subQW) (i := 6) (by decide) di).trans (Em.setv _ (W := subQW) (i := 43) (by decide)
      rand)).trans (Em.setv _ (W := subQW) (i := 42) (by decide) (x % 2 ^ rand))).trans
      (Em.setv _ (W := subQW) (i := 3) (by decide) (outLen v q.code.f di))
    simpa using this
  have ht : evalS G (subQ v dE pBE πBE) s = evalS G (emitX v (.v 3) pBE πBE) s3 := by
    simp only [subQ, evalS_seq, evalS_set]; rw [hd6, e43, e42, e3]
  rw [ht]
  have hlB : (bhw.map (q.elt φ0)).length = bhw.length := List.length_map _
  have ex := emitX_spec (G := G) (F0 := F0) v (.v 3) pBE πBE s3 φ0 u (domW q.code.f) (bhw.map (q.elt φ0)) (q.elt φ0 ohw) d L
    pB πB q3 (by rw [hlB, hdi]; simp [s3]) (by simp [s3, h2]) (by rw [hlB, hdi]; exact hdb)
    (fun t ht' hfl hfp => hpB t (fun j hj => by
      rw [ht' j (fun h => hj (by simp [subQW, h]))]; exact w3.env j hj) hfl hfp)
    (fun t ht' hfl hfp => hπB t (fun j hj => by
      rw [ht' j (fun h => hj (by simp [subQW, h]))]; exact w3.env j hj) hfl hfp)
    (fun t ht' _ _ => by rw [hlB, hdi, eE_v, ht' 3 (by decide)]; simp [s3]; rfl)
    (by rw [hlB, hdi]; exact hB) hL (by have := c.N; omega)
  rw [hlB, hdi] at ex
  have ex' : Em emitXW s3 (evalS G (emitX v (.v 3) pBE πBE) s3) ((blkX v (q.domBasis φ0) (bhw.map (q.elt φ0))
      (q.elt φ0 ohw) d (outLen v q.code.f di) pB πB u).flatMap (elemW L q.code.f)) := by
    rw [← domW_map q φ0]; exact ex
  simpa using w3.trans (ex'.mono (by decide))

theorem blkX_false {F : Type} [Field F] [DecidableEq F] (B BH : List F) (OH : F) (d len pB πB : ℕ) (u : List Bool) :
    blkX false B BH OH d len pB πB u = blkX false B [] 0 d len pB πB u := by
  simp [blkX, outV, innD]

/-- The table lengths fit the clamp. -/
theorem Big.elems {q : Request} (bg : Big G q) (db : DBounds q) :
    (4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2) * q.code.f ≤ G.cap := by
  have hdA := db.dA
  have hdB := db.dB
  have hdH : dH q ≤ q.dB := Nat.sub_le _ _
  have hdI : dI q ≤ q.dA := Nat.sub_le _ _
  set P := 2 ^ (8 * q.code.f + 20) with hP
  set X := 2 ^ q.data.length with hX
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hfd := db.f
  have hfX : q.code.f < X := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h1 : lenR q ≤ (X + 5) * P :=
    le_trans (outLen_le false _ _) (Nat.mul_le_mul_right _ (by omega))
  have h2 : lenH q ≤ (X + 5) * P :=
    le_trans (outLen_le true _ _) (Nat.mul_le_mul_right _ (by omega))
  have h3 : lenI q ≤ (X + 5) * P :=
    le_trans (outLen_le true _ _) (Nat.mul_le_mul_right _ (by omega))
  have h4 : 2 ^ q.code.f ≤ P := pf_le _
  have e1 : (32 * X) * P = 4 * ((X + 5) * P) + (28 * X - 20) * P := by
    have : 4 * ((X + 5) * P) + (28 * X - 20) * P = (4 * (X + 5) + (28 * X - 20)) * P := by ring
    rw [this, show 4 * (X + 5) + (28 * X - 20) = 32 * X by omega]
  have h5 : (28 * X - 20) * P ≥ 6 * P := Nat.mul_le_mul_right _ (by omega)
  have hs : 4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2 ≤ (32 * X) * P := by omega
  have h6 : (4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2) * q.code.f ≤ (32 * X) * P * X :=
    Nat.mul_le_mul hs hfX.le
  have e2 : (32 * X) * P * X = 2 ^ (5 + q.data.length + (8 * q.code.f + 20) + q.data.length) := by
    rw [hX, hP, pow_add, pow_add, pow_add]; norm_num; ring
  have h7 : 2 ^ (5 + q.data.length + (8 * q.code.f + 20) + q.data.length) ≤ 2 ^ (10 * q.data.length + 25) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : 2 ^ (10 * q.data.length + 26) ≤ G.cap + 1 := pow_le_cap (by have := bg.lin; omega)
  rw [pow_succ] at h8
  omega

/-- **One mask of the query half.** -/
def passQ : S :=
  .seq (maskP (.v 3)) (.seq (.set 4 (.bxor (.v 0) (.v 26)))
    (.seq (subQ false (recE 2) (.k 0) nSE)
    (.seq (subQ true (.sub (recE 11) (pw (recE 1))) (.add nSE (.v 7)) (.add (.mul (.k 2) nSE) (.v 7)))
    (.seq consQ (subQ true (.sub (recE 2) (pw (recE 10))) (.k 0) (.add (.mul (.k 2) nSE) (.v 16)))))))

/-- The variables `passQ` writes. -/
def passQW : List Var := [4] ++ maskW ++ subQW ++ consQW

theorem passQ_spec (q : Request) (hv : q.Valid) (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F0)
    (s : FS) (c : DCtx G q s) (bg : Big G q) (R : List Bool) (i L : ℕ)
    (h0 : s.env 0 = bitsValue R) (hR : R.length + 1 ≤ G.K) (h3 : s.env 3 = i) (hi : i < q.masks.length)
    (h2 : s.env 2 = L) (hL : L ≤ G.N) (h7 : s.env 7 = lenR q) (h16 : s.env 16 = lenR q + lenH q) :
    Em passQW s (evalS G passQ s) ((blkS q φ0 (Request.maskedCoins R q.masks[i])).flatMap (elemW L q.code.f)) := by
  have pc := c.pc
  have db := pc.dbounds
  have hf1 : 1 ≤ q.code.f := pc.f1
  have hlin := bg.lin
  have hcK := cap_ge G
  have hNK := bg.N
  have hel := bg.elems db
  have hel1 : 4 * 2 ^ q.code.f + 2 * lenR q + lenH q + lenI q + 2 ≤ G.cap :=
    le_trans (Nat.le_mul_of_pos_right _ (by have := (fl_bounds c.ok).1; omega)) hel
  have hfD := db.f
  set σ := q.masks[i] with hσ
  set cn := Request.maskedCoins R σ with hcn
  have hσl : σ.length ≤ q.data.length := db.sg σ (List.getElem_mem hi)
  obtain ⟨m26, m27, mw⟩ := maskP_spec G s q pc c.h15 (.v 3) i (by simp [evalE, h3]) hi
  have e0 : Em passQW s (evalS G (maskP (.v 3)) s) [] :=
    (em_of_wr (by decide) mw).mono fun _ hx => List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hx))
  generalize hs1 : evalS G (maskP (.v 3)) s = s1 at m26 m27 mw e0
  set x := bitsValue R ^^^ bitsValue σ with hxd
  have hxK : x < 2 ^ G.K := Nat.xor_lt_two_pow
    (lt_of_lt_of_le (bv_lt R) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (lt_of_lt_of_le (bv_lt σ) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have e4 : evalE G s1 (.bxor (.v 0) (.v 26)) = x := by
    show (s1.env 0 ^^^ s1.env 26) % 2 ^ G.K = x
    rw [mw.env 0 (by decide), h0, m26]; exact Nat.mod_eq_of_lt hxK
  have e1 : Em passQW s (s1.setv 4 x) [] := by simpa using e0.trans (Em.setv s1 (W := passQW) (i := 4) (by decide) x)
  have c1 : DCtx G q (s1.setv 4 x) := c.em e1
  have hx : ∀ j, x / 2 ^ j % 2 = (cn j).toNat := maskedCoins_bits R σ
  have hsub : ∀ y ∈ subQW, y ∈ passQW := fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)
  -- evaluation of the bases at states that keep the globals
  have kE : ∀ (b : FS) (t : FS), DCtx G q b → (∀ j, j ∉ subQW → t.env j = b.env j) → t.fl = b.fl →
      t.env 23 = q.code.f ∧ t.env 7 = b.env 7 ∧ t.env 16 = b.env 16 := fun b t cb ht _ =>
    ⟨(ht 23 (by decide)).trans cb.h23, ht 7 (by decide), ht 16 (by decide)⟩
  have hfK : q.code.f + 1 ≤ G.K := by omega
  have c0 : min 0 G.cap = 0 := Nat.zero_min _
  have c2' : min 2 G.cap = 2 := min_eq_left (by omega)
  -- V_RS on p0
  have rR := subQ_spec (G := G) false (recE 2) (.k 0) nSE q φ0 (s1.setv 4 x) c1 cn x q.dA 0 (2 ^ q.code.f) L 0 []
    (by rw [recE_parse G _ q c1.pc c1.h15 2 (by norm_num)]; rfl) (by simp) hx
    (by rw [e1.env 2 (by decide), h2]) (bg.deg db.f _ db.dA) (fun _ _ _ _ => c0)
    (fun t ht hfl _ => nSE_eval G (kE _ t c1 ht hfl).1 hfK) (le_trans (Nat.mul_le_mul_right _ (by
      show 0 + 2 ^ q.code.f + 2 ^ q.code.f + lenR q + 2 ≤ _; omega)) hel) hL
  generalize hs2 : evalS G (subQ false (recE 2) (.k 0) nSE) (s1.setv 4 x) = s2 at rR
  have e2 : Em passQW s s2 _ := e1.trans (rR.mono hsub)
  have c2 : DCtx G q s2 := c.em e2
  have g7 : s2.env 7 = lenR q := by rw [e2.env 7 (by decide), h7]
  have g4 : s2.env 4 = x := by rw [rR.env 4 (by decide)]; simp
  have g16 : s2.env 16 = lenR q + lenH q := by rw [e2.env 16 (by decide), h16]
  have hmH := db.mH
  -- V_VRS on p1 over H
  have rH := subQ_spec (G := G) true (.sub (recE 11) (pw (recE 1))) (.add nSE (.v 7)) (.add (.mul (.k 2) nSE) (.v 7))
    q φ0 s2 c2 cn x q.dB (2 ^ q.code.f + lenR q) (2 * 2 ^ q.code.f + lenR q) L q.code.hOffset q.code.hBasis
    (eE_sub (recE_parse G s2 q c2.pc c2.h15 11 (by norm_num))
      (eE_pow (recE_parse G s2 q c2.pc c2.h15 1 (by norm_num)) (by show q.code.hBasis.length + 1 ≤ G.K; omega)))
    g4 hx (by rw [e2.env 2 (by decide), h2])
    (bg.deg db.f _ (lt_of_le_of_lt (Nat.sub_le _ _) db.dB))
    (fun t ht hfl _ => by
      obtain ⟨t23, t7, -⟩ := kE _ t c2 ht hfl
      exact eE_add (nSE_eval G t23 hfK) (eE_v 7 |>.trans (t7.trans g7)) (by omega))
    (fun t ht hfl _ => by
      obtain ⟨t23, t7, -⟩ := kE _ t c2 ht hfl
      exact eE_add (eE_mul (eE_k (by omega)) (nSE_eval G t23 hfK) (by omega)) (eE_v 7 |>.trans (t7.trans g7))
        (by omega))
    (le_trans (Nat.mul_le_mul_right _ (by
      show 2 ^ q.code.f + lenR q + 2 ^ q.code.f + (2 * 2 ^ q.code.f + lenR q) + lenH q + 2 ≤ _; omega)) hel) hL
  generalize hs3 : evalS G (subQ true (.sub (recE 11) (pw (recE 1))) (.add nSE (.v 7)) (.add (.mul (.k 2) nSE) (.v 7)))
    s2 = s3 at rH
  have e3 : Em passQW s s3 _ := e2.trans (rH.mono hsub)
  have c3 : DCtx G q s3 := c.em e3
  have g4' : s3.env 4 = x := by rw [rH.env 4 (by decide), g4]
  -- the consistency test
  have rC := consQ_spec (G := G) q hv φ0 s3 c3 cn x L g4' hx
    (by rw [e3.env 7 (by decide), h7]) (by rw [e3.env 2 (by decide), h2]) hL
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hel) (by have := db.cN; omega)
    (le_trans (Nat.mul_le_mul (show q.code.cN ≤ q.data.length + 1 by have := db.cN; omega)
      (show q.code.f ≤ q.data.length + 1 by omega)) (by
        have := bg.cube (q.data.length + 1) (q.data.length + 1) 1 le_rfl le_rfl (by omega); simp at this; omega))
  generalize hs4 : evalS G consQ s3 = s4 at rC
  have e4' : Em passQW s s4 _ := e3.trans (rC.mono fun _ hx => List.mem_append_right _ hx)
  have c4 : DCtx G q s4 := c.em e4'
  have g4'' : s4.env 4 = x := by rw [rC.env 4 (by decide), g4']
  have hiw : (iBw q).length = q.mI := pc.iBw_len
  have hmI := db.mI
  -- V_VRS on p0 − p_x over I
  have rI := subQ_spec (G := G) true (.sub (recE 2) (pw (recE 10))) (.k 0) (.add (.mul (.k 2) nSE) (.v 16)) q φ0 s4 c4
    cn x q.dA 0 (2 * 2 ^ q.code.f + lenR q + lenH q) L (iOw q) (iBw q)
    (by rw [eE_sub (recE_parse G s4 q c4.pc c4.h15 2 (by norm_num))
          (eE_pow (recE_parse G s4 q c4.pc c4.h15 10 (by norm_num)) (by show q.mI + 1 ≤ G.K; omega)), hiw]; rfl)
    g4'' hx (by rw [e4'.env 2 (by decide), h2])
    (bg.deg db.f _ (lt_of_le_of_lt (Nat.sub_le _ _) db.dA)) (fun _ _ _ _ => c0)
    (fun t ht hfl _ => by
      obtain ⟨t23, -, t16⟩ := kE _ t c4 ht hfl
      have e16 : evalE G t (.v 16) = lenR q + lenH q := eE_v 16 |>.trans (t16.trans (by rw [e4'.env 16 (by decide), h16]))
      have := eE_add (eE_mul (eE_k (show 2 ≤ G.cap by omega)) (nSE_eval G t23 hfK) (by omega)) e16
        (show 2 * 2 ^ q.code.f + (lenR q + lenH q) ≤ G.cap by omega)
      rw [this]; ring)
    (le_trans (Nat.mul_le_mul_right _ (by
      show 0 + 2 ^ q.code.f + (2 * 2 ^ q.code.f + lenR q + lenH q) + lenI q + 2 ≤ _; omega)) hel) hL
  generalize hs5 : evalS G (subQ true (.sub (recE 2) (pw (recE 10))) (.k 0) (.add (.mul (.k 2) nSE) (.v 16))) s4 = s5
    at rI
  have ht : evalS G passQ s = s5 := by
    show evalS G (.seq _ _) s = _
    simp only [evalS_seq]
    rw [hs1, evalS_set, e4, hs2, hs3, hs4, hs5]
  rw [ht]
  have := e4'.trans (rI.mono hsub)
  convert this using 1
  simp only [blkS, List.flatMap_append, List.append_assoc, List.nil_append, blkX_false]
  rfl

end NearCubicGates.Adapters.ShortPCP.Machines.FL
