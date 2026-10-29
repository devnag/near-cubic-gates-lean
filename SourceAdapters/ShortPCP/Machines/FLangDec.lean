import SourceAdapters.ShortPCP.Machines.FLangSub

/-!
# Single-run time, machine layer 30: the consistency test and one mask of the decision half

proof of `thm:short-pcp-ours` (Step 4 of Construction 8.5: the consistency test at the point given by the first `f` coins) and
proof of `thm:short-pcp-ours` (`V1` runs `V0` on `R ⊕ σ`): `consD` reads the answers `p0(N_i(α))`, `p1(α)` from the answer bits
(`cqP` computes `α` and the neighbours, and `cdP` computes the test; both are defined in `FLangCircCons.lean`)
and multiplies the verdict; `passD` runs, for one
mask `σ`, the coins `R ⊕ σ`, then `V_RS` on `p0`, `V_VRS` on `p1`, the consistency test, and `V_VRS` on `p0 − p_x`,
and multiplies the verdict `2` by `runVerdictN` (`passD_spec`), given that the answer blocks of this mask are the
blocks `blkS` lists.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)
open NearCubicGates.Adapters.ShortPCP (consist)
open NearCubicGates.Adapters.Joins (listWord)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (frame)

variable {G : Glob}

/-! ## The consistency test -/

/-- The word of answer block `3 + e`. -/
def blkWE (e : E) : E := .md (.shr (.v 16) (.mul (.add (.v 3) e) (.v 23))) nSE

/-- **The consistency test of the decision half**: coins `42 := 4`, `α` and the neighbours (`cqP`), the answers of
blocks `3 .. 3 + cN` into `37` and `22`, the test (`cdP`), `2 := 2 · 24`. -/
def consD : S :=
  .seq (.set 42 (.v 4)) (.seq cqP (.seq (.set 40 (recE 5))
    (.seq (genP 40 38 41 39 23 (.set 41 (blkWE (.v 38))))
    (.seq (.set 37 (.v 39)) (.seq (.set 22 (blkWE (.v 40)))
    (.seq (.set 3 (.add (.add (.v 3) (.v 40)) (.k 1))) (.seq cdP (.set 2 (.mul (.v 2) (.v 24))))))))))

/-- The variables `consD` writes. -/
def consW : List Var := [2, 3, 22, 37, 38, 39, 40, 41, 42] ++ cqW ++ cdW

theorem mul_le_one' {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  have := Nat.mul_le_mul ha hb; simpa using this

theorem blkWE_eval {s : FS} {e : E} {f W b0 j : ℕ} (h16 : s.env 16 = W) (h3 : s.env 3 = b0) (h23 : s.env 23 = f)
    (he : evalE G s e = j) (hK : f + 1 ≤ G.K) (hb : (b0 + j) * f ≤ G.cap) (hj : b0 + j ≤ G.cap) :
    evalE G s (blkWE e) = W / 2 ^ ((b0 + j) * f) % 2 ^ f :=
  eE_md (eE_shr (eE_v 16 |>.trans h16) (eE_mul (eE_add (eE_v 3 |>.trans h3) he hj) (eE_v 23 |>.trans h23) hb))
    (nSE_eval G h23 hK)

variable {F : Type} [Field F] [DecidableEq F]

/-- **The consistency test** (proof of `thm:short-pcp-ours`): the verdict is multiplied by `consist` of the join's instance at the
point of the coins, on the tables the oracle encodes, given that blocks `b0 .. b0 + cN − 1` are `p0` at the
neighbours and block `b0 + cN` is `p1` at `α`. -/
theorem consD_spec (q : Request) (hv : q.Valid) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (hφ : Function.Bijective φ) (s : FS) (c : DCtx G q s) (o cn : ℕ → Bool) (x b0 W : ℕ)
    (h4 : s.env 4 = x) (hx : ∀ i, x / 2 ^ i % 2 = (cn i).toNat)
    (h16 : s.env 16 = W) (h3 : s.env 3 = b0) (h2 : s.env 2 ≤ 1)
    (hbK : (b0 + q.code.cN + 2) * q.code.f + 1 ≤ G.K)
    (hWn : ∀ i < q.code.cN, W / 2 ^ ((b0 + i) * q.code.f) % 2 ^ q.code.f =
      q.wordAt o (nbW q q.code.irr (x % 2 ^ q.code.f) i))
    (hWp : W / 2 ^ ((b0 + q.code.cN) * q.code.f) % 2 ^ q.code.f =
      q.wordAt o (2 ^ q.code.f + lenR q + x % 2 ^ q.code.f)) :
    let t := evalS G consD s
    t.env 2 = s.env 2 * (if consist (q.acsp φ) (fun a => q.elt φ (q.wordAt o (q.wordOf φ a)))
        (fun a => q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ a))) (q.consistPoint φ cn) then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ t.env 3 = b0 + q.code.cN + 1 ∧ Wr consW s t := by
  intro t
  obtain ⟨env, out, fl, fp, ip, bad⟩ := s
  obtain rfl : fl = q.code.f := c.fl
  obtain rfl : fp = q.code.irr := c.fp
  set s : FS := ⟨env, out, q.code.f, q.code.irr, ip, bad⟩ with hs
  have hmod : GF.ModulusOk q.code.irr q.code.f := (fl_bounds c.ok).2.2.1
  have hf1 : 1 ≤ q.code.f := (fl_bounds c.ok).1
  have hcK := cap_ge G
  have hKf : 2 * ((q.code.f + 1) * (8 * q.code.f + 16)) + 1 ≤ G.K := c.K
  have hNf := c.N
  have hpc := c.pc
  have hcN : q.code.cN + 1 ≤ q.data.length := by
    obtain ⟨-, -, l5⟩ := hpc.piece 4 (listWord Instance.pairWord q.code.nbr)
      (by norm_num) rfl
    have := count_le Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x) _ _ l5
    unfold Instance.cN; omega
  have hNd := hpc.N
  set a := x % 2 ^ q.code.f with ha
  have hal : a < 2 ^ q.code.f := Nat.mod_lt _ (by positivity)
  -- 42 := 4; cqP
  have c1 : DCtx G q (s.setv 42 x) := c.setv 42 x
  obtain ⟨k36, k37, kw⟩ := cqP_spec G (s.setv 42 x) φ q c1.pc c1.h15 c1.h23 rfl c.ok
  simp only [FS.setv_env, Function.update_self] at k36 k37
  generalize hs2 : evalS G cqP (s.setv 42 x) = s2 at k36 k37 kw
  have w2 : Wr consW s s2 := (Wr.setv _ (by decide) _).trans (kw.mono (by decide))
  have c2 : DCtx G q s2 := c.wr w2
  have e16 : s2.env 16 = W := by rw [w2.env 16 (by decide), h16]
  have e3 : s2.env 3 = b0 := by rw [kw.env 3 (by decide)]; simp [h3]
  have e2 : s2.env 2 = s.env 2 := by rw [kw.env 2 (by decide)]; simp
  have hfK : q.code.f + 2 ≤ G.K := (fl_bounds c.ok).2.1
  -- 40 := cN; the answers of the neighbours
  have e40 : evalE G s2 (recE 5) = q.code.cN := recE_parse G s2 q c2.pc c2.h15 5 (by norm_num)
  set s3 := s2.setv 40 q.code.cN with hs3
  have hpw : ∀ j ≤ q.code.cN, (b0 + j) * q.code.f ≤ G.cap ∧ b0 + j ≤ G.cap := by
    intro j hj
    have : (b0 + j) * q.code.f ≤ (b0 + q.code.cN + 2) * q.code.f := Nat.mul_le_mul_right _ (by omega)
    have : b0 + j ≤ (b0 + j) * q.code.f := Nat.le_mul_of_pos_right _ hf1
    omega
  obtain ⟨g39, gw⟩ := genP_spec G 40 38 41 39 23 (.set 41 (blkWE (.v 38))) [41] s3 q.code.cN q.code.f
    (fun j => W / 2 ^ ((b0 + j) * q.code.f) % 2 ^ q.code.f)
    (by simp only [s3, FS.setv_env, Function.update_self]; omega) (by simp [s3, c2.h23])
    (by have : q.code.f * q.code.cN ≤ (b0 + q.code.cN + 2) * q.code.f := by
          rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
        omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj t' w' h38
      have hb := hpw j hj.le
      refine ⟨?_, Nat.mod_lt _ (by positivity), Wr.setv _ (by simp) _⟩
      simp only [evalS_set, FS.setv_env, Function.update_self]
      exact blkWE_eval (by rw [w'.env 16 (by decide)]; simp [s3, e16]) (by rw [w'.env 3 (by decide)]; simp [s3, e3])
        (by rw [w'.env 23 (by decide)]; simp [s3, c2.h23]) (eE_v 38 |>.trans h38) (by omega) hb.1 hb.2)
  generalize hs4 : evalS G (genP 40 38 41 39 23 (.set 41 (blkWE (.v 38)))) s3 = s4 at g39 gw
  have w4 : Wr consW s s4 := (w2.trans (Wr.setv _ (by decide) _)).trans (gw.mono (by decide))
  obtain ⟨env4, out4, fl4, fp4, ip4, bad4⟩ := s4
  obtain rfl : fp4 = q.code.irr := w4.fp
  obtain rfl : fl4 = q.code.f := w4.fl
  set s4 : FS := ⟨env4, out4, q.code.f, q.code.irr, ip4, bad4⟩ with hs4d
  have c4 : DCtx G q s4 := c.wr w4
  have f16 : s4.env 16 = W := by rw [gw.env 16 (by decide)]; simp [s3, e16]
  have f3 : s4.env 3 = b0 := by rw [gw.env 3 (by decide)]; simp [s3, e3]
  have f40 : s4.env 40 = q.code.cN := by rw [gw.env 40 (by decide)]; simp [s3]
  have f36 : s4.env 36 = a := by
    rw [gw.env 36 (by decide)]; simp only [s3, FS.setv_env, Function.update_of_ne (by decide : (36 : Var) ≠ 40)]
    rw [k36]
  have f2 : s4.env 2 = s.env 2 := by rw [gw.env 2 (by decide)]; simp [s3, e2]
  -- 37, 22, 3
  set ys := (List.range q.code.cN).map (fun j => W / 2 ^ ((b0 + j) * q.code.f) % 2 ^ q.code.f) with hys
  have e22 : evalE G (s4.setv 37 (packW q.code.f ys)) (blkWE (.v 40)) = W / 2 ^ ((b0 + q.code.cN) * q.code.f) % 2 ^ q.code.f :=
    blkWE_eval (by simp [f16]) (by simp [f3]) (by simp [c4.h23]) (by simp [evalE, f40]) (by omega)
      (hpw _ le_rfl).1 (hpw _ le_rfl).2
  set w22 := W / 2 ^ ((b0 + q.code.cN) * q.code.f) % 2 ^ q.code.f with hw22
  set s5 := (s4.setv 37 (packW q.code.f ys)).setv 22 w22 with hs5
  have e3' : evalE G s5 (.add (.add (.v 3) (.v 40)) (.k 1)) = b0 + q.code.cN + 1 :=
    eE_add (eE_add (by simp [s5, evalE, f3]) (by simp [s5, evalE, f40]) (hpw _ le_rfl).2) (eE_k (by omega))
      (by have := (hpw _ le_rfl).1; have : b0 + q.code.cN + 1 ≤ (b0 + q.code.cN + 2) * q.code.f :=
            le_trans (by omega) (Nat.le_mul_of_pos_right _ hf1)
          omega)
  set s6 := s5.setv 3 (b0 + q.code.cN + 1) with hs6
  have w6 : Wr consW s s6 :=
    ((w4.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
  have c6 : DCtx G q s6 := c.wr w6
  have hysl : ∀ b ∈ ys, b < 2 ^ q.code.f := by
    intro b hb; simp only [ys, List.mem_map] at hb; obtain ⟨j, -, rfl⟩ := hb; exact Nat.mod_lt _ (by positivity)
  have hyl : ys.length = q.code.cN := by simp [ys]
  have g36 : s6.env 36 = a := by simp [s6, s5, f36]
  have g22 : s6.env 22 = w22 := by simp [s6, s5]
  obtain ⟨d24, dw⟩ := cdP_spec G s6 φ q c6.pc c6.h15 c6.h23 rfl c.ok c.irr ys hysl hyl (by simp [s6, s5])
    (by rw [g36]; exact hal) (by rw [g22]; exact Nat.mod_lt _ (by positivity))
  rw [g36, g22] at d24
  generalize hs7 : evalS G cdP s6 = s7 at d24 dw
  have w7 : Wr consW s s7 := w6.trans (dw.mono (by decide))
  have f2' : s7.env 2 = s.env 2 := by rw [dw.env 2 (by decide)]; simp [s6, s5, f2]
  -- the math
  have hp0 : ∀ i : Fin q.code.cN, ev φ (ys.getD i.val 0) =
      (fun a => q.elt φ (q.wordAt o (q.wordOf φ a))) ((q.acsp φ).nbr i (ev φ a)) := by
    intro i
    obtain ⟨nlt, nev⟩ := nbW_spec q φ hmod hv.1 a i.val hal
    rw [nbr_eq q φ i a, ← nev]
    simp only [ys, List.getD_eq_getElem _ _ (by simp : i.val < ((List.range q.code.cN).map _).length),
      List.getElem_map, List.getElem_range]
    rw [hWn i.val i.isLt]
    show q.elt φ _ = q.elt φ (q.wordAt o (q.wordOf φ (q.elt φ _)))
    rw [wordOf_elt q φ hφ hmod _ nlt]
  have hp1 : ev φ w22 = (fun a => q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ a))) (ev φ a) := by
    rw [hWp]
    show q.elt φ _ = q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ (q.elt φ a)))
    rw [wordOf_elt q φ hφ hmod _ hal]
  have hcs := consist_eq q φ (fun a => q.elt φ (q.wordAt o (q.wordOf φ a)))
    (fun a => q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ a))) a w22 ys hyl hp0 hp1
  have hcp : q.consistPoint φ cn = ev φ a := consistPoint_eq q φ cn x (fun i _ => hx i)
  have ht : t = evalS G (.set 2 (.mul (.v 2) (.v 24))) (evalS G cdP (evalS G (.set 3 (.add (.add (.v 3) (.v 40))
      (.k 1))) (evalS G (.set 22 (blkWE (.v 40))) (evalS G (.set 37 (.v 39)) (evalS G (genP 40 38 41 39 23
      (.set 41 (blkWE (.v 38)))) (evalS G (.set 40 (recE 5)) (evalS G cqP (evalS G (.set 42 (.v 4)) s)))))))) := rfl
  have q42 : evalS G (.set 42 (.v 4)) s = s.setv 42 x := by rw [evalS_set, eE_v, h4]
  have q40 : evalS G (.set 40 (recE 5)) s2 = s3 := by rw [evalS_set, e40]
  have q37 : evalS G (.set 37 (.v 39)) s4 = s4.setv 37 (packW q.code.f ys) := by rw [evalS_set, eE_v, g39]
  have q22 : evalS G (.set 22 (blkWE (.v 40))) (s4.setv 37 (packW q.code.f ys)) = s5 := by rw [evalS_set, e22]
  have q3 : evalS G (.set 3 (.add (.add (.v 3) (.v 40)) (.k 1))) s5 = s6 := by rw [evalS_set, e3']
  rw [q42, hs2, q40, hs4, q37, q22, q3, hs7] at ht
  have h24 : s7.env 24 ≤ 1 := by rw [d24]; split_ifs <;> omega
  have hs22 : s7.env 2 ≤ 1 := by rw [f2']; exact h2
  have e2m : evalE G s7 (.mul (.v 2) (.v 24)) = s7.env 2 * s7.env 24 :=
    eE_mul rfl rfl (by have : s7.env 2 * s7.env 24 ≤ 1 := mul_le_one' hs22 h24; omega)
  rw [ht, evalS_set, e2m]
  refine ⟨?_, ?_, ?_, w7.trans (Wr.setv _ (by decide) _)⟩
  · simp only [FS.setv_env, Function.update_self]
    rw [f2', d24, hcp, hcs]
    simp only [decide_eq_true_eq]
    rfl
  · simp only [FS.setv_env, Function.update_self]; exact mul_le_one' hs22 h24
  · simp only [FS.setv_env, Function.update_of_ne (by decide : (3 : Var) ≠ 2)]
    rw [dw.env 3 (by decide)]; simp [s6]

/-! ## Sizes the data word bounds -/

theorem length_le_flatten_of_mem {α : Type} (g : α → List Bool) :
    ∀ (L : List α) (x : α), x ∈ L → (g x).length ≤ (L.map g).flatten.length
  | [], x, h => by simp at h
  | y :: L, x, h => by
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := length_le_flatten_of_mem g L x h; omega

/-- What the data word bounds. -/
structure DBounds (q : Request) : Prop where
  dB : q.dB < 2 ^ q.data.length
  dA : q.dA < 2 ^ q.data.length
  cN : q.code.cN + 1 ≤ q.data.length
  nm : q.masks.length + 1 ≤ q.data.length
  mH : q.code.hBasis.length + 1 ≤ q.data.length
  sg : ∀ σ ∈ q.masks, σ.length ≤ q.data.length
  mI : q.mI + 1 ≤ q.data.length
  f : q.code.f + 1 ≤ q.data.length

theorem PCtx.dbounds {q : Request} {D : ℕ} (c : PCtx G q D) : DBounds q := by
  obtain ⟨-, -, l3⟩ := c.piece 2 (listWord natWord q.code.hBasis) (by norm_num) rfl
  obtain ⟨-, -, l5⟩ := c.piece 4 (listWord Instance.pairWord q.code.nbr)
    (by norm_num) rfl
  obtain ⟨-, -, l10⟩ := c.piece 9 (natWord q.dB) (by norm_num) rfl
  obtain ⟨-, -, l11⟩ := c.piece 10 (listWord frame q.masks) (by norm_num) rfl
  have hmH := count_le natWord q.code.hBasis (fun x _ => natWord_pos x) _ _ l3
  have hcN := count_le Instance.pairWord q.code.nbr (fun x _ => pairWord_pos x) _ _ l5
  have hnm := count_le frame q.masks (fun x _ => frame_pos x) _ _ l11
  have hdB := NearCubicGates.Close.Cells.lt_natBitLength q.dB
  have hnb := natBitLength_le_len q.dB
  refine ⟨lt_of_lt_of_le hdB (Nat.pow_le_pow_right (by norm_num) (by omega)), ?_, by unfold Instance.cN; omega,
    hnm, hmH, ?_, c.mI_le, c.f_lt⟩
  · unfold Request.dA
    have : 2 ^ q.code.hBasis.length ≤ 2 ^ q.data.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 1 ≤ 2 ^ q.code.hBasis.length := Nat.one_le_two_pow
    omega
  · intro σ hσ
    have h1 := length_le_flatten_of_mem frame q.masks σ hσ
    rw [listWord_eq, List.length_append] at l11
    rw [frame_len] at h1
    omega

/-- The numeric size of the run (the clamp and the pass bound are large). -/
structure Big (G : Glob) (q : Request) : Prop where
  K : 2048 * (q.data.length + 1) ^ 3 ≤ G.K
  N : G.K ≤ G.N

theorem Big.cube {q : Request} (bg : Big G q) (a b c : ℕ) (ha : a ≤ q.data.length + 1) (hb : b ≤ q.data.length + 1)
    (hc : c ≤ q.data.length + 1) : 2048 * (a * b * c) ≤ G.K := by
  have : a * b * c ≤ (q.data.length + 1) ^ 3 := by
    rw [pow_three, ← mul_assoc]; exact Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  have := bg.K; omega

theorem Big.lin {q : Request} (bg : Big G q) : 2048 * (q.data.length + 1) ≤ G.K := by
  have := bg.cube 1 1 (q.data.length + 1) (by omega) (by omega) le_rfl; simpa using this

/-- The degree bound of a run: `(d + 5)·2^(8f+20)` below the clamp for `d < 2^|data|`. -/
theorem Big.deg {q : Request} (bg : Big G q) (hf : q.code.f + 1 ≤ q.data.length) (d : ℕ) (hd : d < 2 ^ q.data.length) :
    (d + 5) * 2 ^ (8 * q.code.f + 20) ≤ G.cap := by
  have hl := bg.lin
  have h1 : d + 5 ≤ 2 ^ (q.data.length + 3) := by
    rw [pow_add]; have : 1 ≤ 2 ^ q.data.length := Nat.one_le_two_pow; omega
  have h2 : 2 ^ (q.data.length + 3) * 2 ^ (8 * q.code.f + 20) ≤ 2 ^ (9 * q.data.length + 23) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (9 * q.data.length + 24) ≤ G.cap + 1 := pow_le_cap (by omega)
  rw [pow_succ] at h3
  calc (d + 5) * 2 ^ (8 * q.code.f + 20) ≤ 2 ^ (q.data.length + 3) * 2 ^ (8 * q.code.f + 20) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ _ := by omega

theorem nT_le {q : Request} (db : DBounds q) : nT q ≤ q.data.length + 310 := by
  have := qcO_le false q.code.f q.dA; have := qcO_le true q.code.f (dH q); have := qcO_le true q.code.f (dI q)
  unfold nT qcR qcH qcIo; have := db.cN; omega

/-- The block positions and the field width fit the clamp. -/
theorem Big.blk {q : Request} (bg : Big G q) (db : DBounds q) (i : ℕ) (hi : i < q.masks.length) :
    (i * nT q + nT q + 105) * q.code.f + 1 ≤ G.K := by
  have hnT := nT_le db
  have hnm := db.nm
  have hfd := db.f
  set D := q.data.length + 1 with hD
  have a1 : (i + 1) * nT q ≤ D * (311 * D) := Nat.mul_le_mul (by omega) (by omega)
  have a2 : 1 ≤ D * D := Nat.mul_le_mul (show 1 ≤ D by omega) (show 1 ≤ D by omega)
  have e1 : D * (311 * D) = 311 * (D * D) := by ring
  have e2 : i * nT q + nT q = (i + 1) * nT q := by ring
  have a3 : (i * nT q + nT q + 105) * q.code.f ≤ (416 * (D * D)) * D :=
    Nat.mul_le_mul (by omega) (by omega)
  have a4 := bg.cube D D D le_rfl le_rfl le_rfl
  have e3 : 416 * (D * D) * D = 416 * (D * D * D) := by ring
  have a5 : 1 ≤ D * D * D := Nat.mul_le_mul a2 (show 1 ≤ D by omega)
  omega

/-! ## One mask -/

/-- `V_RS` on `p0` (degree `d_A`). -/
def subR : S := subD false none (recE 2) (.k 0) (.k 0) (.k 0)
/-- `V_VRS` on `p1` over `H` (degree `d_B`). -/
def subH : S := subD true none (.sub (recE 11) (pw (recE 1))) (recE 3) (recE 1) (recE 4)
/-- `V_VRS` on `p0 − p_x` over `I` (degree `d_A`). -/
def subI : S := subD true (some pxP) (.sub (recE 2) (pw (recE 10))) (recE 14) (recE 10) (recE 15)

/-- **One mask of the decision half**: `σ` (`maskP`), the coin number `4 := R ⊕ σ`, then the four steps. -/
def passD : S :=
  .seq (maskP (.v 1)) (.seq (.set 4 (.bxor (.v 0) (.v 26))) (.seq subR (.seq subH (.seq consD subI))))

/-- The variables `passD` writes. -/
def passW : List Var := [4] ++ maskW ++ subW ++ consW

theorem ite_and_mul (a b : Bool) : (if (a && b) = true then 1 else 0) = (if a = true then 1 else 0) * (if b = true then 1 else 0) := by
  cases a <;> cases b <;> rfl

theorem getD_app_left (A B : List ℕ) (j : ℕ) (h : j < A.length) : (A ++ B).getD j 0 = A.getD j 0 :=
  List.getD_append _ _ _ _ h

theorem getD_app_right (A B : List ℕ) (j : ℕ) : (A ++ B).getD (A.length + j) 0 = B.getD j 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]; congr 1; omega

theorem getD_app3 (A B C : List ℕ) (j : ℕ) : (A ++ B ++ C).getD (A.length + B.length + j) 0 = C.getD j 0 := by
  rw [show A.length + B.length + j = (A ++ B).length + j by simp, getD_app_right]

section BlocksOfMask

variable {F0 : Type} [Field F0] [DecidableEq F0] (q : Request) (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F0)
  (cn : ℕ → Bool)

theorem lA_eq : (blkX false (q.domBasis φ0) [] 0 q.dA (lenR q) 0 (2 ^ q.code.f)
    ((List.range (randR q)).map cn)).length = qcR q := by rw [blkX_length, domBasis_length]; rfl

theorem lB_eq : (blkX true (q.domBasis φ0) (q.hB φ0) (q.hO φ0) q.dB (lenH q) (2 ^ q.code.f + lenR q)
    (2 * 2 ^ q.code.f + lenR q) ((List.range (randH q)).map cn)).length = qcH q := by
  rw [blkX_length, domBasis_length]; simp [Request.hB, qcH, dH]

theorem lC_eq : (blkC q cn).length = q.code.cN + 1 := by simp [blkC]

theorem lD_eq : (blkX true (q.domBasis φ0) (q.iB φ0) (q.iO φ0) q.dA (lenI q) 0 (2 * 2 ^ q.code.f + lenR q + lenH q)
    ((List.range (randI q)).map cn)).length = qcIo q := by
  rw [blkX_length, domBasis_length]; simp [Request.iB, qcIo, dI, iBw]

theorem blkS_R (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ qcO false q.code.f (innD false ([] : List ℕ).length q.dA)) :
    (blkS q φ0 cn).getD (k - 1) 0 = elemOf ((outV false (q.domBasis φ0) 0 (([] : List ℕ).map (q.elt φ0)) (q.elt φ0 0)
      q.dA).Q ((List.range (outRand false q.code.f (innD false ([] : List ℕ).length q.dA))).map cn)
      (idxO q.code.f (innD false ([] : List ℕ).length q.dA) k)) (2 ^ q.code.f)
      (outLen false q.code.f (innD false ([] : List ℕ).length q.dA)) 0 (2 ^ q.code.f) := by
  have hk' : k ≤ qcR q := hk
  have lA := lA_eq q φ0 cn; have lB := lB_eq q φ0 cn; have lC := lC_eq q cn
  unfold blkS
  rw [getD_app_left _ _ _ (by simp only [List.length_append, lA, lB, lC]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, lA, lB]; omega),
    getD_app_left _ _ _ (by rw [lA]; omega),
    blkX_getD _ _ _ _ _ _ _ _ _ _ hk1 (by rw [domBasis_length]; exact hk)]
  simp only [domBasis_length]; rfl

theorem blkS_H (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ qcO true q.code.f (innD true q.code.hBasis.length q.dB)) :
    (blkS q φ0 cn).getD (qcR q + (k - 1)) 0 = elemOf ((outV true (q.domBasis φ0) 0 (q.code.hBasis.map (q.elt φ0))
      (q.elt φ0 q.code.hOffset) q.dB).Q ((List.range (outRand true q.code.f (innD true q.code.hBasis.length q.dB))).map cn)
      (idxO q.code.f (innD true q.code.hBasis.length q.dB) k)) (2 ^ q.code.f)
      (outLen true q.code.f (innD true q.code.hBasis.length q.dB)) (2 ^ q.code.f + lenR q)
      (2 * 2 ^ q.code.f + lenR q) := by
  have hk' : k ≤ qcH q := hk
  have lA := lA_eq q φ0 cn; have lB := lB_eq q φ0 cn; have lC := lC_eq q cn
  unfold blkS
  rw [getD_app_left _ _ _ (by simp only [List.length_append, lA, lB, lC]; omega),
    getD_app_left _ _ _ (by simp only [List.length_append, lA, lB]; omega), ← lA, getD_app_right,
    blkX_getD _ _ _ _ _ _ _ _ _ _ hk1 (by rw [domBasis_length]; simpa [Request.hB] using hk)]
  simp only [domBasis_length, Request.hB, List.length_map]; rfl

theorem blkS_N (x j : ℕ) (hal : alphaW q cn = x % 2 ^ q.code.f) (hj : j < q.code.cN) :
    (blkS q φ0 cn).getD (qcR q + qcH q + j) 0 = nbW q q.code.irr (x % 2 ^ q.code.f) j := by
  have lA := lA_eq q φ0 cn; have lB := lB_eq q φ0 cn; have lC := lC_eq q cn
  unfold blkS
  rw [getD_app_left _ _ _ (by simp only [List.length_append, lA, lB, lC]; omega), ← lA, ← lB, getD_app3, blkC,
    getD_app_left _ _ _ (by simp only [List.length_map, List.length_range]; exact hj),
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj)]
  simp [hal]

theorem blkS_P (x : ℕ) (hal : alphaW q cn = x % 2 ^ q.code.f) :
    (blkS q φ0 cn).getD (qcR q + qcH q + q.code.cN) 0 = 2 ^ q.code.f + lenR q + x % 2 ^ q.code.f := by
  have lA := lA_eq q φ0 cn; have lB := lB_eq q φ0 cn; have lC := lC_eq q cn
  unfold blkS
  rw [getD_app_left _ _ _ (by simp only [List.length_append, lA, lB, lC]; omega), ← lA, ← lB, getD_app3, blkC]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [hal]

theorem blkS_I (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ qcO true q.code.f (innD true (iBw q).length q.dA)) :
    (blkS q φ0 cn).getD (qcR q + qcH q + (q.code.cN + 1) + (k - 1)) 0 = elemOf ((outV true (q.domBasis φ0) 0
      ((iBw q).map (q.elt φ0)) (q.elt φ0 (iOw q)) q.dA).Q
      ((List.range (outRand true q.code.f (innD true (iBw q).length q.dA))).map cn)
      (idxO q.code.f (innD true (iBw q).length q.dA) k)) (2 ^ q.code.f)
      (outLen true q.code.f (innD true (iBw q).length q.dA)) 0 (2 * 2 ^ q.code.f + lenR q + lenH q) := by
  have lA := lA_eq q φ0 cn; have lB := lB_eq q φ0 cn; have lC := lC_eq q cn
  have lC' : (blkX false (q.domBasis φ0) [] 0 q.dA (lenR q) 0 (2 ^ q.code.f) ((List.range (randR q)).map cn) ++
      blkX true (q.domBasis φ0) (q.hB φ0) (q.hO φ0) q.dB (lenH q) (2 ^ q.code.f + lenR q) (2 * 2 ^ q.code.f + lenR q)
        ((List.range (randH q)).map cn) ++ blkC q cn).length = qcR q + qcH q + (q.code.cN + 1) := by
    simp only [List.length_append, lA, lB, lC]
  unfold blkS
  rw [← lC', getD_app_right, blkX_getD _ _ _ _ _ _ _ _ _ _ hk1 (by rw [domBasis_length]; simpa [Request.iB, iBw] using hk)]
  simp only [domBasis_length, Request.iB, List.length_map]; rfl

end BlocksOfMask

variable {F : Type} [Field F] [DecidableEq F]

/-- `V0` on coins `cn` in the forms the machine specs produce. -/
theorem runVerdictN_parts (q : Request) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F) (o cn : ℕ → Bool) :
    runVerdictN q φ o cn =
      (acceptsN (outV false (q.domBasis φ) 0 (([] : List ℕ).map (q.elt φ)) (q.elt φ 0) q.dA) (q.domBasis φ) 0
        (fun a => q.elt φ (q.wordAt o (0 + q.wordOf φ a)) + (fun _ => (0 : F)) a)
        (fun t => q.elt φ (q.wordAt o (2 ^ q.code.f + t))) cn &&
      acceptsN (outV true (q.domBasis φ) 0 (q.code.hBasis.map (q.elt φ)) (q.elt φ q.code.hOffset) q.dB)
        (q.domBasis φ) 0 (fun a => q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ a)) + (fun _ => (0 : F)) a)
        (fun t => q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + lenR q + t))) cn &&
      consist (q.acsp φ) (fun a => q.elt φ (q.wordAt o (q.wordOf φ a)))
        (fun a => q.elt φ (q.wordAt o (2 ^ q.code.f + lenR q + q.wordOf φ a))) (q.consistPoint φ cn) &&
      acceptsN (outV true (q.domBasis φ) 0 ((iBw q).map (q.elt φ)) (q.elt φ (iOw q)) q.dA)
        (q.domBasis φ) 0 (fun a => q.elt φ (q.wordAt o (0 + q.wordOf φ a)) + pxN q φ a)
        (fun t => q.elt φ (q.wordAt o (2 * 2 ^ q.code.f + lenR q + lenH q + t))) cn) := by
  haveI := charP_two q φ
  have hLR : (vRSF (q.domBasis φ) 0 q.dA).length = lenR q := by
    rw [(vRSF_params _ _ _).2.1, domBasis_length]; simp [lenR, outLen]
  have hLH : (vVRSF (q.domBasis φ) 0 (q.hB φ) (q.hO φ) q.dB).length = lenH q := by
    have := (outV_params true (q.domBasis φ) 0 (q.hB φ) (q.hO φ) q.dB).1
    simp only [outV, if_true] at this
    rw [this, domBasis_length]; simp [lenH, dH, Request.hB]
  have e : (fun a => q.elt φ (q.wordAt o (0 + q.wordOf φ a)) + pxN q φ a) =
      (fun a => q.elt φ (q.wordAt o (q.wordOf φ a)) - pxN q φ a) := by
    funext a; rw [zero_add, CharTwo.sub_eq_add]
  rw [e]
  unfold runVerdictN
  simp only [hLR, hLH, outV, Bool.false_eq_true, if_false, if_true, zero_add, add_zero, List.map_nil]
  rfl

/-- **One mask** (proof of `thm:short-pcp-ours`): the verdict `2` is multiplied by `runVerdictN` on the coins `R ⊕ σ`
for `σ = masks[i]`, given that the answer blocks `i·T, …, i·T + T − 1` are `blkS` of these coins. -/
theorem passD_spec (q : Request) (hv : q.Valid) (φ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (hφ : Function.Bijective φ) {F0 : Type} [Field F0] [DecidableEq F0] (φ0 : AdjoinRoot (GF.toPoly q.code.irr) →+* F0)
    (s : FS) (c : DCtx G q s) (bg : Big G q) (o : ℕ → Bool) (R : List Bool) (i W : ℕ)
    (h0 : s.env 0 = bitsValue R) (hR : R.length + 1 ≤ G.K) (h1 : s.env 1 = i) (hi : i < q.masks.length)
    (h16 : s.env 16 = W) (h3 : s.env 3 = i * nT q) (h2 : s.env 2 ≤ 1)
    (hW : ∀ bi < nT q, W / 2 ^ ((i * nT q + bi) * q.code.f) % 2 ^ q.code.f =
      q.wordAt o ((blkS q φ0 (Request.maskedCoins R q.masks[i])).getD bi 0)) :
    let t := evalS G passD s
    t.env 2 = s.env 2 * (if runVerdictN q φ o (Request.maskedCoins R q.masks[i]) then 1 else 0) ∧ t.env 2 ≤ 1 ∧
      t.env 3 = (i + 1) * nT q ∧ Wr passW s t := by
  intro t
  have pc := c.pc
  have db := pc.dbounds
  have hf1 : 1 ≤ q.code.f := pc.f1
  have hwf := pc.wf
  have hlin := bg.lin
  have hcK := cap_ge G
  have hNK := bg.N
  set σ := q.masks[i] with hσ
  set cn := Request.maskedCoins R σ with hcn
  have hb0 := bg.blk db i hi
  have hσl : σ.length ≤ q.data.length := db.sg σ (List.getElem_mem hi)
  have hqI : qcR q + qcH q + (q.code.cN + 1) + qcIo q = nT q := rfl
  have hBK : ∀ b, b ≤ i * nT q + nT q → (b + 105) * q.code.f + 1 ≤ G.K := fun b hb =>
    le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show b + 105 ≤ i * nT q + nT q + 105 by omega)) 1) hb0
  -- σ and the coin number
  obtain ⟨m26, m27, mw⟩ := maskP_spec G s q pc c.h15 (.v 1) i (by simp [evalE, h1]) hi
  generalize hs1 : evalS G (maskP (.v 1)) s = s1 at m26 m27 mw
  have c1 : DCtx G q s1 := c.wr mw
  set x := bitsValue R ^^^ bitsValue σ with hxd
  have hxK : x < 2 ^ G.K := Nat.xor_lt_two_pow
    (lt_of_lt_of_le (bv_lt R) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (lt_of_lt_of_le (bv_lt σ) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have e4 : evalE G s1 (.bxor (.v 0) (.v 26)) = x := by
    show (s1.env 0 ^^^ s1.env 26) % 2 ^ G.K = x
    rw [mw.env 0 (by decide), h0, m26]; exact Nat.mod_eq_of_lt hxK
  have c2 : DCtx G q (s1.setv 4 x) := c1.setv 4 x
  have hx : ∀ j, x / 2 ^ j % 2 = (cn j).toNat := maskedCoins_bits R σ
  have w2 : Wr passW s (s1.setv 4 x) :=
    (mw.mono fun _ hx => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))).trans
      (Wr.setv _ (by decide) _)
  have g16 : (s1.setv 4 x).env 16 = W := by rw [w2.env 16 (by decide), h16]
  have g3 : (s1.setv 4 x).env 3 = i * nT q := by simp; rw [mw.env 3 (by decide), h3]
  have g2 : (s1.setv 4 x).env 2 = s.env 2 := by simp; rw [mw.env 2 (by decide)]
  have hsub : ∀ y ∈ subW, y ∈ passW := fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)
  -- V_RS on p0
  obtain ⟨r2, r2le, r3, rw⟩ := subD_spec false none (recE 2) (.k 0) (.k 0) (.k 0) q hv φ hφ φ0 (s1.setv 4 x) c2 o cn x
    q.dA 0 (2 ^ q.code.f) (i * nT q) W 0 [] (fun _ => 0)
    (by rw [recE_parse G _ q c2.pc c2.h15 2 (by norm_num)]; rfl) (by simp) hx g16 g3 (by rw [g2]; exact h2)
    (bg.deg db.f _ db.dA) (hBK _ (by omega))
    (fun k hk1 hk => by
      have hk' : k ≤ qcR q := hk
      rw [hW (k - 1) (by unfold nT; omega), blkS_R q φ0 cn k hk1 hk])
    (Or.inl ⟨rfl, fun _ => rfl⟩) (fun h => by cases h)
  generalize hs3 : evalS G (subD false none (recE 2) (.k 0) (.k 0) (.k 0)) (s1.setv 4 x) = s3 at r2 r2le r3 rw
  have w3 : Wr passW s s3 := w2.trans (rw.mono hsub)
  have c3 : DCtx G q s3 := c2.wr rw
  have k4 : s3.env 4 = x := by rw [rw.env 4 (by decide)]; simp
  have k16 : s3.env 16 = W := by rw [w3.env 16 (by decide), h16]
  have k3 : s3.env 3 = i * nT q + qcR q := r3
  have hmH := db.mH
  have hdD := db.dB
  have hfD := db.f
  have hDK := bg.cube (q.data.length + 1) (q.data.length + 1) 1 le_rfl le_rfl (by omega)
  -- V_VRS on p1 over H
  obtain ⟨h2', h2le, h3', hw'⟩ := subD_spec true none (.sub (recE 11) (pw (recE 1))) (recE 3) (recE 1) (recE 4) q hv φ hφ
    φ0 s3 c3 o cn x q.dB (2 ^ q.code.f + lenR q) (2 * 2 ^ q.code.f + lenR q) (i * nT q + qcR q) W q.code.hOffset
    q.code.hBasis (fun _ => 0)
    (eE_sub (recE_parse G s3 q c3.pc c3.h15 11 (by norm_num))
      (eE_pow (recE_parse G s3 q c3.pc c3.h15 1 (by norm_num)) (by show q.code.hBasis.length + 1 ≤ G.K; omega)))
    k4 hx k16 k3 r2le (bg.deg db.f _ (lt_of_le_of_lt (by simp [innD]) hdD)) (hBK _ (by unfold nT; omega))
    (fun k hk1 hk => by
      have hk' : k ≤ qcH q := hk
      rw [show i * nT q + qcR q + (k - 1) = i * nT q + (qcR q + (k - 1)) by omega, hW _ (by unfold nT; omega),
        blkS_H q φ0 cn k hk1 hk])
    (Or.inl ⟨rfl, fun _ => rfl⟩)
    (fun _ => ⟨hwf.2.2.1, hwf.2.2.2.1,
      fun t w => recE_parse G t q (c3.wr w).pc (c3.wr w).h15 3 (by norm_num),
      fun t w => recE_parse G t q (c3.wr w).pc (c3.wr w).h15 1 (by norm_num),
      fun t w => recE_parse G t q (c3.wr w).pc (c3.wr w).h15 4 (by norm_num),
      by have : q.code.f * (q.code.hBasis.length + 1) ≤ (q.data.length + 1) * (q.data.length + 1) :=
           Nat.mul_le_mul (by omega) (by omega)
         omega, by omega⟩)
  generalize hs4 : evalS G (subD true none (.sub (recE 11) (pw (recE 1))) (recE 3) (recE 1) (recE 4)) s3 = s4
    at h2' h2le h3' hw'
  have w4 : Wr passW s s4 := w3.trans (hw'.mono hsub)
  have c4 : DCtx G q s4 := c3.wr hw'
  have l4 : s4.env 4 = x := by rw [hw'.env 4 (by decide), k4]
  have l16 : s4.env 16 = W := by rw [w4.env 16 (by decide), h16]
  have l3 : s4.env 3 = i * nT q + qcR q + qcH q := h3'
  -- the consistency test
  have hal : alphaW q cn = x % 2 ^ q.code.f := bv_coins cn x _ hx
  obtain ⟨c2', c2le, c3', cw⟩ := consD_spec q hv φ hφ s4 c4 o cn x (i * nT q + qcR q + qcH q) W l4 hx l16 l3 h2le
    (le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show _ ≤ i * nT q + nT q + 105 by unfold nT; omega)) 1)
      hb0)
    (fun j hj => by
      rw [show i * nT q + qcR q + qcH q + j = i * nT q + (qcR q + qcH q + j) by omega, hW _ (by unfold nT; omega),
        blkS_N q φ0 cn x j hal hj])
    (by rw [show i * nT q + qcR q + qcH q + q.code.cN = i * nT q + (qcR q + qcH q + q.code.cN) by omega,
        hW _ (by unfold nT; omega), blkS_P q φ0 cn x hal])
  generalize hs5 : evalS G consD s4 = s5 at c2' c2le c3' cw
  have w5 : Wr passW s s5 := w4.trans (cw.mono fun _ hx => List.mem_append_right _ hx)
  have c5 : DCtx G q s5 := c4.wr cw
  have m4 : s5.env 4 = x := by rw [cw.env 4 (by decide), l4]
  have m16 : s5.env 16 = W := by rw [w5.env 16 (by decide), h16]
  have hmI := db.mI
  have hiw : (iBw q).length = q.mI := pc.iBw_len
  -- V_VRS on p0 − p_x over I
  obtain ⟨i2, i2le, i3, iw⟩ := subD_spec true (some pxP) (.sub (recE 2) (pw (recE 10))) (recE 14) (recE 10) (recE 15) q
    hv φ hφ φ0 s5 c5 o cn x q.dA 0 (2 * 2 ^ q.code.f + lenR q + lenH q) (i * nT q + qcR q + qcH q + (q.code.cN + 1))
    W (iOw q) (iBw q) (pxN q φ)
    (by rw [eE_sub (recE_parse G s5 q c5.pc c5.h15 2 (by norm_num))
          (eE_pow (recE_parse G s5 q c5.pc c5.h15 10 (by norm_num)) (by show q.mI + 1 ≤ G.K; omega)), hiw]; rfl)
    m4 hx m16 (by rw [c3']; ring) c2le (bg.deg db.f _ (lt_of_le_of_lt (by simp [innD]) db.dA))
    (hBK _ (by unfold nT; omega))
    (fun k hk1 hk => by
      have hk' : k ≤ qcIo q := hk
      rw [show i * nT q + qcR q + qcH q + (q.code.cN + 1) + (k - 1) =
          i * nT q + (qcR q + qcH q + (q.code.cN + 1) + (k - 1)) by omega, hW _ (by unfold nT; omega),
        blkS_I q φ0 cn k hk1 hk])
    (Or.inr ⟨rfl, rfl⟩)
    (fun _ => ⟨pc.iBw_lt, pc.iOw_lt,
      fun t w => recE_parse G t q (c5.wr w).pc (c5.wr w).h15 14 (by norm_num),
      fun t w => (recE_parse G t q (c5.wr w).pc (c5.wr w).h15 10 (by norm_num)).trans hiw.symm,
      fun t w => recE_parse G t q (c5.wr w).pc (c5.wr w).h15 15 (by norm_num),
      by have : q.code.f * ((iBw q).length + 1) ≤ (q.data.length + 1) * (q.data.length + 1) :=
           Nat.mul_le_mul (by omega) (by omega)
         omega, by omega⟩)
  generalize hs6 : evalS G (subD true (some pxP) (.sub (recE 2) (pw (recE 10))) (recE 14) (recE 10) (recE 15)) s5 = s6
    at i2 i2le i3 iw
  have ht : t = evalS G (subD true (some pxP) (.sub (recE 2) (pw (recE 10))) (recE 14) (recE 10) (recE 15))
      (evalS G consD (evalS G (subD true none (.sub (recE 11) (pw (recE 1))) (recE 3) (recE 1) (recE 4))
      (evalS G (subD false none (recE 2) (.k 0) (.k 0) (.k 0))
      (evalS G (.set 4 (.bxor (.v 0) (.v 26))) (evalS G (maskP (.v 1)) s))))) := rfl
  rw [hs1, evalS_set, e4, hs3, hs4, hs5, hs6] at ht
  rw [ht]
  refine ⟨?_, i2le, by rw [i3]; show _ + qcIo q = _; unfold nT; ring, w5.trans (iw.mono hsub)⟩
  rw [i2, c2', h2', r2, g2, runVerdictN_parts, ite_and_mul, ite_and_mul, ite_and_mul]
  ring

end NearCubicGates.Adapters.ShortPCP.Machines.FL
