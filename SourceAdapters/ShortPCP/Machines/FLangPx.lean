import SourceAdapters.ShortPCP.Machines.FLangCircCons
import SourceAdapters.ShortPCP.TimeVerdict

/-!
# Single-run time, machine layer 23: the low-degree extension `p_x` of the instance

BCGT13 Construction 8.5 Step 5 runs `V_VRS` on `p0 − p_x`, where `p_x` is the low-degree extension of `x̄` over
the single input subspace `I`, whose basis and offset come from `q.code.iBasis` and `q.code.iOffset`
(`Request.iB`, `Request.iO`, `Request.px`; `Time.pxN` is the Lagrange form). The proof of `thm:short-pcp-ours` states: "By Lagrange interpolation over the
subspace `I` of size `|x̄|`, each evaluation takes `O(|x̄|²)` field operations".

`pxPrep` builds, from the parse record (`FLangParseRec.lean`), the packed points `GetEltWithIndex(I, j + 1)` (`49`),
the packed values `x̄_j ∈ {0, 1}` (`50`) and their number `|x̄|` (`51`); `lagP` (`FLangLag.lean`) then evaluates the
interpolant at the word in `52` into `53`. `pxP = pxPrep; lagP` (`pxP_spec`). Since `49`–`51` are inputs that
`lagP` does not write, a caller may run `pxPrep` once and `lagP` once per point.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins.SingleRun (Request)
open NearCubicGates.Adapters.ACSP.Affine (Instance)
open NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

variable (G : Glob)

/-- The point body: `46 := sel iB j + iO` (`j` in `54`; the basis in `20`/`21` via `selP`, the offset from slot 15). -/
def pxPt : S := .seq (.set 22 (.v 54)) (.seq selP (.set 46 (.fadd (.v 24) (recE 15))))

/-- The value body: `46 :=` bit `j` of `x̄` (slot 9). -/
def pxVal : S := .set 46 (.md (.shr (recE 9) (.v 54)) (.k 2))

/-- The Lagrange data of `p_x`: points `49`, values `50`, their number `51` (from record slots 14, 10, 8, 15, 9). -/
def pxPrep : S :=
  .seq (.set 20 (recE 14)) (.seq (.set 21 (recE 10)) (.seq (.set 55 (recE 8))
    (.seq (genP 55 54 46 49 23 pxPt) (.seq (genP 55 54 46 50 23 pxVal) (.set 51 (.v 55))))))

def pxPrepW : List Var := [20, 21, 22, 24, 25, 46, 49, 50, 51, 54, 55]

/-- **`p_x`** at the word in `52`, into `53`. -/
def pxP : S := .seq pxPrep lagP

def pxW : List Var := [20, 21, 22, 24, 25, 45, 46, 49, 50, 51, 53, 54, 55]

/-- The join's `p_x` in Lagrange form on words (`Time.pxN`, `Request.px`). -/
theorem pxN_eq {F : Type} [Field F] [DecidableEq F] (q : Request) (ψ : AdjoinRoot (GF.toPoly q.code.irr) →+* F)
    (x : F) : pxN q ψ x = lagEval q.xbar.length
      (fun i => eltWithIndex ((iBw q).map (ev ψ)) (ev ψ (iOw q)) (i + 1))
      (fun i => if q.xbar.getD i false then 1 else 0) x := rfl

/-- **The Lagrange data of `p_x`.** -/
theorem pxPrep_spec {F : Type} [Field F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (q : Request) {D : ℕ}
    (c : PCtx G q D) (h15 : s.env 15 = packW (G.K / 16) (parseRec q)) (h23 : s.env 23 = q.code.f)
    (hfl : s.fl = q.code.f) (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp)) :
    (∃ pts : List ℕ, (evalS G pxPrep s).env 49 = packW q.code.f pts ∧ pts.length = q.xbar.length ∧
      (∀ a ∈ pts, a < 2 ^ q.code.f) ∧
      ∀ j < q.xbar.length, ev φ (pts.getD j 0) = eltWithIndex ((iBw q).map (ev φ)) (ev φ (iOw q)) (j + 1)) ∧
    (evalS G pxPrep s).env 50 = packW q.code.f ((List.range q.xbar.length).map fun j => (q.xbar.getD j false).toNat) ∧
    (evalS G pxPrep s).env 51 = q.xbar.length ∧ Wr pxPrepW s (evalS G pxPrep s) := by
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  rw [hfl] at hf1 hfK hmod
  have hK := c.K32; have hcap := cap_ge G; have hx := c.xbar_le; have hm := c.mI_le; have hiBl := c.iBw_len
  have hKd := c.K; have hf := c.f_lt
  have hxK : q.code.f * q.xbar.length ≤ G.K := by
    have := Nat.mul_le_mul (show q.code.f ≤ q.data.length by omega) (show q.xbar.length ≤ q.data.length by omega)
    omega
  have hmK : q.mI * q.code.f ≤ G.cap := by
    have := Nat.mul_le_mul (show q.mI ≤ q.data.length by omega) (show q.code.f ≤ q.data.length by omega)
    omega
  have rr := fun (t : FS) (ht : t.env 15 = s.env 15) (i : ℕ) (hi : i < 16) =>
    recE_parse G t q c (by rw [ht]; exact h15) i hi
  set s1 := ((s.setv 20 (packW q.code.f (iBw q))).setv 21 q.mI).setv 55 q.xbar.length with hs1
  have e1 : evalS G (.set 55 (recE 8)) (evalS G (.set 21 (recE 10)) (evalS G (.set 20 (recE 14)) s)) = s1 := by
    simp only [evalS_set]
    rw [rr s rfl 14 (by norm_num), rr _ (by simp) 10 (by norm_num), rr _ (by simp) 8 (by norm_num)]; rfl
  have s1_15 : s1.env 15 = s.env 15 := by simp [s1]
  have s1_23 : s1.env 23 = q.code.f := by simp (config := { decide := true }) [s1, Function.update_apply, h23]
  -- the selection words
  have hsel : ∀ (u : FS) (j : ℕ), u.fp = s.fp → u.fl = s.fl → u.env 20 = packW q.code.f (iBw q) →
      u.env 21 = q.mI → u.env 23 = q.code.f →
      (evalS G selP (u.setv 22 j)).env 24 < 2 ^ q.code.f ∧
        ev φ ((evalS G selP (u.setv 22 j)).env 24) = sel ((iBw q).map (ev φ)) j ∧
        Wr [24, 25] (u.setv 22 j) (evalS G selP (u.setv 22 j)) := by
    intro u j ufp ufl u20 u21 u23
    obtain ⟨env, out, fl, fp, ip, bad⟩ := u
    obtain rfl : fp = s.fp := ufp
    obtain rfl : fl = s.fl := ufl
    have := selP_spec G (FS.setv ⟨env, out, s.fl, s.fp, ip, bad⟩ 22 j) φ (iBw q) (by rw [hfl]; exact c.iBw_lt)
      (by simpa [hfl] using u20) (by simpa [hiBl] using u21) (by simpa [hfl] using u23) hok
      (by rw [hiBl, hfl]; exact hmK) (by rw [hiBl]; have := hKd; have := c.N; omega)
    exact ⟨by rw [← hfl]; exact this.1, this.2.1, this.2.2⟩
  let sw : ℕ → ℕ := fun j => (evalS G selP (s1.setv 22 j)).env 24
  let g : ℕ → ℕ := fun j => (sw j ^^^ iOw q) % 2 ^ q.code.f
  have hsw : ∀ j, sw j < 2 ^ q.code.f ∧ ev φ (sw j) = sel ((iBw q).map (ev φ)) j := fun j =>
    let h := hsel s1 j rfl rfl (by simp [s1]) (by simp [s1]) s1_23
    ⟨h.1, h.2.1⟩
  have hg : ∀ j, g j < 2 ^ q.code.f ∧ ev φ (g j) = sel ((iBw q).map (ev φ)) j + ev φ (iOw q) := fun j => by
    have hx' := Nat.xor_lt_two_pow (hsw j).1 c.iOw_lt
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    simp only [g]; rw [Nat.mod_eq_of_lt hx', ev_xor, (hsw j).2]
  -- the points
  have hgen := genP_spec G 55 54 46 49 23 pxPt [22, 24, 25, 46] s1 q.xbar.length q.code.f g
    (by simp [s1]; have := c.N; omega) s1_23 hxK
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj u uW u54
      have u20 : u.env 20 = packW q.code.f (iBw q) := by rw [uW.env 20 (by decide)]; simp [s1]
      have u21 : u.env 21 = q.mI := by rw [uW.env 21 (by decide)]; simp [s1]
      have u23 : u.env 23 = q.code.f := by rw [uW.env 23 (by decide)]; exact s1_23
      have u15 : u.env 15 = s.env 15 := by rw [uW.env 15 (by decide)]; exact s1_15
      have hu := hsel u j uW.fp uW.fl u20 u21 u23
      have heq : (evalS G selP (u.setv 22 j)).env 24 = sw j :=
        ev_inj φ q.code.f _ _ hmod hirr hu.1 (hsw j).1 (hu.2.1.trans (hsw j).2.symm)
      have hfl' : (evalS G selP (u.setv 22 j)).fl = q.code.f := hu.2.2.fl.trans (uW.fl.trans hfl)
      have h15' : (evalS G selP (u.setv 22 j)).env 15 = s.env 15 := by
        rw [hu.2.2.env 15 (by decide)]; simpa using u15
      refine ⟨?_, (hg j).1, ?_⟩
      · simp only [pxPt, evalS_seq, evalS_set, FS.setv_env, Function.update_self]
        rw [show evalE G u (.v 54) = j from u54]
        simp only [evalE]
        rw [rr _ h15' 15 (by norm_num), heq, hfl']; rfl
      · simp only [pxPt, evalS_seq, evalS_set]; rw [show evalE G u (.v 54) = j from u54]
        exact ((Wr.setv (W := [22, 24, 25, 46]) (i := 22) _ (by decide) _).trans (hu.2.2.mono
          (W' := [22, 24, 25, 46]) (by decide))).trans (Wr.setv (W := [22, 24, 25, 46]) (i := 46) _ (by decide) _))
  obtain ⟨g49, gW⟩ := hgen
  generalize hs2 : evalS G (genP 55 54 46 49 23 pxPt) s1 = s2 at g49 gW
  have s2_55 : s2.env 55 = q.xbar.length := by rw [gW.env 55 (by decide)]; simp [s1]
  have s2_23 : s2.env 23 = q.code.f := by rw [gW.env 23 (by decide)]; exact s1_23
  have s2_15 : s2.env 15 = s.env 15 := by rw [gW.env 15 (by decide)]; exact s1_15
  -- the values
  have c2 : min 2 G.cap = 2 := by omega
  let gv : ℕ → ℕ := fun j => (q.xbar.getD j false).toNat
  have hgen2 := genP_spec G 55 54 46 50 23 pxVal [46] s2 q.xbar.length q.code.f gv
    (by rw [s2_55]; have := c.N; omega) s2_23 hxK
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj u uW u54
      have u15 : u.env 15 = s.env 15 := by rw [uW.env 15 (by decide)]; exact s2_15
      refine ⟨?_, ?_, Wr.setv _ (by decide) _⟩
      · simp only [pxVal, evalS_set, FS.setv_env, Function.update_self, evalE]
        rw [rr _ u15 9 (by norm_num), show u.env 54 = j from u54, c2]
        exact testBit_bitsValue q.xbar j
      · have : gv j ≤ 1 := bool_toNat_le _
        have : 2 ≤ 2 ^ q.code.f := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ q.code.f := Nat.pow_le_pow_right (by norm_num) hf1
        omega)
  obtain ⟨v50, vW⟩ := hgen2
  generalize hs3 : evalS G (genP 55 54 46 50 23 pxVal) s2 = s3 at v50 vW
  have e : evalS G pxPrep s = s3.setv 51 (s3.env 55) := by
    simp only [pxPrep, evalS_seq]
    rw [e1, hs2, hs3]; rfl
  rw [e]
  refine ⟨⟨(List.range q.xbar.length).map g, ?_, by simp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [FS.setv_env, Function.update_of_ne (show (49 : Var) ≠ 51 by decide)]
    rw [vW.env 49 (by decide), g49]
  · intro a ha; simp only [List.mem_map] at ha; obtain ⟨j, -, rfl⟩ := ha; exact (hg j).1
  · intro j hj
    rw [packW_map_range_getD q.code.f g, if_pos hj, (hg j).2, eltWithIndex_eq]; rfl
  · simp only [FS.setv_env, Function.update_of_ne (show (50 : Var) ≠ 51 by decide), v50]; rfl
  · simp only [FS.setv_env, Function.update_self]; rw [vW.env 55 (by decide), s2_55]
  · have w1 : Wr pxPrepW s s1 := by
      simp only [s1]
      exact ((Wr.setv _ (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)
    exact ((w1.trans (gW.mono (by decide))).trans (vW.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-- **`p_x` at the word in `52`** (proof of `thm:short-pcp-ours`), into `53`. -/
theorem pxP_spec {F : Type} [Field F] [CharP F 2] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (q : Request)
    {D : ℕ} (c : PCtx G q D) (h15 : s.env 15 = packW (G.K / 16) (parseRec q)) (h23 : s.env 23 = q.code.f)
    (hfl : s.fl = q.code.f) (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp))
    (hind : Indep ((iBw q).map (ev φ))) (hx : q.xbar.length = 2 ^ q.mI) (h52 : s.env 52 < 2 ^ q.code.f) :
    (evalS G pxP s).env 53 < 2 ^ q.code.f ∧
      ev φ ((evalS G pxP s).env 53) = lagEval q.xbar.length
        (fun i => eltWithIndex ((iBw q).map (ev φ)) (ev φ (iOw q)) (i + 1))
        (fun i => if q.xbar.getD i false then 1 else 0) (ev φ (s.env 52)) ∧
      Wr pxW s (evalS G pxP s) := by
  have hxd := c.xbar_le; have hf := c.f_lt; have hKd := c.K; have hN := c.N
  obtain ⟨hf1, -, -, -⟩ := fl_bounds hok
  rw [hfl] at hf1
  obtain ⟨⟨pts, p49, plen, plt, pev⟩, v50, c51, pW⟩ := pxPrep_spec G s φ q c h15 h23 hfl hok hirr
  have e : evalS G pxP s = evalS G lagP (evalS G pxPrep s) := rfl
  rw [e]
  generalize ht : evalS G pxPrep s = t at p49 v50 c51 pW
  obtain ⟨env, out, fl, fp, ip, bad⟩ := t
  obtain rfl : fp = s.fp := pW.fp
  obtain rfl : fl = s.fl := pW.fl
  set vals := (List.range q.xbar.length).map fun j => (q.xbar.getD j false).toNat with hvals
  have h2f : 2 ≤ 2 ^ q.code.f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ q.code.f := Nat.pow_le_pow_right (by norm_num) hf1
  have hvw : ∀ a ∈ vals, a < 2 ^ s.fl := by
    intro a ha; simp only [hvals, List.mem_map] at ha; obtain ⟨j, -, rfl⟩ := ha
    have := bool_toNat_le (q.xbar.getD j false); rw [hfl]; omega
  have hdist : ∀ i j, i < q.xbar.length → j < q.xbar.length → i ≠ j → pts.getD i 0 ≠ pts.getD j 0 := by
    intro i j hi hj hij heq
    have h1 := congrArg (ev φ) heq
    rw [pev i hi, pev j hj, eltWithIndex_eq, eltWithIndex_eq, Nat.add_sub_cancel, Nat.add_sub_cancel] at h1
    have hlen : ((iBw q).map (ev φ)).length = q.mI := by rw [List.length_map, c.iBw_len]
    exact hij (hind.injOn (by rw [hlen, ← hx]; exact hi) (by rw [hlen, ← hx]; exact hj) (add_right_cancel h1))
  have e52 : env 52 = s.env 52 := pW.env 52 (by decide)
  have hmK : q.xbar.length * s.fl + s.fl + 1 ≤ G.K := by
    rw [hfl]
    have := Nat.mul_le_mul (show q.xbar.length ≤ q.data.length by omega) (show q.code.f ≤ q.data.length by omega)
    omega
  obtain ⟨l53, ev53, lW⟩ := lagP_spec G ⟨env, out, s.fl, s.fp, ip, bad⟩ φ pts vals q.xbar.length
    (fun a ha => by show a < 2 ^ s.fl; rw [hfl]; exact plt a ha) hvw
    (by show env 49 = packW s.fl pts; rw [hfl]; exact p49) (by show env 50 = packW s.fl vals; rw [hfl]; exact v50)
    c51 (by show env 52 < 2 ^ s.fl; rw [e52, hfl]; exact h52)
    (by show env 23 = s.fl; have := pW.env 23 (by decide); simp only at this; rw [this, h23, hfl])
    hok hirr (by omega) hmK hdist
  refine ⟨by rw [← hfl]; exact l53, ?_, (pW.mono (by decide)).trans (lW.mono (by decide))⟩
  have ev52 : ev φ ((⟨env, out, s.fl, s.fp, ip, bad⟩ : FS).env 52) = ev φ (s.env 52) := by
    show ev φ (env 52) = _; rw [e52]
  rw [ev53, ev52]
  apply lagEval_congr
  · intro j hj; exact pev j hj
  · intro j hj
    rw [hvals, packW_map_range_getD s.fl, if_pos hj]
    cases q.xbar.getD j false
    · simp
    · simp [ev_one]

end NearCubicGates.Adapters.ShortPCP.Machines.FL
