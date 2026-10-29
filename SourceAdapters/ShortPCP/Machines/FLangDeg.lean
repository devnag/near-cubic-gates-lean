import SourceAdapters.ShortPCP.Machines.FLangLag

/-!
# Single-run time, machine layer 15: the base-case degree test

`Time.degreeTestF B O deg ans` (the base of `D_{RS,=}` and of `D_RS`, BCGT13 Algorithm 23 with Algorithm 16 step 1;
proof of `thm:short-pcp-ours`) accepts iff `2^κ ≤ deg + 1` or every point `i + 1` of the subspace agrees with the interpolant through
the first `deg + 1` points. `dtP` computes it for the level held in `38`–`40` (`Machines/FLangStep.lean`), the degree
in `12` and the packed answers in `11` (word `i` = `ans i`): the points `sel B j + O` (`j < 2^κ`) are built with
`genP` into `49`, the values `ans (j + 1)` are `11` shifted by one word, and `lagP` evaluates the interpolant at each
point (`dtP_spec`). Result bit in `7`, loop variable `13`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

variable (G : Glob)

/-- Distinct reduced words have distinct field elements (irreducible modulus). -/
theorem ev_inj {F : Type} [Field F] {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (ℓ a b : ℕ)
    (hp : GF.ModulusOk p ℓ) (hirr : Irreducible (GF.toPoly p)) (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : ev φ a = ev φ b) : a = b := by
  haveI : Fact (Irreducible (GF.toPoly p)) := ⟨hirr⟩
  exact GF.rep_injOn p ℓ a b hp ha hb (φ.injective h)

/-- The body building the points: `46 := sel B j + O` for `j` in `54`. -/
def ptBody : S := .seq (.set 22 (.v 54)) (.seq selP (.set 46 (.fadd (.v 24) (.v 40))))

/-- The check loop: `7 := 7 · [lagEval(x_i) = ans (i + 1)]` for `i` in `13`. -/
def dtLoop : S :=
  .loop 13 (.v 55) (.seq (.set 52 (getW 49 (.v 13))) (.seq lagP
    (.set 7 (.mul (.v 7) (.eq (.v 53) (getW 11 (.add (.v 13) (.k 1))))))))

/-- **The base-case degree test** into `7`. -/
def dtP : S :=
  .seq (.set 20 (.v 38)) (.seq (.set 21 (.v 39)) (.seq (.set 55 (.shl (.k 1) (.v 39)))
  (.seq (genP 55 54 46 49 23 ptBody) (.seq (.set 50 (.shr (.v 11) (.v 23))) (.seq (.set 51 (.add (.v 12) (.k 1)))
  (.seq (.set 7 (.k 1)) (.ite (.lt (.v 51) (.v 55)) dtLoop .skip)))))))

/-- The variables `dtP` writes. -/
def dtW : List Var := [7, 13, 20, 21, 22, 24, 25, 45, 46, 49, 50, 51, 52, 53, 54, 55]

theorem lagEval_congr {F : Type} [Field F] (m : ℕ) (pt pt' val val' : ℕ → F) (x : F)
    (hp : ∀ j < m, pt j = pt' j) (hv : ∀ j < m, val j = val' j) : lagEval m pt val x = lagEval m pt' val' x := by
  unfold lagEval
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hv i hi]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [hp i hi, hp j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))]

theorem getD_drop_one (l : List ℕ) (j : ℕ) : (l.drop 1).getD j 0 = l.getD (j + 1) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

theorem getD_lt {w : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (j : ℕ) : l.getD j 0 < 2 ^ w := by
  rcases Nat.lt_or_ge j l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; positivity

/-- **The base-case degree test** (`Time.degreeTestF`, Algorithm 23) on the level in `38`–`40`. -/
theorem dtP_spec {F : Type} [Field F] [CharP F 2] [DecidableEq F] (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (l ansl : List ℕ) (d : ℕ) (hlw : ∀ a ∈ l, a < 2 ^ s.fl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl)
    (h38 : s.env 38 = packW s.fl l) (h39 : s.env 39 = l.length) (h40 : s.env 40 < 2 ^ s.fl)
    (h11 : s.env 11 = packW s.fl ansl) (h12 : s.env 12 = d) (h23 : s.env 23 = s.fl)
    (hok : fieldOk G s.fl s.fp = true) (hirr : Irreducible (GF.toPoly s.fp)) (hind : Indep (l.map (ev φ)))
    (hK : 2 ^ l.length * s.fl + s.fl + 1 ≤ G.K) (hN : 2 ^ l.length ≤ G.N) (hd : d + 2 ≤ G.K) :
    let t := evalS G dtP s
    t.env 7 = (if degreeTestF (l.map (ev φ)) (ev φ (s.env 40)) d (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      Wr dtW s t := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds hok
  have hc1 : min 1 G.cap = 1 := min_cap (by omega)
  have hκ1 : l.length < 2 ^ l.length := Nat.lt_two_pow_self
  have hfle : 2 ^ l.length ≤ 2 ^ l.length * s.fl := Nat.le_mul_of_pos_right _ hf1
  have e1 : min (2 ^ l.length) G.cap = 2 ^ l.length := min_cap_pow (by omega)
  have hcapl : l.length * s.fl ≤ G.cap := by
    have := cap_ge G; have := Nat.mul_le_mul_right s.fl hκ1.le; omega
  -- the canonical selection words
  let s3 : FS := ((s.setv 20 (packW s.fl l)).setv 21 l.length).setv 55 (2 ^ l.length)
  have hs3 : evalS G (.set 55 (.shl (.k 1) (.v 39))) (evalS G (.set 21 (.v 39)) (evalS G (.set 20 (.v 38)) s)) = s3 := by
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false, h38,
      h39, hc1, one_mul, e1, s3]
  have hsel : ∀ (t : FS) (j : ℕ), t.fp = s.fp → t.fl = s.fl → t.env 20 = packW s.fl l → t.env 21 = l.length →
      t.env 23 = s.fl → (evalS G selP (t.setv 22 j)).env 24 < 2 ^ s.fl ∧
        ev φ ((evalS G selP (t.setv 22 j)).env 24) = sel (l.map (ev φ)) j ∧ Wr [24, 25] (t.setv 22 j) (evalS G selP (t.setv 22 j)) := by
    intro t j tfp tfl t20 t21 t23
    obtain ⟨env, out, fl, fp, ip, bad⟩ := t
    obtain rfl : fp = s.fp := tfp
    obtain rfl : fl = s.fl := tfl
    have := selP_spec G (FS.setv ⟨env, out, s.fl, s.fp, ip, bad⟩ 22 j) φ l hlw (by simpa using t20) (by simpa using t21)
      (by simpa using t23) hok (by simpa using hcapl) (by omega)
    exact ⟨this.1, this.2.1, this.2.2⟩
  let sw : ℕ → ℕ := fun j => (evalS G selP (s3.setv 22 j)).env 24
  let g : ℕ → ℕ := fun j => (sw j ^^^ s.env 40) % 2 ^ s.fl
  have hsw : ∀ j, sw j < 2 ^ s.fl ∧ ev φ (sw j) = sel (l.map (ev φ)) j := fun j =>
    let h := hsel s3 j rfl rfl (by simp [s3]) (by simp [s3]) (by simp (config := { decide := true }) [s3,
      Function.update_apply, h23])
    ⟨h.1, h.2.1⟩
  have hg : ∀ j, g j < 2 ^ s.fl ∧ ev φ (g j) = sel (l.map (ev φ)) j + ev φ (s.env 40) := fun j => by
    have hx := Nat.xor_lt_two_pow (hsw j).1 h40
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    simp only [g]; rw [Nat.mod_eq_of_lt hx, ev_xor, (hsw j).2]
  -- the points
  have hgen := genP_spec G 55 54 46 49 23 ptBody [22, 24, 25, 46] s3 (2 ^ l.length) s.fl g (by simp [s3]; omega)
    (by simp (config := { decide := true }) [s3, Function.update_apply, h23]) (by rw [mul_comm]; omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      intro j hj u uW u54
      have u20 : u.env 20 = packW s.fl l := by rw [uW.env 20 (by decide)]; simp [s3]
      have u21 : u.env 21 = l.length := by rw [uW.env 21 (by decide)]; simp [s3]
      have u23 : u.env 23 = s.fl := by rw [uW.env 23 (by decide)]; simp (config := { decide := true }) [s3,
        Function.update_apply, h23]
      have u40 : u.env 40 = s.env 40 := by rw [uW.env 40 (by decide)]; simp (config := { decide := true }) [s3,
        Function.update_apply]
      have hu := hsel u j uW.fp uW.fl u20 u21 u23
      have heq : (evalS G selP (u.setv 22 j)).env 24 = sw j :=
        ev_inj φ s.fl _ _ hmod hirr hu.1 (hsw j).1 (hu.2.1.trans (hsw j).2.symm)
      have hfl : (evalS G selP (u.setv 22 j)).fl = s.fl := hu.2.2.fl.trans uW.fl
      have h40' : (evalS G selP (u.setv 22 j)).env 40 = s.env 40 := by rw [hu.2.2.env 40 (by decide)]; simpa using u40
      refine ⟨?_, (hg j).1, ?_⟩
      · simp only [ptBody, evalS_seq, evalS_set, evalE, u54, FS.setv_env, Function.update_self, heq, h40', hfl]
        rfl
      · simp only [ptBody, evalS_seq, evalS_set]; rw [show evalE G u (.v 54) = j from u54]
        exact ((Wr.setv (W := [22, 24, 25, 46]) (i := 22) _ (by decide) _).trans (hu.2.2.mono (W' := [22, 24, 25, 46])
          (by decide))).trans (Wr.setv (W := [22, 24, 25, 46]) (i := 46) _ (by decide) _))
  obtain ⟨g49, gW⟩ := hgen
  generalize hs4 : evalS G (genP 55 54 46 49 23 ptBody) s3 = s4 at g49 gW
  have s4_11 : s4.env 11 = packW s.fl ansl := by rw [gW.env 11 (by decide)]; simp [s3, h11]
  have s4_12 : s4.env 12 = d := by rw [gW.env 12 (by decide)]; simp [s3, h12]
  have s4_23 : s4.env 23 = s.fl := by rw [gW.env 23 (by decide)]; simp (config := { decide := true }) [s3,
    Function.update_apply, h23]
  have s4_55 : s4.env 55 = 2 ^ l.length := by rw [gW.env 55 (by decide)]; simp [s3]
  have s4fl : s4.fl = s.fl := gW.fl
  have s4fp : s4.fp = s.fp := gW.fp
  have hd1 : min (d + 1) G.cap = d + 1 := min_cap (by omega)
  set pts := (List.range (2 ^ l.length)).map g with hpts
  have hpw : ∀ a ∈ pts, a < 2 ^ s.fl := by
    intro a ha; simp only [hpts, List.mem_map] at ha; obtain ⟨j, -, rfl⟩ := ha; exact (hg j).1
  have hvw : ∀ a ∈ ansl.drop 1, a < 2 ^ s.fl := fun a ha => haw a (List.mem_of_mem_drop ha)
  let s7 : FS := ((s4.setv 50 (packW s.fl (ansl.drop 1))).setv 51 (d + 1)).setv 7 1
  have hs7 : evalS G (.set 7 (.k 1)) (evalS G (.set 51 (.add (.v 12) (.k 1))) (evalS G (.set 50 (.shr (.v 11) (.v 23))) s4))
      = s7 := by
    simp (config := { decide := true }) only [evalS_set, evalE, FS.setv_env, Function.update_apply, if_false, s4_11,
      s4_12, s4_23, hc1, hd1, s7]
    rw [packW_drop _ ansl haw 1, mul_one]
  have ht : t = evalS G (.ite (.lt (.v 51) (.v 55)) dtLoop .skip) s7 := by
    show evalS G dtP s = _
    simp only [dtP, evalS_seq]
    rw [hs3, hs4, hs7]
  have s7W : Wr dtW s s7 :=
    ((((Wr.setv (W := dtW) (i := 20) s (by decide) _).trans (Wr.setv (W := dtW) (i := 21) _ (by decide) _)).trans
      (Wr.setv (W := dtW) (i := 55) _ (by decide) _)).trans (gW.mono (W' := dtW) (by decide))).trans
      ((Wr.setv (W := dtW) (i := 50) _ (by decide) _).trans ((Wr.setv (W := dtW) (i := 51) _ (by decide) _).trans
        (Wr.setv (W := dtW) (i := 7) _ (by decide) _)))
  have hlen : (l.map (ev φ)).length = l.length := List.length_map _
  rw [ht, evalS_ite]
  by_cases hlt : d + 1 < 2 ^ l.length
  · have hc : evalE G s7 (.lt (.v 51) (.v 55)) = 1 := by
      simp (config := { decide := true }) [evalE, s7, Function.update_apply, s4_55, hlt]
    rw [hc, if_neg one_ne_zero]
    have hm2 : min (evalE G s7 (.v 55)) G.N = 2 ^ l.length := by
      simp (config := { decide := true }) only [evalE, s7, FS.setv_env, Function.update_apply, if_false, s4_55]
      omega
    have hκ2 : l.length = (l.map (ev φ)).length := hlen.symm
    let chk : ℕ → Bool := fun i => decide (lagEval (d + 1) (fun j => eltWithIndex (l.map (ev φ)) (ev φ (s.env 40)) (j + 1))
      (fun j => ev φ (ansl.getD (j + 1) 0)) (eltWithIndex (l.map (ev φ)) (ev φ (s.env 40)) (i + 1)) =
        ev φ (ansl.getD (i + 1) 0))
    have hpg : ∀ j, j < 2 ^ l.length → pts.getD j 0 = g j := fun j hj => by
      rw [hpts, packW_map_range_getD s.fl, if_pos hj]
    have hl := loop_inv G (i := 13) (n := .v 55) (body := .seq (.set 52 (getW 49 (.v 13))) (.seq lagP
        (.set 7 (.mul (.v 7) (.eq (.v 53) (getW 11 (.add (.v 13) (.k 1))))))))
      (s := s7) (fun i' u => u.env 7 = (if (List.range i').all chk then 1 else 0) ∧
        Wr [7, 13, 45, 46, 52, 53, 54, 55] s7 u)
      ⟨by simp [s7], Wr.refl _ _⟩ (by
        rw [hm2]
        rintro i hi u ⟨u7, uW⟩
        obtain ⟨env, out, fl, fp, ip, bad⟩ := u
        obtain rfl : fp = s.fp := uW.fp.trans s4fp
        obtain rfl : fl = s.fl := uW.fl.trans s4fl
        have u49 : env 49 = packW s.fl pts := by
          have := uW.env 49 (by decide); simp only at this; rw [this]; simp [s7, g49]
        have u50 : env 50 = packW s.fl (ansl.drop 1) := by
          have := uW.env 50 (by decide); simp only at this; rw [this]; simp [s7]
        have u51 : env 51 = d + 1 := by
          have := uW.env 51 (by decide); simp only at this; rw [this]; simp [s7]
        have u23 : env 23 = s.fl := by
          have := uW.env 23 (by decide); simp only at this; rw [this]
          simp (config := { decide := true }) [s7, Function.update_apply, s4_23]
        have u11 : env 11 = packW s.fl ansl := by
          have := uW.env 11 (by decide); simp only at this; rw [this]
          simp (config := { decide := true }) [s7, Function.update_apply, s4_11]
        set u : FS := ⟨env, out, s.fl, s.fp, ip, bad⟩ with hu
        have hiK : i * s.fl ≤ G.K := by have := Nat.mul_le_mul_right s.fl hi.le; omega
        have hi1K : (i + 1) * s.fl ≤ G.K := by
          have := Nat.mul_le_mul_right s.fl (show i + 1 ≤ 2 ^ l.length by omega); omega
        have hdK : (d + 1) * s.fl + s.fl + 1 ≤ G.K := by
          have := Nat.mul_le_mul_right s.fl (show d + 1 ≤ 2 ^ l.length by omega); omega
        have hgi := getW_eval G (u.setv 13 i) 49 (.v 13) s.fl i pts hpw (by simp [hu, u49]) (by simp [hu, u23])
          (by simp [evalE]) hiK (by omega)
        rw [hpg i hi] at hgi
        have hlag := lagP_spec G ((u.setv 13 i).setv 52 (g i)) φ pts (ansl.drop 1) (d + 1) hpw hvw
          (by simp [hu, u49]) (by simp [hu, u50]) (by simp [hu, u51]) (by simp; exact (hg i).1)
          (by simp [hu, u23]) hok hirr (by omega) hdK (by
            intro a b ha hb hab heq
            rw [hpg a (by omega), hpg b (by omega)] at heq
            have h2 := congrArg (ev φ) heq
            rw [(hg a).2, (hg b).2] at h2
            exact hab (hind.injOn (by rw [List.length_map]; omega) (by rw [List.length_map]; omega)
              (add_right_cancel h2)))
        obtain ⟨l53, lev, lW⟩ := hlag
        generalize hu3 : evalS G lagP ((u.setv 13 i).setv 52 (g i)) = u3 at l53 lev lW
        have v7 : u3.env 7 = env 7 := by rw [lW.env 7 (by decide)]; simp [hu]
        have v13 : u3.env 13 = i := by rw [lW.env 13 (by decide)]; simp
        have v11 : u3.env 11 = packW s.fl ansl := by rw [lW.env 11 (by decide)]; simp [hu, u11]
        have v23 : u3.env 23 = s.fl := by rw [lW.env 23 (by decide)]; simp [hu, u23]
        have hc1' : min (i + 1) G.cap = i + 1 := min_cap (by omega)
        have hai := getW_eval G u3 11 (.add (.v 13) (.k 1)) s.fl (i + 1) ansl haw v11 v23
          (by simp [evalE, v13, hc1, hc1']) hi1K (by omega)
        have hchk : (u3.env 53 = ansl.getD (i + 1) 0) ↔ chk i = true := by
          simp only [chk, decide_eq_true_eq]
          have e2 : lagEval (d + 1) (fun j => ev φ (pts.getD j 0)) (fun j => ev φ ((ansl.drop 1).getD j 0))
              (ev φ (((u.setv 13 i).setv 52 (g i)).env 52)) = lagEval (d + 1)
              (fun j => eltWithIndex (l.map (ev φ)) (ev φ (s.env 40)) (j + 1)) (fun j => ev φ (ansl.getD (j + 1) 0))
              (eltWithIndex (l.map (ev φ)) (ev φ (s.env 40)) (i + 1)) := by
            have ex : ev φ (((u.setv 13 i).setv 52 (g i)).env 52) =
                eltWithIndex (l.map (ev φ)) (ev φ (s.env 40)) (i + 1) := by
              simp only [FS.setv_env, Function.update_self]
              rw [(hg i).2, eltWithIndex_eq, Nat.add_sub_cancel]
            rw [ex]
            apply lagEval_congr
            · intro j hj
              rw [hpg j (by omega), (hg j).2, eltWithIndex_eq, Nat.add_sub_cancel]
            · intro j hj; rw [getD_drop_one]
          rw [← e2]
          constructor
          · intro h; rw [← h]; exact lev.symm
          · intro h; exact ev_inj φ s.fl _ _ hmod hirr l53 (getD_lt ansl haw _) (lev.trans h)
        refine ⟨?_, ?_⟩
        · simp only [evalS_seq, evalS_set]
          rw [hgi, hu3]
          simp only [FS.setv_env, Function.update_self, evalE, hai, v7]
          rw [show env 7 = u.env 7 from rfl, u7, List.range_succ, List.all_append, List.all_cons, List.all_nil,
            Bool.and_true]
          by_cases hq : u3.env 53 = ansl.getD (i + 1) 0
          · rw [if_pos hq, hchk.mp hq]
            cases (List.range i).all chk <;> simp [hc1]
          · rw [if_neg hq, show chk i = false by simpa using (mt hchk.mpr hq)]
            have hc0 : min 0 G.cap = 0 := min_cap (by omega)
            cases (List.range i).all chk <;> simp [hc0]
        · simp only [evalS_seq, evalS_set]
          rw [hgi, hu3]
          exact (((uW.trans (Wr.setv (W := [7, 13, 45, 46, 52, 53, 54, 55]) (i := 13) _ (by decide) _)).trans
            (Wr.setv (W := [7, 13, 45, 46, 52, 53, 54, 55]) (i := 52) _ (by decide) _)).trans
            (lW.mono (W' := [7, 13, 45, 46, 52, 53, 54, 55]) (by decide))).trans
            (Wr.setv (W := [7, 13, 45, 46, 52, 53, 54, 55]) (i := 7) _ (by decide) _))
    rw [hm2] at hl
    obtain ⟨t7, tW⟩ := hl
    refine ⟨?_, s7W.trans (tW.mono (W' := dtW) (by decide))⟩
    rw [show evalS G dtLoop s7 = evalS G (.loop 13 (.v 55) (.seq (.set 52 (getW 49 (.v 13))) (.seq lagP
        (.set 7 (.mul (.v 7) (.eq (.v 53) (getW 11 (.add (.v 13) (.k 1))))))))) s7 from rfl, t7]
    unfold degreeTestF
    rw [hlen, if_neg (show ¬ 2 ^ l.length ≤ d + 1 by omega)]
  · have hc : evalE G s7 (.lt (.v 51) (.v 55)) = 0 := by
      simp (config := { decide := true }) [evalE, s7, Function.update_apply, s4_55, hlt]
    rw [hc, if_pos rfl, evalS_skip]
    refine ⟨?_, s7W⟩
    unfold degreeTestF
    rw [hlen, if_pos (show 2 ^ l.length ≤ d + 1 by omega)]
    simp [s7]


end NearCubicGates.Adapters.ShortPCP.Machines.FL
