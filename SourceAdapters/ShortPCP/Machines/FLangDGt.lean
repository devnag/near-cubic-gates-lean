import SourceAdapters.ShortPCP.Machines.FLangDRS

/-!
# Single-run time, machine layer 27: the decision of `V_{RS,>}`, of `V_RS`, and of a sub-verifier run

BCGT13 Algorithm 14 (`D_{RS,>}`: the `m` runs of `D_{RS,=}` on consecutive answer blocks, the run of `D_{RS,<}` for the
remainder degree, and the combination test `v = Σ_{i<4} γ^{i(d_{κ,η}+1)} a_i` at the random point `γ`), Algorithm 13
(`V_RS` dispatches on the degree) and Algorithm 12 (`V_VRS`: `V_RS`'s decision and the test
`a_{q+1} = Z_H(α + O_H)·a_{q+2}`); proof of `thm:short-pcp-ours`. `dOutP v` decides `TimeBlocks.outD` from the answers at the
effective positions (`dOutP_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-! ## The combination test -/

/-- The answer word `a(5 + k)`. -/
def aE (k : ℕ) : E := getW 11 (.add (.v 5) (.k k))

/-- `γ`'s word: the coins mod `2^f`. -/
def gwE : E := .md (.v 42) nSE

/-- The term `γ^{i(d_{f,2}+1)} · a(base + 2 + i)`. -/
def tE (i : ℕ) : E := .fmul (.fpow gwE (.mul (.k i) (.add dKEE (.k 1)))) (aE (2 + i))

/-- The combination test (base in `5`). -/
def bcE : E := .eq (aE 1) (.fadd (.fadd (tE 0) (tE 1)) (.fadd (tE 2) (tE 3)))

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

theorem getD_wlt (l : List ℕ) (w : ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (j : ℕ) : l.getD j 0 < 2 ^ w := by
  rcases Nat.lt_or_ge j l.length with h | h
  · exact hl _ (List.getD_eq_getElem _ _ h ▸ List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; exact Nat.two_pow_pos _

omit [CharP F 2] in
theorem bcE_eval (t : FS) (φ : AdjoinRoot (GF.toPoly t.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ) (base : ℕ)
    (c : QC G t l0 u) (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ t.fl))
    (h5 : t.env 5 = base) (h11 : t.env 11 = packW t.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ t.fl)
    (hK : (base + 6) * t.fl ≤ G.K) :
    evalE G t bcE = if ev φ (ansl.getD (base + 1) 0) = ∑ i ∈ Finset.range 4,
      getRandElt (l0.map (ev φ)) 0 (u.take t.fl) ^ (i * (dKE t.fl 2 + 1)) * ev φ (ansl.getD (base + 2 + i) 0)
      then 1 else 0 := by
  have A := c.atoms
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hbig := A.big
  have hp := pf_le t.fl
  have hk := dKE_lt t.fl
  have hcK := cap_ge G
  have h64 : 64 ≤ 2 ^ (8 * t.fl + 20) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 6 ≤ 8 * t.fl + 20 by omega))
  have hka : ∀ k, k ≤ 5 → evalE G t (aE k) = ansl.getD (base + k) 0 := by
    intro k hk5
    refine getW_eval G t 11 _ t.fl _ ansl haw h11 c.h23 (eE_add (eE_v 5 |>.trans h5) (eE_k (by omega))
      (by have : (base + 6) * t.fl ≥ base + 6 := Nat.le_mul_of_pos_right _ hf1; omega)) ?_ (by omega)
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hK
  have hγ : evalE G t gwE = bitsValue (u.take t.fl) % 2 ^ t.fl := by
    rw [gwE, eE_md (eE_v 42 |>.trans c.h42) A.n, bitsValue_take, Nat.mod_mod]
  have hγl : bitsValue (u.take t.fl) % 2 ^ t.fl < 2 ^ t.fl := Nat.mod_lt _ (by positivity)
  have hγe : getRandElt (l0.map (ev φ)) 0 (u.take t.fl) = ev φ (bitsValue (u.take t.fl) % 2 ^ t.fl) :=
    dom_rand φ hdom _
  have hte : ∀ i, i ≤ 3 → evalE G t (tE i) =
      mulW t.fp t.fl (powW t.fp t.fl (bitsValue (u.take t.fl) % 2 ^ t.fl) (i * (dKE t.fl 2 + 1)))
        (ansl.getD (base + (2 + i)) 0) := by
    intro i hi
    have he : evalE G t (.mul (.k i) (.add dKEE (.k 1))) = i * (dKE t.fl 2 + 1) :=
      eE_mul (eE_k (by omega)) (eE_add A.k (eE_k (by omega)) (by omega)) (by
        have : i * (dKE t.fl 2 + 1) ≤ 3 * 2 ^ t.fl := Nat.mul_le_mul (by omega) (by omega)
        have : 4 * 2 ^ t.fl ≤ 2 ^ (8 * t.fl + 20) := by
          have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show t.fl + 2 ≤ 8 * t.fl + 20 by omega)
          rw [pow_add] at this; omega
        omega)
    show mulW t.fp t.fl (evalE G t (.fpow gwE _) % 2 ^ t.fl) (evalE G t (aE (2 + i)) % 2 ^ t.fl) = _
    rw [hka (2 + i) (by omega), Nat.mod_eq_of_lt (getD_wlt ansl t.fl haw _)]
    show mulW t.fp t.fl (powW t.fp t.fl (evalE G t gwE % 2 ^ t.fl) (evalE G t _) % 2 ^ t.fl) _ = _
    rw [hγ, he, Nat.mod_mod, Nat.mod_eq_of_lt (powW_lt _ _ _ _)]
  have hfa : ∀ a b : E, ∀ x y : ℕ, evalE G t a = x → evalE G t b = y → x < 2 ^ t.fl → y < 2 ^ t.fl →
      evalE G t (.fadd a b) = x ^^^ y ∧ x ^^^ y < 2 ^ t.fl :=
    fun a b x y ha hb hx hy => ⟨eE_fadd ha hb hx hy, Nat.xor_lt_two_pow hx hy⟩
  obtain ⟨e01, l01⟩ := hfa _ _ _ _ (hte 0 (by omega)) (hte 1 (by omega)) (mulW_lt _ _ _ _) (mulW_lt _ _ _ _)
  obtain ⟨e23, l23⟩ := hfa _ _ _ _ (hte 2 (by omega)) (hte 3 (by omega)) (mulW_lt _ _ _ _) (mulW_lt _ _ _ _)
  obtain ⟨es, ls⟩ := hfa _ _ _ _ e01 e23 l01 l23
  rw [bcE, eE_eq (hka 1 (by omega)) es]
  have hsum : ev φ ((mulW t.fp t.fl (powW t.fp t.fl (bitsValue (u.take t.fl) % 2 ^ t.fl) (0 * (dKE t.fl 2 + 1)))
      (ansl.getD (base + (2 + 0)) 0) ^^^ mulW t.fp t.fl (powW t.fp t.fl (bitsValue (u.take t.fl) % 2 ^ t.fl)
      (1 * (dKE t.fl 2 + 1))) (ansl.getD (base + (2 + 1)) 0)) ^^^ (mulW t.fp t.fl (powW t.fp t.fl
      (bitsValue (u.take t.fl) % 2 ^ t.fl) (2 * (dKE t.fl 2 + 1))) (ansl.getD (base + (2 + 2)) 0) ^^^
      mulW t.fp t.fl (powW t.fp t.fl (bitsValue (u.take t.fl) % 2 ^ t.fl) (3 * (dKE t.fl 2 + 1)))
      (ansl.getD (base + (2 + 3)) 0))) = ∑ i ∈ Finset.range 4,
      getRandElt (l0.map (ev φ)) 0 (u.take t.fl) ^ (i * (dKE t.fl 2 + 1)) * ev φ (ansl.getD (base + 2 + i) 0) := by
    simp only [ev_xor, ev_mulW φ _ _ _ hmod, ev_powW φ _ _ _ hmod, Finset.sum_range_succ, Finset.sum_range_zero,
      hγe, zero_add, add_assoc]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by rw [← hsum, h1]) h2
  · exact absurd (ev_inj φ t.fl _ _ hmod c.irr (getD_wlt ansl t.fl haw _) ls (h2.trans hsum.symm)) h1
  · rfl

theorem ite_01 (p : Prop) [Decidable p] : (if p then 1 else 0 : ℕ) ≤ 1 := by split <;> omega

theorem mul_le_cap01 {c : ℕ} (a x : ℕ) (ha : a ≤ 1) (hx : x ≤ 1) (hc : 1 ≤ c) : a * x ≤ c := by
  interval_cases a <;> interval_cases x <;> omega

theorem getD_drop' (l : List ℕ) (k i : ℕ) : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ## `D_{RS,>}` -/

/-- `dd = d − m(d_{f,2} + 1)`. -/
def ddE : E := .sub (.v 6) (.mul (mE (.v 6)) (.add dKEE (.k 1)))
/-- `base = m·q + q_L`. -/
def baseE : E := .add (.mul (mE (.v 6)) qEE) (.mul (oneE (.v 6)) (.mul (.k 2) qEE))
/-- One block run of `D_{RS,=}` (block `14`, saved answers in `8`). -/
def bsBody : S := .seq (.set 11 (.shr (.v 8) (.mul (.mul (.v 14) qEE) (.v 23)))) eqD

/-- **`D_{RS,>}`** (Algorithm 14), degree in `6`, `d < 2^f`. -/
def dGtP : S :=
  .seq (.set 5 baseE) (.seq (.set 2 (.mul (.v 2) bcE)) (.seq (.set 8 (.v 11)) (.seq (.loop 14 (mE (.v 6)) bsBody)
    (.ite (oneE (.v 6)) (.seq (.set 11 (.shr (.v 8) (.mul (.mul (mE (.v 6)) qEE) (.v 23)))) (.seq (.set 6 ddE) dLtP))
      .skip))))

theorem dGtP_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ) (d : ℕ)
    (c : QC G s l0 u) (hind : Indep (l0.map (ev φ))) (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ s.fl))
    (h6 : s.env 6 = d) (h11 : s.env 11 = packW s.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1)
    (hf : 2 < s.fl) (hdk : dKE s.fl 2 < d) (hdn : d < 2 ^ s.fl) :
    let t := evalS G dGtP s
    t.env 2 = s.env 2 * (if (vGtF (l0.map (ev φ)) 0 d).D u (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧
      t.env 2 ≤ 1 ∧ Wr dW s t := by
  intro t
  have A := c.atoms
  have hK := c.K
  have hN := c.N
  have hl0 := c.hl0
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hbig := A.big
  have hcK := cap_ge G
  have h64 : 1024 ≤ 2 ^ (8 * s.fl + 20) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 10 ≤ 8 * s.fl + 20 by omega))
  have hq := queryEq_le16 s.fl
  have hB : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, hl0]
  have hdb : (d + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap := by
    have e1 : (d + 4) * 2 ^ (8 * s.fl + 20) ≤ (2 ^ s.fl + 4) * 2 ^ (8 * s.fl + 20) := Nat.mul_le_mul_right _ (by omega)
    have e2 : 2 ^ s.fl + 4 ≤ 2 ^ (s.fl + 3) := by
      rw [pow_add]; have : 1 ≤ 2 ^ s.fl := Nat.one_le_two_pow; omega
    have e3 : 2 ^ (s.fl + 3) * 2 ^ (8 * s.fl + 20) = 2 ^ (9 * s.fl + 23) := by rw [← pow_add]; ring_nf
    have e4 : 2 ^ (9 * s.fl + 24) ≤ G.cap + 1 := pow_le_cap (by nlinarith)
    have e5 : (2 ^ s.fl + 4) * 2 ^ (8 * s.fl + 20) ≤ 2 ^ (s.fl + 3) * 2 ^ (8 * s.fl + 20) := Nat.mul_le_mul_right _ e2
    rw [show 9 * s.fl + 24 = (9 * s.fl + 23) + 1 by ring, pow_succ] at e4
    omega
  have hm4 := mKED_le4 (by omega : 2 ≤ s.fl) hdn
  have hqL16 : (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) ≤ 32 := by split_ifs <;> omega
  have hmq : mKED s.fl 2 d * queryEq T0 s.fl ≤ 64 := le_trans (Nat.mul_le_mul hm4 hq) (by norm_num)
  have hcap1 := A.c1
  -- the math side
  have hD : (vGtF (l0.map (ev φ)) 0 d).D u (fun i => ev φ (ansl.getD i 0)) =
      ((decide (ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 1) 0) = ∑ i ∈ Finset.range 4,
          getRandElt (l0.map (ev φ)) 0 (u.take s.fl) ^ (i * (dKE s.fl 2 + 1)) *
            ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 2 + i) 0)) &&
        (List.range (mKED s.fl 2 d)).all fun z => dEqR (l0.map (ev φ)) 0 u fun i => ev φ (ansl.getD (z * queryEq T0 s.fl + i) 0)) &&
        (if gtOne s.fl d = true then (vLtF (l0.map (ev φ)) 0 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))).D u
          (fun i => ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + i) 0)) else true)) := by
    simp only [vGtF, T0_η, hB, if_neg (show ¬ d ≥ 2 ^ s.fl by omega), gtOne, vLtF_query]
    rfl
  -- stage 1: the base
  have hm' : evalE G s (mE (.v 6)) = mKED s.fl 2 d := mE_eval A h6 hdb
  have ho' : evalE G s (oneE (.v 6)) = if gtOne s.fl d = true then 1 else 0 := oneE_eval A h6 hdb
  have hb : evalE G s baseE = mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) := by
    have hob : (if gtOne s.fl d = true then 1 else 0) * (2 * queryEq T0 s.fl) ≤ 32 := by
      by_cases hg : gtOne s.fl d = true <;> simp [hg] <;> omega
    have hob' : (if gtOne s.fl d = true then 1 else 0) * (2 * queryEq T0 s.fl) =
        if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0 := by split_ifs <;> simp
    rw [baseE, eE_add (eE_mul hm' A.q (by omega)) (eE_mul ho' (eE_mul (eE_k (by omega)) A.q (by omega))
      (by omega)) (by omega), hob']
  have c1 : QC G (s.setv 5 (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0))) l0 u := c.setv 5 _
  -- stage 2: the combination test
  have hbc := bcE_eval G (s.setv 5 (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0))) φ u l0 ansl (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0)) c1 hdom (by simp) (by simp [h11]) haw
    (show (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 6) * s.fl ≤ G.K by
      have : (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 6) * s.fl ≤ 102 * s.fl := Nat.mul_le_mul_right _ (by omega)
      nlinarith)
  set bc := decide (ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 1) 0) = ∑ i ∈ Finset.range 4,
          getRandElt (l0.map (ev φ)) 0 (u.take s.fl) ^ (i * (dKE s.fl 2 + 1)) *
            ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0) + 2 + i) 0)) with hbcd
  have hbc' : evalE G (s.setv 5 (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0))) (.mul (.v 2) bcE) = s.env 2 * if bc then 1 else 0 := by
    rw [eE_mul (show evalE G (s.setv 5 (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0))) (.v 2) = s.env 2 by simp [evalE]) hbc (mul_le_cap01 _ _ h2 (ite_01 _) hcap1)]
    simp only [hbcd, decide_eq_true_eq]; congr 1
  set s3 := ((s.setv 5 (mKED s.fl 2 d * queryEq T0 s.fl + (if gtOne s.fl d = true then 2 * queryEq T0 s.fl else 0))).setv 2 (s.env 2 * if bc then 1 else 0)).setv 8 (packW s.fl ansl) with hs3
  have c3 : QC G s3 l0 u := (c1.setv 2 _).setv 8 _
  have hs3e : evalS G (.seq (.set 5 baseE) (.seq (.set 2 (.mul (.v 2) bcE)) (.set 8 (.v 11)))) s = s3 := by
    simp only [evalS_seq, evalS_set]; rw [hb, hbc']; simp [hs3, evalE, h11]
  -- stage 3: the block runs
  set bsF : ℕ → Bool := fun z => dEqR (l0.map (ev φ)) 0 u fun i => ev φ (ansl.getD (z * queryEq T0 s.fl + i) 0) with hbsF
  have hloop := loop_inv (G := G) (i := 14) (n := mE (.v 6)) (body := bsBody) (s := s3)
    (fun z t => t.fp = s.fp ∧ t.fl = s.fl ∧ QC G t l0 u ∧ t.env 8 = packW s.fl ansl ∧ t.env 6 = d ∧
      t.env 2 = (s.env 2 * if bc then 1 else 0) * (if (List.range z).all bsF then 1 else 0) ∧ t.env 2 ≤ 1 ∧
      Wr dW s t) ⟨rfl, rfl, c3, by simp [hs3], by simp [hs3, h6], by simp [hs3], by
        rw [hs3]; exact mul_ite_le _ _ h2, by
        rw [hs3]; exact ((Wr.setv s (by decide) _).trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)⟩
    (by
      intro z hz t ⟨tfp, tfl, ct, t8, t6, t2, t2b, tw⟩
      have hmz : z < mKED s.fl 2 d := by
        have : evalE G s3 (mE (.v 6)) = mKED s.fl 2 d := mE_eval (c3.atoms : Atoms G s3 s.fl) (show evalE G s3 (.v 6) = d by simp [hs3, evalE, h6]) hdb
        rw [this] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
      have hzq : z * queryEq T0 s.fl ≤ 64 := le_trans (Nat.mul_le_mul (by omega : z ≤ 4) hq) (by norm_num)
      obtain ⟨env, out, fl, fp, ip, bad⟩ := t
      obtain rfl : fp = s.fp := tfp
      obtain rfl : fl = s.fl := tfl
      set t0 : FS := ⟨env, out, s.fl, s.fp, ip, bad⟩ with ht0
      have c0 : QC G (t0.setv 14 z) l0 u := ct.setv 14 z
      have A0 : Atoms G (t0.setv 14 z) s.fl := c0.atoms
      have hsh : evalE G (t0.setv 14 z) (.shr (.v 8) (.mul (.mul (.v 14) qEE) (.v 23))) =
          packW s.fl (ansl.drop (z * queryEq T0 s.fl)) := by
        rw [eE_shr (show evalE G (t0.setv 14 z) (.v 8) = packW s.fl ansl by simp [evalE, t8])
          (eE_mul (eE_mul (show evalE G (t0.setv 14 z) (.v 14) = z by simp [evalE]) A0.q (by omega))
            (show evalE G (t0.setv 14 z) (.v 23) = s.fl from c0.h23) (by
              have : z * queryEq T0 s.fl * s.fl ≤ 64 * s.fl := Nat.mul_le_mul_right _ (by omega)
              nlinarith)), packW_drop _ _ haw, mul_comm s.fl]
      have c1' : QC G ((t0.setv 14 z).setv 11 (packW s.fl (ansl.drop (z * queryEq T0 s.fl)))) l0 u := c0.setv 11 _
      obtain ⟨e2, e2b, ew⟩ := eqD_spec G ((t0.setv 14 z).setv 11 (packW s.fl (ansl.drop (z * queryEq T0 s.fl)))) φ u l0
        (ansl.drop (z * queryEq T0 s.fl)) c1' hind (by simp; rfl) (fun a ha => haw a (List.mem_of_mem_drop ha)) (by simpa using t2b)
      have hev : evalS G bsBody (t0.setv 14 z) = evalS G eqD ((t0.setv 14 z).setv 11 (packW s.fl (ansl.drop (z * queryEq T0 s.fl)))) := by
        rw [bsBody, evalS_seq, evalS_set, hsh]
      rw [hev]
      generalize ht1 : evalS G eqD ((t0.setv 14 z).setv 11 (packW s.fl (ansl.drop (z * queryEq T0 s.fl)))) = t1 at e2 e2b ew
      have hb1 : dEqR (l0.map (ev φ)) 0 u (fun i => ev φ ((ansl.drop (z * queryEq T0 s.fl)).getD i 0)) = bsF z := by
        simp only [hbsF, getD_drop']
      refine ⟨ew.fp, ew.fl, c1'.wr ew (by decide) ew.fp, by rw [ew.env 8 (by decide)]; simpa using t8,
        by rw [ew.env 6 (by decide)]; simpa using t6, ?_, e2b, ?_⟩
      · replace e2 : t1.env 2 = t0.env 2 * (if dEqR (l0.map (ev φ)) 0 u
            (fun i => ev φ ((ansl.drop (z * queryEq T0 s.fl)).getD i 0)) then 1 else 0) := e2
        rw [e2, hb1, t2, List.range_succ, List.all_append]
        by_cases ha : (List.range z).all bsF = true <;> by_cases hb : bsF z = true <;> simp [ha, hb]
      · exact ((tw.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans (ew.mono (by decide)))
  have hmN : min (evalE G s3 (mE (.v 6))) G.N = mKED s.fl 2 d := by
    have e : evalE G s3 (mE (.v 6)) = mKED s.fl 2 d :=
      mE_eval (c3.atoms : Atoms G s3 s.fl) (show evalE G s3 (.v 6) = d by simp [hs3, evalE, h6]) hdb
    rw [e]; exact min_eq_left (by omega)
  rw [hmN] at hloop
  generalize ht4 : evalS G (.loop 14 (mE (.v 6)) bsBody) s3 = t4 at hloop
  obtain ⟨t4fp, t4fl, c4, t48, t46, t42, t42b, t4w⟩ := hloop
  obtain ⟨env4, out4, fl4, fp4, ip4, bad4⟩ := t4
  obtain rfl : fp4 = s.fp := t4fp
  obtain rfl : fl4 = s.fl := t4fl
  set t4 : FS := ⟨env4, out4, s.fl, s.fp, ip4, bad4⟩ with ht4d
  have A4 : Atoms G t4 s.fl := c4.atoms
  have hm4' : evalE G t4 (mE (.v 6)) = mKED s.fl 2 d := mE_eval A4 (show evalE G t4 (.v 6) = d from t46) hdb
  have ho4 : evalE G t4 (oneE (.v 6)) = if gtOne s.fl d = true then 1 else 0 :=
    oneE_eval A4 (show evalE G t4 (.v 6) = d from t46) hdb
  have hpre : t = evalS G (.ite (oneE (.v 6)) (.seq (.set 11 (.shr (.v 8) (.mul (.mul (mE (.v 6)) qEE) (.v 23))))
      (.seq (.set 6 ddE) dLtP)) .skip) t4 := by
    show evalS G dGtP s = _
    rw [dGtP, ← ht4, ← hs3e]; simp only [evalS_seq]
  rw [hpre, evalS_ite, ho4, hD]
  by_cases hg : gtOne s.fl d = true
  · rw [if_pos hg, if_neg one_ne_zero, if_pos hg]
    have hsh : evalE G t4 (.shr (.v 8) (.mul (.mul (mE (.v 6)) qEE) (.v 23))) =
        packW s.fl (ansl.drop (mKED s.fl 2 d * queryEq T0 s.fl)) := by
      rw [eE_shr (show evalE G t4 (.v 8) = packW s.fl ansl from t48)
        (eE_mul (eE_mul hm4' A4.q (by omega)) (show evalE G t4 (.v 23) = s.fl from c4.h23) (by
            have : mKED s.fl 2 d * queryEq T0 s.fl * s.fl ≤ 64 * s.fl := Nat.mul_le_mul_right _ hmq
            nlinarith)), packW_drop _ _ haw, mul_comm s.fl]
    set al := ansl.drop (mKED s.fl 2 d * queryEq T0 s.fl) with hal
    have c5 : QC G (t4.setv 11 (packW s.fl al)) l0 u := c4.setv 11 _
    have A5 : Atoms G (t4.setv 11 (packW s.fl al)) s.fl := c5.atoms
    have h6' : evalE G (t4.setv 11 (packW s.fl al)) (.v 6) = d := by simp [evalE, ht4d]; exact t46
    have hdd : evalE G (t4.setv 11 (packW s.fl al)) ddE = d - mKED s.fl 2 d * (dKE s.fl 2 + 1) := by
      have hk := dKE_lt s.fl
      have : mKED s.fl 2 d * (dKE s.fl 2 + 1) ≤ d + 1 := Nat.div_mul_le_self _ _
      have := pf_le s.fl
      rw [ddE, eE_sub h6' (eE_mul (mE_eval A5 h6' hdb) (eE_add A5.k (eE_k hcap1) (by omega)) (by omega))]
    have c6 : QC G ((t4.setv 11 (packW s.fl al)).setv 6 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))) l0 u := c5.setv 6 _
    obtain ⟨f2, f2b, fw⟩ := dLtP_spec G ((t4.setv 11 (packW s.fl al)).setv 6 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1)))
      φ u l0 al (d - mKED s.fl 2 d * (dKE s.fl 2 + 1)) c6 hind hdom (by simp) (by simp; rfl) (fun a ha => haw a (List.mem_of_mem_drop ha))
      (by simpa [ht4d] using t42b)
    have hev : evalS G (.seq (.set 11 (.shr (.v 8) (.mul (.mul (mE (.v 6)) qEE) (.v 23)))) (.seq (.set 6 ddE) dLtP)) t4 =
        evalS G dLtP ((t4.setv 11 (packW s.fl al)).setv 6 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))) := by
      rw [evalS_seq, evalS_set, hsh, evalS_seq, evalS_set, hdd]
    rw [hev]
    generalize ht6 : evalS G dLtP ((t4.setv 11 (packW s.fl al)).setv 6 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))) = t6
      at f2 f2b fw
    replace f2 : t6.env 2 = t4.env 2 * (if (vLtF (l0.map (ev φ)) 0 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))).D u
        (fun i => ev φ (al.getD i 0)) then 1 else 0) := f2
    have hal' : (fun i => ev φ (al.getD i 0)) = fun i => ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + i) 0) := by
      funext i; rw [hal, getD_drop']
    rw [hal'] at f2
    refine ⟨?_, f2b, (((t4w.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans fw)⟩
    rw [f2, show t4.env 2 = _ from t42]
    cases bc <;> cases (List.range (mKED s.fl 2 d)).all bsF <;>
      cases (vLtF (l0.map (ev φ)) 0 (d - mKED s.fl 2 d * (dKE s.fl 2 + 1))).D u
        (fun i => ev φ (ansl.getD (mKED s.fl 2 d * queryEq T0 s.fl + i) 0)) <;> simp
  · rw [if_neg hg, if_pos rfl, evalS_skip, if_neg hg]
    refine ⟨?_, t42b, t4w⟩
    rw [show t4.env 2 = _ from t42]
    cases bc <;> cases (List.range (mKED s.fl 2 d)).all bsF <;> simp

/-! ## `D_RS`: the dispatch -/

/-- **`D_RS`** (Algorithm 13), degree in `6` (`V_{RS,>}` with `d ≥ 2^f` accepts). -/
def dRSP : S :=
  .ite smallE baseD (.ite (.lt (.v 6) dKEE) dLtP (.ite (.eq (.v 6) dKEE) eqD (.ite (.lt (.v 6) nSE) dGtP .skip)))

theorem dRSP_spec (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool) (l0 ansl : List ℕ) (d : ℕ)
    (c : QC G s l0 u) (hind : Indep (l0.map (ev φ))) (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ s.fl))
    (h6 : s.env 6 = d) (h11 : s.env 11 = packW s.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1) :
    let t := evalS G dRSP s
    t.env 2 = s.env 2 * (if (if trivB s.fl d then true else
      (vRSF (l0.map (ev φ)) 0 d).D u (fun i => ev φ (ansl.getD i 0))) then 1 else 0) ∧ t.env 2 ≤ 1 ∧ Wr dW s t := by
  intro t
  have A := c.atoms
  have hB : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, c.hl0]
  have h6' : evalE G s (.v 6) = d := h6
  have hs : evalE G s smallE = if s.fl < 3 then 1 else 0 :=
    eE_lt (eE_v 23 |>.trans c.h23) (eE_k (by have := A.big; have := Nat.lt_two_pow_self (n := 8 * s.fl + 20); omega))
  have hk := dKE_lt s.fl
  by_cases h1 : s.fl ≤ 2
  · have ht : t = evalS G baseD s := by
      show evalS G dRSP s = _
      rw [dRSP, evalS_ite, hs, if_pos (show s.fl < 3 by omega), if_neg one_ne_zero]
    rw [ht]
    obtain ⟨a, b, w⟩ := baseD_spec G s φ u l0 ansl d c hind h6 h11 haw h2 h1
    refine ⟨?_, b, w⟩
    rw [a]; simp only [trivB, show ¬ (2 < s.fl) by omega, false_and, decide_false, vRSF, hB, T0_η, if_pos h1]; rfl
  have hbr : ∀ X : S, evalS G (.ite smallE baseD X) s = evalS G X s := by
    intro X; rw [evalS_ite, hs, if_neg (show ¬ s.fl < 3 by omega), if_pos rfl]
  have hnt : ∀ (h : ¬ (2 ^ s.fl ≤ d)), trivB s.fl d = false := by
    intro h; simp [trivB]; omega
  by_cases h2' : d < dKE s.fl 2
  · have ht : t = evalS G dLtP s := by
      show evalS G dRSP s = _
      rw [dRSP, hbr, evalS_ite, eE_lt h6' A.k, if_pos h2', if_neg one_ne_zero]
    rw [ht]
    obtain ⟨a, b, w⟩ := dLtP_spec G s φ u l0 ansl d c hind hdom h6 h11 haw h2
    refine ⟨?_, b, w⟩
    rw [a, hnt (by omega)]; simp only [vRSF, hB, T0_η, if_neg h1, if_pos h2', Bool.false_eq_true, if_false]
  by_cases h3 : d = dKE s.fl 2
  · have ht : t = evalS G eqD s := by
      show evalS G dRSP s = _
      rw [dRSP, hbr, evalS_ite, eE_lt h6' A.k, if_neg h2', if_pos rfl, evalS_ite, eE_eq h6' A.k, if_pos h3,
        if_neg one_ne_zero]
    rw [ht]
    obtain ⟨a, b, w⟩ := eqD_spec G s φ u l0 ansl c hind h11 haw h2
    refine ⟨?_, b, w.mono (by decide)⟩
    rw [a, hnt (by omega)]; simp only [vRSF, vEqF, hB, T0_η, if_neg h1, if_neg h2', if_pos h3, Bool.false_eq_true,
      if_false]
  have hpre : ∀ X : S, evalS G dRSP s = evalS G (.ite (.lt (.v 6) nSE) dGtP .skip) s := by
    intro X
    rw [dRSP, hbr, evalS_ite, eE_lt h6' A.k, if_neg h2', if_pos rfl, evalS_ite, eE_eq h6' A.k, if_neg h3, if_pos rfl]
  by_cases h4 : d < 2 ^ s.fl
  · have ht : t = evalS G dGtP s := by
      show evalS G dRSP s = _
      rw [hpre .skip, evalS_ite, eE_lt h6' A.n, if_pos h4, if_neg one_ne_zero]
    rw [ht]
    obtain ⟨a, b, w⟩ := dGtP_spec G s φ u l0 ansl d c hind hdom h6 h11 haw h2 (by omega) (by omega) h4
    refine ⟨?_, b, w⟩
    rw [a, hnt (by omega)]; simp only [vRSF, hB, T0_η, if_neg h1, if_neg h2', if_neg h3, Bool.false_eq_true, if_false]
  · have ht : t = s := by
      show evalS G dRSP s = _
      rw [hpre .skip, evalS_ite, eE_lt h6' A.n, if_neg h4, if_pos rfl, evalS_skip]
    rw [ht]
    have htr : trivB s.fl d = true := by simp [trivB]; omega
    refine ⟨by rw [if_pos htr]; simp, h2, Wr.refl _ _⟩

/-! ## The `Z_H` test of `V_VRS` and the decision of a sub-verifier run -/

/-- **The `Z_H` test** at the effective positions `qcI + 1`, `qcI + 2` (basis words `bhE`, length `lhE`, offset `ohE`). -/
def vcP (bhE lhE ohE : E) : S :=
  .seq (.set 5 (qcIE (.v 6))) (.seq (.set 26 bhE) (.seq (.set 27 lhE) (.seq (zfP (.fadd gwE ohE))
    (.set 2 (.mul (.v 2) (.eq (aE 1) (.fmul (.v 28) (aE 2))))))))

theorem vcP_spec (bhE lhE ohE : E) (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool)
    (l0 ansl bhw : List ℕ) (ohw di : ℕ) (c : QC G s l0 u) (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ s.fl))
    (h6 : s.env 6 = di) (h11 : s.env 11 = packW s.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1)
    (hdb : (di + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap) (hbw : ∀ a ∈ bhw, a < 2 ^ s.fl) (how : ohw < 2 ^ s.fl)
    (hbe : ∀ t : FS, Wr [5, 26] s t → evalE G t bhE = packW s.fl bhw)
    (hle : ∀ t : FS, Wr [5, 26] s t → evalE G t lhE = bhw.length)
    (hoe : ∀ t : FS, Wr [5, 26, 27] s t → evalE G t ohE = ohw)
    (hKb : s.fl * (bhw.length + 1) + 1 ≤ G.K) (hNb : bhw.length + 1 ≤ G.N) (hqb : (qcI s.fl di + 3) * s.fl ≤ G.K) :
    let t := evalS G (vcP bhE lhE ohE) s
    t.env 2 = s.env 2 * (if vrsCheck (l0.map (ev φ)) 0 (bhw.map (ev φ)) (ev φ ohw) u (fun i => ev φ (ansl.getD i 0))
      (qcI s.fl di) then 1 else 0) ∧ t.env 2 ≤ 1 ∧ Wr ([5, 26, 27] ++ zfW ++ [2]) s t := by
  intro t
  have A := c.atoms
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hq := qcIE_eval c.h23 A (show evalE G s (.v 6) = di from h6) hdb
  set q := qcI s.fl di with hqd
  have w1 : Wr [5, 26] s (s.setv 5 q) := Wr.setv s (by decide) _
  set b := packW s.fl bhw with hb
  have w2 : Wr [5, 26] s ((s.setv 5 q).setv 26 b) := w1.trans (Wr.setv _ (by decide) _)
  have w3 : Wr [5, 26, 27] s (((s.setv 5 q).setv 26 b).setv 27 bhw.length) :=
    (w2.mono (by decide)).trans (Wr.setv _ (by decide) _)
  set s3 := ((s.setv 5 q).setv 26 b).setv 27 bhw.length with hs3
  have c3 : QC G s3 l0 u := ((c.setv 5 _).setv 26 _).setv 27 _
  have A3 : Atoms G s3 s.fl := c3.atoms
  have hα : evalE G s3 gwE = bitsValue u % 2 ^ s.fl := eE_md (show evalE G s3 (.v 42) = bitsValue u from c3.h42) A3.n
  have hαl : bitsValue u % 2 ^ s.fl < 2 ^ s.fl := Nat.mod_lt _ (by positivity)
  have hy := eE_fadd hα (hoe s3 w3) hαl how
  obtain ⟨z1, z2, zw⟩ := zfP_spec G s3 φ (.fadd gwE ohE) bhw _ hbw hy (Nat.xor_lt_two_pow hαl how)
    (by simp [hs3, hb]) (by simp [hs3]) c3.h23 c3.ok hKb hNb
  generalize ht4 : evalS G (zfP (.fadd gwE ohE)) s3 = t4 at z1 z2 zw
  have c4 : QC G t4 l0 u := c3.wr zw (by decide) zw.fp
  have hfl4 : t4.fl = s.fl := zw.fl
  have hfp4 : t4.fp = s.fp := zw.fp
  replace z2 : ev φ (t4.env 28) = zFast (bhw.map (ev φ)) (ev φ ((bitsValue u % 2 ^ s.fl) ^^^ ohw)) := z2
  replace z1 : t4.env 28 < 2 ^ s.fl := z1
  have t5 : t4.env 5 = q := by rw [zw.env 5 (by decide)]; simp [hs3]
  have t11 : t4.env 11 = packW s.fl ansl := by rw [zw.env 11 (by decide)]; simp [hs3, h11]
  have t2 : t4.env 2 = s.env 2 := by rw [zw.env 2 (by decide)]; simp [hs3]
  have hcK := cap_ge G
  have ha : ∀ k, k ≤ 2 → evalE G t4 (aE k) = ansl.getD (q + k) 0 := by
    intro k hk
    refine getW_eval G t4 11 _ s.fl _ ansl haw t11 (c4.h23.trans hfl4) (eE_add (eE_v 5 |>.trans t5)
      (eE_k (by have := c4.atoms.big; have := Nat.lt_two_pow_self (n := 8 * t4.fl + 20); omega)) ?_) ?_ (by omega)
    · have : (q + 3) * s.fl ≥ q + 3 := Nat.le_mul_of_pos_right _ hf1
      omega
    · exact le_trans (Nat.mul_le_mul_right _ (by omega)) hqb
  have hm : evalE G t4 (.fmul (.v 28) (aE 2)) = mulW s.fp s.fl (t4.env 28) (ansl.getD (q + 2) 0) := by
    show mulW t4.fp t4.fl (t4.env 28 % 2 ^ t4.fl) (evalE G t4 (aE 2) % 2 ^ t4.fl) = _
    rw [ha 2 le_rfl, hfl4, hfp4, Nat.mod_eq_of_lt z1, Nat.mod_eq_of_lt (getD_wlt ansl s.fl haw _)]
  have hev : t = t4.setv 2 (t4.env 2 * if ansl.getD (q + 1) 0 = mulW s.fp s.fl (t4.env 28) (ansl.getD (q + 2) 0)
      then 1 else 0) := by
    show evalS G (vcP bhE lhE ohE) s = _
    have e1 : evalE G s (qcIE (.v 6)) = q := hq
    have e2 : evalE G (s.setv 5 q) bhE = b := hbe _ w1
    have e3 : evalE G ((s.setv 5 q).setv 26 b) lhE = bhw.length := hle _ w2
    rw [vcP, evalS_seq, evalS_set, e1, evalS_seq, evalS_set, e2, evalS_seq, evalS_set, e3, evalS_seq, ← hs3, ht4,
      evalS_set, eE_mul (eE_v 2) (eE_eq (ha 1 (by omega)) hm) (by
        rw [t2]; exact mul_le_cap01 _ _ h2 (ite_01 _) A.c1)]
  rw [hev]
  have hcheck : (ansl.getD (q + 1) 0 = mulW s.fp s.fl (t4.env 28) (ansl.getD (q + 2) 0)) ↔
      vrsCheck (l0.map (ev φ)) 0 (bhw.map (ev φ)) (ev φ ohw) u (fun i => ev φ (ansl.getD i 0)) q = true := by
    simp only [vrsCheck, decide_eq_true_eq, List.length_map, c.hl0, dom_rand φ hdom, bitsValue_take, Nat.mod_mod]
    rw [← ev_xor, ← z2, ← ev_mulW φ _ _ _ hmod]
    exact ⟨fun h => by rw [h], fun h => ev_inj φ s.fl _ _ hmod c.irr (getD_wlt ansl s.fl haw _) (mulW_lt _ _ _ _) h⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [FS.setv_env, Function.update_self, t2]
    by_cases h : ansl.getD (q + 1) 0 = mulW s.fp s.fl (t4.env 28) (ansl.getD (q + 2) 0)
    · rw [if_pos h, if_pos (hcheck.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hcheck.2 h'))]
  · simp only [FS.setv_env, Function.update_self, t2]; exact mul_le_cap01 _ _ h2 (ite_01 _) (by omega)
  · exact ((w3.mono (by decide)).trans (zw.mono (by decide))).trans (Wr.setv _ (by decide) _)

/-- **The decision of a sub-verifier run** (`TimeBlocks.outD`). -/
def dOutP (v : Bool) (bhE lhE ohE : E) : S := .seq (if v then vcP bhE lhE ohE else .skip) dRSP

theorem dOutP_spec (v : Bool) (bhE lhE ohE : E) (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F) (u : List Bool)
    (l0 ansl bhw : List ℕ) (ohw di : ℕ) (c : QC G s l0 u) (hind : Indep (l0.map (ev φ)))
    (hdom : ∀ v, sel (l0.map (ev φ)) v = ev φ (v % 2 ^ s.fl))
    (h6 : s.env 6 = di) (h11 : s.env 11 = packW s.fl ansl) (haw : ∀ a ∈ ansl, a < 2 ^ s.fl) (h2 : s.env 2 ≤ 1)
    (hv : v = true → (di + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap ∧ (∀ a ∈ bhw, a < 2 ^ s.fl) ∧ ohw < 2 ^ s.fl ∧
      (∀ t : FS, Wr [5, 26] s t → evalE G t bhE = packW s.fl bhw) ∧
      (∀ t : FS, Wr [5, 26] s t → evalE G t lhE = bhw.length) ∧
      (∀ t : FS, Wr [5, 26, 27] s t → evalE G t ohE = ohw) ∧
      s.fl * (bhw.length + 1) + 1 ≤ G.K ∧ bhw.length + 1 ≤ G.N ∧ (qcI s.fl di + 3) * s.fl ≤ G.K) :
    let t := evalS G (dOutP v bhE lhE ohE) s
    t.env 2 = s.env 2 * (if outD v (l0.map (ev φ)) 0 (bhw.map (ev φ)) (ev φ ohw) di u
      (fun i => ev φ (ansl.getD i 0)) then 1 else 0) ∧ t.env 2 ≤ 1 ∧ Wr dW s t := by
  intro t
  have hB : (l0.map (ev φ)).length = s.fl := by rw [List.length_map, c.hl0]
  cases v with
  | false =>
    have ht : t = evalS G dRSP s := by show evalS G (dOutP false bhE lhE ohE) s = _; simp [dOutP]
    obtain ⟨a, b, w⟩ := dRSP_spec G s φ u l0 ansl di c hind hdom h6 h11 haw h2
    rw [ht]; refine ⟨?_, b, w⟩
    rw [a]; simp only [outD, hB, Bool.false_eq_true, if_false, Bool.true_and]
  | true =>
    obtain ⟨hdb, hbw, how, hbe, hle, hoe, hKb, hNb, hqb⟩ := hv rfl
    obtain ⟨a1, b1, w1⟩ := vcP_spec G bhE lhE ohE s φ u l0 ansl bhw ohw di c hdom h6 h11 haw h2 hdb hbw how hbe hle
      hoe hKb hNb hqb
    have ht : t = evalS G dRSP (evalS G (vcP bhE lhE ohE) s) := by
      show evalS G (dOutP true bhE lhE ohE) s = _; simp [dOutP]
    generalize ht1 : evalS G (vcP bhE lhE ohE) s = t1 at a1 b1 w1 ht
    have c1 : QC G t1 l0 u := c.wr w1 (by decide) w1.fp
    have e6 : t1.env 6 = di := by rw [w1.env 6 (by decide), h6]
    have e11 : t1.env 11 = packW s.fl ansl := by rw [w1.env 11 (by decide), h11]
    have hfl := w1.fl
    have hfp := w1.fp
    obtain ⟨env, out, fl, fp, ip, bad⟩ := t1
    obtain rfl : fp = s.fp := hfp
    obtain rfl : fl = s.fl := hfl
    obtain ⟨a2, b2, w2⟩ := dRSP_spec G ⟨env, out, s.fl, s.fp, ip, bad⟩ φ u l0 ansl di c1 hind hdom e6 e11 haw b1
    rw [ht]; refine ⟨?_, b2, (w1.mono (by decide)).trans w2⟩
    rw [a2, a1]
    simp only [outD, hB, if_true]
    cases vrsCheck (l0.map (ev φ)) 0 (bhw.map (ev φ)) (ev φ ohw) u (fun i => ev φ (ansl.getD i 0)) (qcI s.fl di) <;>
      cases (if trivB s.fl di = true then true else
        (vRSF (l0.map (ev φ)) 0 di).D u (fun i => ev φ (ansl.getD i 0))) <;> simp [mul_assoc]

end NearCubicGates.Adapters.ShortPCP.Machines.FL
