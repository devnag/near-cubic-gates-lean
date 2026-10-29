import SourceAdapters.ShortPCP.Machines.FLangQ
import SourceAdapters.ShortPCP.TimeBlocks

/-!
# Single-run time, machine layer 23: the parameters of a sub-verifier run as expressions

In the sub-verifier computation of `thm:short-pcp-ours`, Step 2, “Time and queries”, this module evaluates `query`, `length`, `rand` of `V_RS` on the domain
`F` (`κ = f` in `23`) at the degree `d` (an expression), in the closed forms `qRS`, `lRS`, `rRS` of
`TimeBlocks.lean`, from the tables in `17`/`18` (`TblRep`). Branches are the expression `iteE c a b`
(`c ∈ {0, 1}`); each evaluation lemma needs only the value of the branch taken (`iteE_pos`, `iteE_neg`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13

variable {G : Glob} {s : FS}

/-- `if c ≠ 0 then a else b` for `c ∈ {0, 1}`. -/
def iteE (c a b : E) : E := .add (.mul c a) (.mul (.sub (.k 1) c) b)

theorem iteE_pos {c a b : E} {x : ℕ} (h1 : 1 ≤ G.cap) (hc : evalE G s c = 1) (ha : evalE G s a = x)
    (hx : x ≤ G.cap) : evalE G s (iteE c a b) = x := by
  rw [iteE, eE_add (eE_mul hc ha (by omega)) (eE_mul (eE_sub (eE_k h1) hc) rfl (by simp)) (by simp; omega)]
  simp

theorem iteE_neg {c a b : E} {y : ℕ} (h1 : 1 ≤ G.cap) (hc : evalE G s c = 0) (hb : evalE G s b = y)
    (hy : y ≤ G.cap) : evalE G s (iteE c a b) = y := by
  rw [iteE, eE_add (eE_mul hc rfl (by simp)) (eE_mul (eE_sub (eE_k h1) hc) hb (by simpa)) (by simpa)]
  simp

/-! ## The expressions (`f` in `23`, `d` an expression) -/

/-- `d_{f,2} = 2^f / 4 − 1`. -/
def dKEE : E := .sub (.div nSE (.k 4)) (.k 1)
/-- `m = (d + 1)/(d_{f,2} + 1)`. -/
def mE (d : E) : E := .div (.add d (.k 1)) (.add dKEE (.k 1))
/-- The flag `m·(d_{f,2}+1) < d + 1`. -/
def oneE (d : E) : E := .lt (.mul (mE d) (.add dKEE (.k 1))) (.add d (.k 1))
/-- `f ≤ 2`. -/
def smallE : E := .lt (.v 23) (.k 3)
def gtqE (d : E) : E := .add (.add (.mul (mE d) qEE) (.mul (oneE d) (.mul (.k 2) qEE))) (.k 5)
/-- `query` of `V_RS`. -/
def qRSE (d : E) : E := iteE smallE nSE (iteE (.lt d dKEE) (.mul (.k 2) qEE) (iteE (.eq d dKEE) qEE (gtqE d)))
def gtlE (d : E) : E := .add (.mul (mE d) (.add nSE lEE)) (.mul (oneE d) (.add nSE (.mul (.k 2) lEE)))
/-- `length` of `V_RS`. -/
def lRSE (d : E) : E := iteE smallE (.k 0) (iteE (.lt d dKEE) (.mul (.k 2) lEE) (iteE (.eq d dKEE) lEE (gtlE d)))
/-- `rand_{RS,=}(f)` from the table. -/
def rEE : E := getT (.add (.add (.v 23) (.k 1)) (.v 23))
/-- `rand` of `V_RS`. -/
def rRSE (d : E) : E := iteE smallE (.k 0) (iteE (.lt dKEE d) (iteE (.lt rEE (.v 23)) (.v 23) rEE) rEE)
/-- `2 < f ∧ 2^f ≤ d`. -/
def trivE (d : E) : E := .mul (.lt (.k 2) (.v 23)) (.lt (.sub nSE (.k 1)) d)
/-- The number of effective queries of the `V_RS` part. -/
def qcIE (d : E) : E := iteE (trivE d) (.k 0) (qRSE d)

/-! ## Evaluation -/

theorem TblRep.rnd {t : FS} {f : ℕ} (h : TblRep t f) {e : E} (he : evalE G t e = f)
    (hK : 2 * ((f + 1) * (8 * f + 16)) + 1 ≤ G.K) : evalE G t (getT (.add (.add e (.k 1)) e)) = randEq T0 f := by
  obtain ⟨h17, l, h18, hl, hv⟩ := h
  have hc := cap_ge G
  have e0 : f + 1 ≤ (f + 1) * (8 * f + 16) := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : 2 * ((f + 1) * (8 * f + 16)) = (f + 1 + f) * (8 * f + 16) + (8 * f + 16) := by ring
  rw [getT_eval G t _ (8 * f + 16) (f + 1 + f) l hl h18 h17
    (eE_add (eE_add he (eE_k (by omega)) (by omega)) he (by omega)) (by omega) (by omega)]
  exact (hv f le_rfl).2

/-- The atoms at a state with `23 = f` and the tables. -/
structure Atoms (G : Glob) (s : FS) (f : ℕ) : Prop where
  n : evalE G s nSE = 2 ^ f
  q : evalE G s qEE = queryEq T0 f
  l : evalE G s lEE = lengthEq T0 f
  r : evalE G s rEE = randEq T0 f
  k : evalE G s dKEE = dKE f 2
  c1 : 1 ≤ G.cap
  big : 2 ^ (8 * f + 20) ≤ G.cap

theorem atoms {f : ℕ} (h23 : s.env 23 = f) (htb : TblRep s f) (hf : 1 ≤ f)
    (hK : 2 * ((f + 1) * (8 * f + 16)) + 1 ≤ G.K) : Atoms G s f := by
  have hc := cap_ge G
  have hK1 : (f + 1) * (8 * f + 16) + 1 ≤ G.K := by omega
  have e1 : 8 * f + 21 ≤ (f + 1) * (8 * f + 16) := by nlinarith
  have hn := nSE_eval G h23 (by omega)
  refine ⟨hn, qEE_eval G h23 (by omega), lEE_eval G h23 htb hK1, ?_, ?_, by omega, ?_⟩
  · exact htb.rnd (eE_v 23 |>.trans h23) hK
  · rw [dKEE, eE_sub (eE_div hn (eE_k (by omega))) (eE_k (by omega))]; rfl
  · have := pow_le_cap (G := G) (a := 8 * f + 21) (by omega)
    rw [pow_succ] at this; omega

theorem queryEq_le16 (f : ℕ) : queryEq T0 f ≤ 16 := by
  rw [queryEq_eq]; exact (Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)).trans (by norm_num)

theorem nl_le (f : ℕ) : 2 ^ f + 2 * lengthEq T0 f ≤ 2 ^ (8 * f + 18) := by
  have h1 := lengthEq_lt f
  have h2 : 2 ^ f ≤ 2 ^ (8 * f + 16) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (8 * f + 18) = 4 * 2 ^ (8 * f + 16) := by rw [show 8 * f + 18 = 8 * f + 16 + 2 by omega, pow_add]; ring
  omega

theorem mKED_le (f d : ℕ) : mKED f 2 d ≤ d + 1 := Nat.div_le_self _ _

theorem pf_le (f : ℕ) : 2 ^ f ≤ 2 ^ (8 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem dv_le {f dv : ℕ} (hb : (dv + 4) * 2 ^ (8 * f + 20) ≤ G.cap) : dv + 4 ≤ G.cap := by
  have : 1 ≤ 2 ^ (8 * f + 20) := Nat.one_le_two_pow
  have := Nat.le_mul_of_pos_right (dv + 4) this; omega

theorem gt_le (f dv : ℕ) : mKED f 2 dv * (2 ^ f + lengthEq T0 f) + (2 ^ f + 2 * lengthEq T0 f) ≤
    (dv + 4) * 2 ^ (8 * f + 20) := by
  have h1 := mKED_le f dv
  have h2 := nl_le f
  have h3 : 2 ^ (8 * f + 20) = 4 * 2 ^ (8 * f + 18) := by
    rw [show 8 * f + 20 = 8 * f + 18 + 2 by omega, pow_add]; ring
  have h4 : mKED f 2 dv * (2 ^ f + lengthEq T0 f) ≤ (dv + 1) * 2 ^ (8 * f + 18) :=
    Nat.mul_le_mul h1 (by omega)
  have h5 : (dv + 4) * (4 * 2 ^ (8 * f + 18)) = (dv + 1) * 2 ^ (8 * f + 18) + (3 * dv + 15) * 2 ^ (8 * f + 18) := by
    ring
  have h6 : 2 ^ (8 * f + 18) ≤ (3 * dv + 15) * 2 ^ (8 * f + 18) := Nat.le_mul_of_pos_left _ (by omega)
  rw [h3, h5]; omega

theorem gtq_le (f dv : ℕ) : mKED f 2 dv * queryEq T0 f + 2 * queryEq T0 f + 1 + 4 ≤ (dv + 4) * 2 ^ (8 * f + 20) := by
  have h1 := mKED_le f dv
  have h2 := queryEq_le16 f
  have h3 : 16 ≤ 2 ^ (8 * f + 20) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : mKED f 2 dv * queryEq T0 f ≤ (dv + 1) * 16 := Nat.mul_le_mul h1 h2
  have h5 : (dv + 4) * 16 ≤ (dv + 4) * 2 ^ (8 * f + 20) := Nat.mul_le_mul_left _ h3
  omega

section Params

variable {f : ℕ} (h23 : s.env 23 = f) (A : Atoms G s f) {d : E} {dv : ℕ} (hd : evalE G s d = dv)
  (hb : (dv + 4) * 2 ^ (8 * f + 20) ≤ G.cap)
include h23 A hd hb

omit h23 in
theorem mE_eval : evalE G s (mE d) = mKED f 2 dv := by
  have hk := dKE_lt f
  have := pf_le f
  have := dv_le hb
  have := A.big
  rw [mE, eE_div (eE_add hd (eE_k A.c1) (by omega)) (eE_add A.k (eE_k A.c1) (by omega)), mKED]

omit h23 in
theorem oneE_eval : evalE G s (oneE d) = if gtOne f dv then 1 else 0 := by
  have hk := dKE_lt f
  have := pf_le f
  have := dv_le hb
  have := A.big
  have hm : mKED f 2 dv * (dKE f 2 + 1) ≤ dv + 1 := Nat.div_mul_le_self _ _
  rw [oneE, eE_lt (eE_mul (mE_eval A hd hb) (eE_add A.k (eE_k A.c1) (by omega)) (by omega))
    (eE_add hd (eE_k A.c1) (by omega))]
  simp [gtOne]

theorem qRSE_eval : evalE G s (qRSE d) = qRS f dv := by
  have hk := dKE_lt f
  have hp := pf_le f
  have hcap := dv_le hb
  have hbig := A.big
  have hq := queryEq_le16 f
  have g1 := gtq_le f dv
  have hm := mE_eval A hd hb
  have ho := oneE_eval A hd hb
  have hs : evalE G s smallE = if f < 3 then 1 else 0 := eE_lt (eE_v 23 |>.trans h23) (eE_k (by omega))
  have h4 : mKED f 2 dv * queryEq T0 f ≤ G.cap := by omega
  have hgt : evalE G s (gtqE d) =
      mKED f 2 dv * queryEq T0 f + (if gtOne f dv then 2 * queryEq T0 f else 0) + 1 + 4 := by
    have e2 : evalE G s (.mul (.k 2) qEE) = 2 * queryEq T0 f := eE_mul (eE_k (by omega)) A.q (by omega)
    rw [gtqE, eE_add (eE_add (eE_mul hm A.q h4) (eE_mul ho e2 (by split_ifs <;> omega)) (by split_ifs <;> omega))
      (eE_k (by omega)) (by split_ifs <;> omega)]
    split_ifs <;> ring
  have hv3 : evalE G s (iteE (.eq d dKEE) qEE (gtqE d)) = if dv = dKE f 2 then queryEq T0 f else
      mKED f 2 dv * queryEq T0 f + (if gtOne f dv then 2 * queryEq T0 f else 0) + 1 + 4 := by
    by_cases h : dv = dKE f 2
    · rw [if_pos h]; exact iteE_pos A.c1 (by rw [eE_eq hd A.k, if_pos h]) A.q (by omega)
    · rw [if_neg h]; exact iteE_neg A.c1 (by rw [eE_eq hd A.k, if_neg h]) hgt (by split_ifs <;> omega)
  have hv2 : evalE G s (iteE (.lt d dKEE) (.mul (.k 2) qEE) (iteE (.eq d dKEE) qEE (gtqE d))) =
      if dv < dKE f 2 then 2 * queryEq T0 f else if dv = dKE f 2 then queryEq T0 f else
      mKED f 2 dv * queryEq T0 f + (if gtOne f dv then 2 * queryEq T0 f else 0) + 1 + 4 := by
    by_cases h : dv < dKE f 2
    · rw [if_pos h]
      exact iteE_pos A.c1 (by rw [eE_lt hd A.k, if_pos h]) (eE_mul (eE_k (by omega)) A.q (by omega)) (by omega)
    · rw [if_neg h]; exact iteE_neg A.c1 (by rw [eE_lt hd A.k, if_neg h]) hv3 (by split_ifs <;> omega)
  unfold qRSE qRS
  by_cases h1 : f ≤ 2
  · rw [if_pos h1]; exact iteE_pos A.c1 (by rw [hs, if_pos (by omega)]) A.n (by omega)
  · rw [if_neg h1]
    exact iteE_neg A.c1 (by rw [hs, if_neg (by omega)]) hv2 (by split_ifs <;> omega)

theorem lRSE_eval : evalE G s (lRSE d) = lRS f dv := by
  have hk := dKE_lt f
  have hp := pf_le f
  have hcap := dv_le hb
  have hbig := A.big
  have g1 := gt_le f dv
  have hl := lengthEq_lt f
  have hnl := nl_le f
  have h18 : 2 ^ (8 * f + 18) ≤ 2 ^ (8 * f + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm := mE_eval A hd hb
  have ho := oneE_eval A hd hb
  have hs : evalE G s smallE = if f < 3 then 1 else 0 := eE_lt (eE_v 23 |>.trans h23) (eE_k (by omega))
  have e2 : evalE G s (.mul (.k 2) lEE) = 2 * lengthEq T0 f := eE_mul (eE_k (by omega)) A.l (by omega)
  have hgt : evalE G s (gtlE d) =
      mKED f 2 dv * (2 ^ f + lengthEq T0 f) + (if gtOne f dv then 2 ^ f + 2 * lengthEq T0 f else 0) := by
    rw [gtlE, eE_add (eE_mul hm (eE_add A.n A.l (by omega)) (by omega))
      (eE_mul ho (eE_add A.n e2 (by omega)) (by split_ifs <;> omega)) (by split_ifs <;> omega)]
    split_ifs <;> ring
  have hv3 : evalE G s (iteE (.eq d dKEE) lEE (gtlE d)) = if dv = dKE f 2 then lengthEq T0 f else
      mKED f 2 dv * (2 ^ f + lengthEq T0 f) + (if gtOne f dv then 2 ^ f + 2 * lengthEq T0 f else 0) := by
    by_cases h : dv = dKE f 2
    · rw [if_pos h]; exact iteE_pos A.c1 (by rw [eE_eq hd A.k, if_pos h]) A.l (by omega)
    · rw [if_neg h]; exact iteE_neg A.c1 (by rw [eE_eq hd A.k, if_neg h]) hgt (by split_ifs <;> omega)
  have hv2 : evalE G s (iteE (.lt d dKEE) (.mul (.k 2) lEE) (iteE (.eq d dKEE) lEE (gtlE d))) =
      if dv < dKE f 2 then 2 * lengthEq T0 f else if dv = dKE f 2 then lengthEq T0 f else
      mKED f 2 dv * (2 ^ f + lengthEq T0 f) + (if gtOne f dv then 2 ^ f + 2 * lengthEq T0 f else 0) := by
    by_cases h : dv < dKE f 2
    · rw [if_pos h]; exact iteE_pos A.c1 (by rw [eE_lt hd A.k, if_pos h]) e2 (by omega)
    · rw [if_neg h]; exact iteE_neg A.c1 (by rw [eE_lt hd A.k, if_neg h]) hv3 (by split_ifs <;> omega)
  unfold lRSE lRS
  by_cases h1 : f ≤ 2
  · rw [if_pos h1]; exact iteE_pos A.c1 (by rw [hs, if_pos (by omega)]) (eE_k (by omega)) (by omega)
  · rw [if_neg h1]
    exact iteE_neg A.c1 (by rw [hs, if_neg (by omega)]) hv2 (by split_ifs <;> omega)

theorem rRSE_eval : evalE G s (rRSE d) = rRS f dv := by
  have hk := dKE_lt f
  have hp := pf_le f
  have hcap := dv_le hb
  have hbig := A.big
  have hr := randEq_le f
  have hr' : randEq T0 f ≤ G.cap := by
    have : 4 * f ≤ 2 ^ (8 * f + 20) := by
      have := Nat.lt_two_pow_self (n := 8 * f + 20); omega
    omega
  have hf : f ≤ G.cap := by have := Nat.lt_two_pow_self (n := 8 * f + 20); omega
  have hs : evalE G s smallE = if f < 3 then 1 else 0 := eE_lt (eE_v 23 |>.trans h23) (eE_k (by omega))
  have hmx : evalE G s (iteE (.lt rEE (.v 23)) (.v 23) rEE) = max (randEq T0 f) f := by
    by_cases h : randEq T0 f < f
    · rw [max_eq_right h.le]
      exact iteE_pos A.c1 (by rw [eE_lt A.r (eE_v 23 |>.trans h23), if_pos h]) (eE_v 23 |>.trans h23) hf
    · rw [max_eq_left (by omega)]
      exact iteE_neg A.c1 (by rw [eE_lt A.r (eE_v 23 |>.trans h23), if_neg h]) A.r hr'
  unfold rRSE rRS
  by_cases h1 : f ≤ 2
  · rw [if_pos h1]; exact iteE_pos A.c1 (by rw [hs, if_pos (by omega)]) (eE_k (by omega)) (by omega)
  · rw [if_neg h1]
    refine iteE_neg A.c1 (by rw [hs, if_neg (by omega)]) ?_ (by split_ifs <;> omega)
    by_cases h2 : dKE f 2 < dv
    · rw [if_neg (by omega), if_neg (by omega)]
      exact iteE_pos A.c1 (by rw [eE_lt A.k hd, if_pos h2]) hmx (by simp; omega)
    · have e : (if dv < dKE f 2 then randEq T0 f else if dv = dKE f 2 then randEq T0 f else
          max (randEq T0 f) f) = randEq T0 f := by split_ifs <;> first | rfl | omega
      rw [e]; exact iteE_neg A.c1 (by rw [eE_lt A.k hd, if_neg h2]) A.r hr'

theorem trivE_eval : evalE G s (trivE d) = if trivB f dv then 1 else 0 := by
  have hcap := dv_le hb
  have hp := pf_le f
  have hbig := A.big
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rw [trivE, eE_mul (eE_lt (eE_k (by omega)) (eE_v 23 |>.trans h23)) (eE_lt (eE_sub A.n (eE_k A.c1)) hd)
    (by split_ifs <;> omega)]
  simp only [trivB]
  by_cases a : 2 < f <;> by_cases b : 2 ^ f - 1 < dv <;> simp [a, b] <;> omega

theorem qcIE_eval : evalE G s (qcIE d) = qcI f dv := by
  have hcap := dv_le hb
  have g1 := gtq_le f dv
  have hp := pf_le f
  have hbig := A.big
  have hq := queryEq_le16 f
  unfold qcIE qcI
  by_cases h : trivB f dv = true
  · rw [if_pos h]; exact iteE_pos A.c1 (by rw [trivE_eval h23 A hd hb, if_pos h]) (eE_k (by omega)) (by omega)
  · rw [if_neg h]
    refine iteE_neg A.c1 (by rw [trivE_eval h23 A hd hb, if_neg h]) (qRSE_eval h23 A hd hb) ?_
    unfold qRS; split_ifs <;> omega

end Params

end NearCubicGates.Adapters.ShortPCP.Machines.FL
