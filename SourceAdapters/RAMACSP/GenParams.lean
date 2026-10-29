import SourceAdapters.RAMACSP.GenGlue
import Proof.Foundations.CanonicalBinary
import SourceAdapters.RAMACSP.PackInstance

/-!
# The generator's stages G1–G2 in `FL`: read the request, compute the numbers

Paper: `lem:generator`. The program reads x and t and computes the word
width, padded time and input dimensions, layout dimensions and field degree.
The verifier-dependent constants are fixed before the request.

`readP` reads `frame x` and `frame (bits t)` (`rdFrame`, `FLangLib`) into the program variables `20 … 23`; `paramsP`
computes every number into `24 … 36` (`PV`) by counting loops (`clogP`: `⌈log₂ x⌉` as the least `k` with
`x ≤ 2^k`). Both are exact for every request (no promise), as `lem:generator` asks ("total: also when `n < 2`, `n > t`").
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins

variable {G : Glob}

/-! ## `⌈log₂ x⌉` by counting -/

/-- `dst := ⌈log₂ e⌉`: the least `k` with `e ≤ 2^k`. -/
def clogP (dst : Var) (e : E) : S :=
  .seq (.set dst (.k 0)) (.whl (.lt (.shl (.k 1) (.v dst)) e) (.set dst (.add (.v dst) (.k 1))))

theorem clogP_spec (s : FS) (dst : Var) (e : E) (x : ℕ)
    (he : ∀ t : FS, (∀ j, j ≠ dst → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t e = x)
    (hN : Nat.clog 2 x ≤ G.N) (hc : 2 * 2 ^ Nat.clog 2 x ≤ G.cap) :
    (evalS G (clogP dst e) s).env dst = Nat.clog 2 x ∧ Wr [dst] s (evalS G (clogP dst e) s) := by
  set L := Nat.clog 2 x with hL
  have c1 : min 1 G.cap = 1 := min_eq_left (by have := Nat.one_le_two_pow (n := L); omega)
  have hLp : L < 2 ^ L := Nat.lt_two_pow_self
  set s1 := s.setv dst (min 0 G.cap) with hs1
  have w1 : Wr [dst] s s1 := Wr.setv s (by simp) _
  have hw := whl_inv G (c := .lt (.shl (.k 1) (.v dst)) e) (body := .set dst (.add (.v dst) (.k 1)))
    (fun t => t.env dst ≤ L ∧ Wr [dst] s t) (fun t => L - t.env dst) s1
    ⟨by simp [s1], w1⟩ (by simp [s1]; omega) (by
      rintro t ⟨tL, tw⟩ hcnd
      have hx := he t (fun j hj => tw.env j (by simp [hj])) tw.fl tw.fp
      have hpt : 2 ^ t.env dst ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) tL
      have hsh : evalE G t (.shl (.k 1) (.v dst)) = 2 ^ t.env dst := by
        simp only [evalE, c1, one_mul]; exact min_eq_left (by omega)
      have hlt : 2 ^ t.env dst < x := by
        by_contra hn; apply hcnd; rw [eE_lt hsh hx, if_neg hn]
      have htL : t.env dst < L := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hlt
      have hadd : evalE G t (.add (.v dst) (.k 1)) = t.env dst + 1 := by
        simp only [evalE, c1]; exact min_eq_left (by omega)
      simp only [evalS_set, hadd]
      exact ⟨⟨by simp; omega, tw.trans (Wr.setv t (by simp) _)⟩, by simp; omega⟩)
  obtain ⟨⟨wL, ww⟩, wc⟩ := hw
  have ht : evalS G (clogP dst e) s = evalS G (.whl (.lt (.shl (.k 1) (.v dst)) e) (.set dst (.add (.v dst) (.k 1))))
      s1 := rfl
  rw [ht]
  generalize evalS G (.whl (.lt (.shl (.k 1) (.v dst)) e) (.set dst (.add (.v dst) (.k 1)))) s1 = t at wL ww wc
  refine ⟨?_, ww⟩
  have hx := he t (fun j hj => ww.env j (by simp [hj])) ww.fl ww.fp
  have hpt : 2 ^ t.env dst ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) wL
  have hsh : evalE G t (.shl (.k 1) (.v dst)) = 2 ^ t.env dst := by
    simp only [evalE, c1, one_mul]; exact min_eq_left (by omega)
  have hge : x ≤ 2 ^ t.env dst := by
    by_contra hn
    rw [eE_lt hsh hx, if_pos (by omega)] at wc; exact absurd wc one_ne_zero
  have := Nat.clog_le_of_le_pow hge
  omega

/-! ## The numbers -/

variable (V : Verifier)

theorem inExp_eq (r : ClockRequest) :
    inExp V r = Nat.clog 2 (max (r.1.1 + 1) (wordW V r.2)) := by
  unfold inExp ownXbar
  rw [padInput_length _ _ _ (by unfold inputPadLength; exact le_trans (le_max_left _ _) (le_two_pow_clog _))]
  unfold inputPadLength; rw [Nat.log_pow (by norm_num)]; rfl

/-- **The numbers in the program variables** (`20 … 36`). -/
structure PV (r : ClockRequest) (s : FS) : Prop where
  x : s.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2)
  n : s.env 21 = r.1.1
  t : s.env 22 = r.2
  tb : s.env 23 = r.2.bits.length
  c : s.env 24 = clockConst V
  om : s.env 25 = wordExp V r.2
  w : s.env 26 = wordW V r.2
  ta : s.env 27 = tau V r.2
  T : s.env 28 = 2 ^ tau V r.2
  m : s.env 29 = inExp V r
  P : s.env 30 = 2 ^ inExp V r
  k : s.env 31 = laneExp V r.2
  ell : s.env 32 = stageExp V r.2
  d : s.env 33 = tagExp V
  q : s.env 34 = colExp V r.2
  mH : s.env 35 = domExp V r.2
  f : s.env 36 = fieldExp V r.2

theorem PV.keep {r : ClockRequest} {s t : FS} (h : PV V r s) (he : ∀ i : Var, 20 ≤ i.val → i.val ≤ 36 →
    t.env i = s.env i) : PV V r t :=
  ⟨(he 20 (by decide) (by decide)).trans h.x, (he 21 (by decide) (by decide)).trans h.n,
    (he 22 (by decide) (by decide)).trans h.t, (he 23 (by decide) (by decide)).trans h.tb,
    (he 24 (by decide) (by decide)).trans h.c, (he 25 (by decide) (by decide)).trans h.om,
    (he 26 (by decide) (by decide)).trans h.w, (he 27 (by decide) (by decide)).trans h.ta,
    (he 28 (by decide) (by decide)).trans h.T, (he 29 (by decide) (by decide)).trans h.m,
    (he 30 (by decide) (by decide)).trans h.P, (he 31 (by decide) (by decide)).trans h.k,
    (he 32 (by decide) (by decide)).trans h.ell, (he 33 (by decide) (by decide)).trans h.d,
    (he 34 (by decide) (by decide)).trans h.q, (he 35 (by decide) (by decide)).trans h.mH,
    (he 36 (by decide) (by decide)).trans h.f⟩

/-- **The parameter program** (G1–G2 after the read): `24 … 36`, scratch `38, 39, 40`. -/
def paramsP : S :=
  .seq (.set 24 (.k (clockConst V))) (.seq (clogP 38 (.v 22)) (.seq (clogP 25 (.add (.v 38) (.v 24)))
  (.seq (.set 26 (.shl (.k 1) (.v 25))) (.seq (clogP 27 (.mul (.v 24) (.add (.v 22) (.v 26))))
  (.seq (.set 28 (.shl (.k 1) (.v 27)))
  (.seq (.ite (.lt (.add (.v 21) (.k 1)) (.v 26)) (.set 39 (.v 26)) (.set 39 (.add (.v 21) (.k 1))))
  (.seq (clogP 29 (.v 39)) (.seq (.set 30 (.shl (.k 1) (.v 29))) (.seq (.set 31 (.add (.v 27) (.k 1)))
  (.seq (clogP 32 (.mul (.k 2) (.v 31))) (.seq (.set 33 (.k (tagExp V))) (.seq (.set 34 (.add (.v 33) (.v 25)))
  (.seq (.set 35 (.add (.add (.add (.v 31) (.v 32)) (.v 34)) (.k 4)))
  (.seq (clogP 40 (.mul (.k 4) (.add (.v 35) (.k 4)))) (.set 36 (.add (.v 35) (.v 40)))))))))))))))))

/-- The size condition of the parameter program. -/
def ParamFit (r : ClockRequest) (G : Glob) : Prop :=
  r.1.1 + fieldExp V r.2 + r.2.bits.length + clockConst V + tagExp V + 8 ≤ G.K ∧ G.K ≤ G.N

theorem wr_val {s t : FS} {W : List Var} (h : Wr W s t) {i : Var} (hi : i ∉ W) : t.env i = s.env i := h.env i hi

theorem clog_le_size (t : ℕ) : Nat.clog 2 t ≤ t.bits.length := by
  have : t < 2 ^ t.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self t
  exact Nat.clog_le_of_le_pow (le_of_lt this)

theorem pow_le_cap' {G : Glob} {a : ℕ} (h : a + 2 ≤ G.K) : 2 * 2 ^ a ≤ G.cap := by
  have h1 := cap_add G
  have h2 : 2 ^ (a + 2) ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) h
  rw [pow_add] at h2
  have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  omega

theorem le_cap_of_lt_pow {G : Glob} {x a : ℕ} (hx : x < 2 ^ a) (h : a ≤ G.K) : x ≤ G.cap := by
  have := cap_add G; have : 2 ^ a ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) h; omega

/-- The variables the parameter program writes. -/
def PW : List Var := [24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40]

theorem setStep (s : FS) (i : Var) (e : E) (v : ℕ) (he : evalE G s e = v) :
    (evalS G (.set i e) s).env i = v ∧ Wr [i] s (evalS G (.set i e) s) :=
  ⟨by simp [he], Wr.setv s (by simp) _⟩

theorem wr_ne {W : List Var} {s t : FS} (h : Wr W s t) (j : Var) (hj : j ∉ W) : t.env j = s.env j := h.env j hj

theorem clogStep (s : FS) (dst : Var) (e : E) (x : ℕ) (he : evalE G s e = x) (hd : ∀ t : FS, (∀ j, j ≠ dst →
    t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t e = evalE G s e)
    (hN : Nat.clog 2 x ≤ G.N) (hc : Nat.clog 2 x + 2 ≤ G.K) :
    (evalS G (clogP dst e) s).env dst = Nat.clog 2 x ∧ Wr [dst] s (evalS G (clogP dst e) s) :=
  clogP_spec s dst e x (fun t h1 h2 h3 => (hd t h1 h2 h3).trans he) hN (pow_le_cap' hc)

/-- `e` does not read `dst`. -/
def noRd (dst : Var) : E → Bool
  | .v i => decide (i ≠ dst)
  | .k _ | .gk => true
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => noRd dst a && noRd dst b
  | .finv a => noRd dst a

/-- An expression in variables other than `dst` keeps its value when only `dst` changes. -/
theorem evalE_keep (dst : Var) {s : FS} : ∀ e : E, noRd dst e = true → ∀ t : FS,
    (∀ j, j ≠ dst → t.env j = s.env j) → t.fl = s.fl → t.fp = s.fp → evalE G t e = evalE G s e
  | .v i, he, t, h, _, _ => h i (by simpa [noRd] using he)
  | .k _, _, _, _, _, _ => rfl
  | .gk, _, _, _, _, _ => rfl
  | .add a b, he, t, h, hfl, hfp | .sub a b, he, t, h, hfl, hfp | .mul a b, he, t, h, hfl, hfp
  | .div a b, he, t, h, hfl, hfp | .md a b, he, t, h, hfl, hfp | .shl a b, he, t, h, hfl, hfp
  | .shr a b, he, t, h, hfl, hfp | .bxor a b, he, t, h, hfl, hfp | .lt a b, he, t, h, hfl, hfp
  | .eq a b, he, t, h, hfl, hfp => by
    simp only [noRd, Bool.and_eq_true] at he
    simp only [evalE, evalE_keep dst a he.1 t h hfl hfp, evalE_keep dst b he.2 t h hfl hfp]
  | .fadd a b, he, t, h, hfl, hfp | .fmul a b, he, t, h, hfl, hfp | .fpow a b, he, t, h, hfl, hfp => by
    simp only [noRd, Bool.and_eq_true] at he
    simp only [evalE, evalE_keep dst a he.1 t h hfl hfp, evalE_keep dst b he.2 t h hfl hfp, hfl, hfp]
  | .finv a, he, t, h, hfl, hfp => by
    simp only [noRd] at he
    simp only [evalE, evalE_keep dst a he t h hfl hfp, hfl, hfp]

/-- **The parameter program is correct** (G1–G2). -/
theorem paramsP_spec (r : ClockRequest) (s : FS) (h20 : s.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2))
    (h21 : s.env 21 = r.1.1) (h22 : s.env 22 = r.2) (h23 : s.env 23 = r.2.bits.length) (hfit : ParamFit V r G) :
    PV V r (evalS G (paramsP V) s) ∧ Wr PW s (evalS G (paramsP V) s) := by
  obtain ⟨hK, hKN⟩ := hfit
  set n := r.1.1
  set t := r.2
  set c := clockConst V with hcdef
  have hKc : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have hcap := cap_add G
  have hc16 : 16 ≤ c := sixteen_le_clockConst V
  have hωτ := wordExp_le_tau V t
  have hτm := tau_lt_domExp V t
  have hmf := domExp_add_two_le_fieldExp V t
  have hct := clog_le_size t
  -- closed forms
  have eω : wordExp V t = Nat.clog 2 (Nat.clog 2 t + c) := rfl
  have ew : wordW V t = 2 ^ wordExp V t := rfl
  have eτ : tau V t = Nat.clog 2 (c * (t + wordW V t)) := rfl
  have ek : laneExp V t = tau V t + 1 := rfl
  have eℓ : stageExp V t = Nat.clog 2 (2 * laneExp V t) := rfl
  have eq' : colExp V t = tagExp V + wordExp V t := rfl
  have emH : domExp V t = laneExp V t + stageExp V t + colExp V t + 4 := rfl
  have ef : fieldExp V t = domExp V t + Nat.clog 2 (4 * (domExp V t + 4)) := rfl
  have hm := inExp_eq V r
  have hcap_le : ∀ x, x ≤ G.K → x ≤ G.cap := fun x hx => le_cap_of_lt_pow (lt_of_le_of_lt hx hKc) le_rfl
  have hpow_cap : ∀ a, a + 1 ≤ G.K → 2 ^ a ≤ G.cap := fun a ha =>
    le_cap_of_lt_pow (Nat.pow_lt_pow_right (by norm_num) (show a < a + 1 by omega)) ha
  -- extra facts
  have hτF : tau V t + 2 ≤ fieldExp V t := by omega
  have hωF : wordExp V t + 2 ≤ fieldExp V t := by omega
  have hwτ : wordW V t ≤ 2 ^ tau V t := Nat.pow_le_pow_right (by norm_num) hωτ
  have hpτ : c * (t + wordW V t) ≤ 2 ^ tau V t := padTime_ge c t
  have hpτc : 2 ^ tau V t ≤ G.cap := hpow_cap _ (by omega)
  have hτK : tau V t + 2 ≤ G.K := by omega
  have hmle : inExp V r ≤ n + wordExp V t := by
    rw [hm]; apply Nat.clog_le_of_le_pow
    have h1 : n + 1 ≤ 2 ^ (n + wordExp V t) := by
      have := Nat.lt_two_pow_self (n := n); have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
        (show n ≤ n + wordExp V t by omega); omega
    have h2 : wordW V t ≤ 2 ^ (n + wordExp V t) := by rw [ew]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le h1 h2
  have hℓ : stageExp V t + 2 ≤ fieldExp V t := by omega
  have hlf : Nat.clog 2 (4 * (domExp V t + 4)) ≤ fieldExp V t := by omega
  have h4 : 4 * (domExp V t + 4) ≤ 2 ^ fieldExp V t := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) (4 * (domExp V t + 4))
    exact this.trans (Nat.pow_le_pow_right (by norm_num) hlf)
  have hFc : 2 ^ fieldExp V t ≤ G.cap := hpow_cap _ (by omega)
  have hFK : fieldExp V t + 1 ≤ G.K := by omega
  have ht : evalS G (paramsP V) s = evalS G (.set 36 (.add (.v 35) (.v 40))) (evalS G (clogP 40 (.mul (.k 4)
      (.add (.v 35) (.k 4)))) (evalS G (.set 35 (.add (.add (.add (.v 31) (.v 32)) (.v 34)) (.k 4)))
      (evalS G (.set 34 (.add (.v 33) (.v 25))) (evalS G (.set 33 (.k (tagExp V))) (evalS G (clogP 32
      (.mul (.k 2) (.v 31))) (evalS G (.set 31 (.add (.v 27) (.k 1))) (evalS G (.set 30 (.shl (.k 1) (.v 29)))
      (evalS G (clogP 29 (.v 39)) (evalS G (.ite (.lt (.add (.v 21) (.k 1)) (.v 26)) (.set 39 (.v 26))
      (.set 39 (.add (.v 21) (.k 1)))) (evalS G (.set 28 (.shl (.k 1) (.v 27))) (evalS G (clogP 27 (.mul (.v 24)
      (.add (.v 22) (.v 26)))) (evalS G (.set 26 (.shl (.k 1) (.v 25))) (evalS G (clogP 25 (.add (.v 38) (.v 24)))
      (evalS G (clogP 38 (.v 22)) (evalS G (.set 24 (.k c)) s))))))))))))))) := rfl
  rw [ht]
  -- step 1: `24 := c`
  obtain ⟨v1, w1⟩ := setStep (G := G) s 24 (.k c) (c) (eE_k (hcap_le c (by omega)))
  generalize hs1 : evalS G (.set 24 (.k c)) s = s1 at v1 w1
  -- step 2: `38 := ⌈log₂ (t)⌉`
  obtain ⟨v2, w2⟩ := clogStep (G := G) s1 38 (.v 22) (t) (by rw [eE_v, wr_ne w1 22 (by decide), h22])
    (evalE_keep 38 _ (by decide)) (by omega) (by omega)
  generalize hs2 : evalS G (clogP 38 (.v 22)) s1 = s2 at v2 w2
  -- step 3: `25 := ⌈log₂ (Nat.clog 2 t + c)⌉`
  obtain ⟨v3, w3⟩ := clogStep (G := G) s2 25 (.add (.v 38) (.v 24)) (Nat.clog 2 t + c) (eE_add (by rw [eE_v, v2]) (by rw [eE_v, wr_ne w2 24 (by decide), v1]) (hcap_le _ (by omega)))
    (evalE_keep 25 _ (by decide)) (by omega) (by omega)
  generalize hs3 : evalS G (clogP 25 (.add (.v 38) (.v 24))) s2 = s3 at v3 w3
  -- step 4: `26 := 2 ^ wordExp V t`
  obtain ⟨v4, w4⟩ := setStep (G := G) s3 26 (.shl (.k 1) (.v 25)) (2 ^ wordExp V t) (eE_pow (by rw [eE_v, v3, ← eω]) (by omega))
  generalize hs4 : evalS G (.set 26 (.shl (.k 1) (.v 25))) s3 = s4 at v4 w4
  -- step 5: `27 := ⌈log₂ (c * (t + wordW V t))⌉`
  obtain ⟨v5, w5⟩ := clogStep (G := G) s4 27 (.mul (.v 24) (.add (.v 22) (.v 26))) (c * (t + wordW V t)) (eE_mul (by rw [eE_v, wr_ne w4 24 (by decide), wr_ne w3 24 (by decide), wr_ne w2 24 (by decide), v1]) (eE_add (by rw [eE_v, wr_ne w4 22 (by decide), wr_ne w3 22 (by decide), wr_ne w2 22 (by decide), wr_ne w1 22 (by decide), h22]) (by rw [eE_v, v4, ew]) (le_trans (Nat.le_mul_of_pos_left _ (by omega)) (hpτ.trans hpτc))) (hpτ.trans hpτc))
    (evalE_keep 27 _ (by decide)) (by omega) (by omega)
  generalize hs5 : evalS G (clogP 27 (.mul (.v 24) (.add (.v 22) (.v 26)))) s4 = s5 at v5 w5
  -- step 6: `28 := 2 ^ tau V t`
  obtain ⟨v6, w6⟩ := setStep (G := G) s5 28 (.shl (.k 1) (.v 27)) (2 ^ tau V t) (eE_pow (by rw [eE_v, v5, ← eτ]) (by omega))
  generalize hs6 : evalS G (.set 28 (.shl (.k 1) (.v 27))) s5 = s6 at v6 w6
  -- step 7: `39 := max (n + 1) w`
  have v7w : s6.env 26 = wordW V t := by rw [wr_ne w6 26 (by decide), wr_ne w5 26 (by decide), v4]; rfl
  have v7n : s6.env 21 = n := by rw [wr_ne w6 21 (by decide), wr_ne w5 21 (by decide), wr_ne w4 21 (by decide), wr_ne w3 21 (by decide), wr_ne w2 21 (by decide), wr_ne w1 21 (by decide), h21]
  have hw7 : evalS G (.ite (.lt (.add (.v 21) (.k 1)) (.v 26)) (.set 39 (.v 26)) (.set 39 (.add (.v 21) (.k 1)))) s6 =
      s6.setv 39 (max (n + 1) (wordW V t)) := by
    have hc1 : evalE G s6 (.add (.v 21) (.k 1)) = n + 1 := eE_add (by rw [eE_v, v7n]) (eE_k (by omega)) (by omega)
    rw [evalS_ite, eE_lt hc1 (by rw [eE_v, v7w])]
    by_cases hlt : n + 1 < wordW V t
    · rw [if_pos hlt, if_neg one_ne_zero, evalS_set, eE_v, v7w, max_eq_right (le_of_lt hlt)]
    · rw [if_neg hlt, if_pos rfl, evalS_set, hc1, max_eq_left (by omega)]
  have v7 : (s6.setv 39 (max (n + 1) (wordW V t))).env 39 = max (n + 1) (wordW V t) := by simp
  have w7 : Wr [39] s6 (s6.setv 39 (max (n + 1) (wordW V t))) := Wr.setv s6 (by simp) _
  rw [hw7]
  generalize hs7 : s6.setv 39 (max (n + 1) (wordW V t)) = s7 at v7 w7
  -- step 8: `29 := ⌈log₂ (max (n + 1) (wordW V t))⌉`
  obtain ⟨v8, w8⟩ := clogStep (G := G) s7 29 (.v 39) (max (n + 1) (wordW V t)) (by rw [eE_v, v7])
    (evalE_keep 29 _ (by decide)) (by rw [← hm]; omega) (by rw [← hm]; omega)
  generalize hs8 : evalS G (clogP 29 (.v 39)) s7 = s8 at v8 w8
  -- step 9: `30 := 2 ^ inExp V r`
  obtain ⟨v9, w9⟩ := setStep (G := G) s8 30 (.shl (.k 1) (.v 29)) (2 ^ inExp V r) (eE_pow (by rw [eE_v, v8, hm]) (by omega))
  generalize hs9 : evalS G (.set 30 (.shl (.k 1) (.v 29))) s8 = s9 at v9 w9
  -- step 10: `31 := laneExp V t`
  obtain ⟨v10, w10⟩ := setStep (G := G) s9 31 (.add (.v 27) (.k 1)) (laneExp V t) (eE_add (by rw [eE_v, wr_ne w9 27 (by decide), wr_ne w8 27 (by decide), wr_ne w7 27 (by decide), wr_ne w6 27 (by decide), v5, ← eτ]) (eE_k (by omega)) (by omega))
  generalize hs10 : evalS G (.set 31 (.add (.v 27) (.k 1))) s9 = s10 at v10 w10
  -- step 11: `32 := ⌈log₂ (2 * laneExp V t)⌉`
  obtain ⟨v11, w11⟩ := clogStep (G := G) s10 32 (.mul (.k 2) (.v 31)) (2 * laneExp V t) (eE_mul (eE_k (by omega)) (by rw [eE_v, v10]) (by omega))
    (evalE_keep 32 _ (by decide)) (by omega) (by omega)
  generalize hs11 : evalS G (clogP 32 (.mul (.k 2) (.v 31))) s10 = s11 at v11 w11
  -- step 12: `33 := tagExp V`
  obtain ⟨v12, w12⟩ := setStep (G := G) s11 33 (.k (tagExp V)) (tagExp V) (eE_k (hcap_le _ (by omega)))
  generalize hs12 : evalS G (.set 33 (.k (tagExp V))) s11 = s12 at v12 w12
  -- step 13: `34 := colExp V t`
  obtain ⟨v13, w13⟩ := setStep (G := G) s12 34 (.add (.v 33) (.v 25)) (colExp V t) (eE_add (by rw [eE_v, v12]) (by rw [eE_v, wr_ne w12 25 (by decide), wr_ne w11 25 (by decide), wr_ne w10 25 (by decide), wr_ne w9 25 (by decide), wr_ne w8 25 (by decide), wr_ne w7 25 (by decide), wr_ne w6 25 (by decide), wr_ne w5 25 (by decide), wr_ne w4 25 (by decide), v3, ← eω]) (by omega))
  generalize hs13 : evalS G (.set 34 (.add (.v 33) (.v 25))) s12 = s13 at v13 w13
  -- step 14: `35 := domExp V t`
  obtain ⟨v14, w14⟩ := setStep (G := G) s13 35 (.add (.add (.add (.v 31) (.v 32)) (.v 34)) (.k 4)) (domExp V t) (eE_add (eE_add (eE_add (by rw [eE_v, wr_ne w13 31 (by decide), wr_ne w12 31 (by decide), wr_ne w11 31 (by decide), v10]) (by rw [eE_v, wr_ne w13 32 (by decide), wr_ne w12 32 (by decide), v11, ← eℓ]) (by omega)) (by rw [eE_v, v13]) (by omega)) (eE_k (by omega)) (by omega))
  generalize hs14 : evalS G (.set 35 (.add (.add (.add (.v 31) (.v 32)) (.v 34)) (.k 4))) s13 = s14 at v14 w14
  -- step 15: `40 := ⌈log₂ (4 * (domExp V t + 4))⌉`
  obtain ⟨v15, w15⟩ := clogStep (G := G) s14 40 (.mul (.k 4) (.add (.v 35) (.k 4))) (4 * (domExp V t + 4)) (eE_mul (eE_k (by omega)) (eE_add (by rw [eE_v, v14]) (eE_k (by omega)) (by omega)) (by omega))
    (evalE_keep 40 _ (by decide)) (by omega) (by omega)
  generalize hs15 : evalS G (clogP 40 (.mul (.k 4) (.add (.v 35) (.k 4)))) s14 = s15 at v15 w15
  -- step 16: `36 := fieldExp V t`
  obtain ⟨v16, w16⟩ := setStep (G := G) s15 36 (.add (.v 35) (.v 40)) (fieldExp V t) (eE_add (by rw [eE_v, wr_ne w15 35 (by decide), v14]) (by rw [eE_v, v15]) (by omega))
  generalize hs16 : evalS G (.set 36 (.add (.v 35) (.v 40))) s15 = s16 at v16 w16
  refine ⟨⟨by rw [wr_ne w16 20 (by decide), wr_ne w15 20 (by decide), wr_ne w14 20 (by decide), wr_ne w13 20 (by decide), wr_ne w12 20 (by decide), wr_ne w11 20 (by decide), wr_ne w10 20 (by decide), wr_ne w9 20 (by decide), wr_ne w8 20 (by decide), wr_ne w7 20 (by decide), wr_ne w6 20 (by decide), wr_ne w5 20 (by decide), wr_ne w4 20 (by decide), wr_ne w3 20 (by decide), wr_ne w2 20 (by decide), wr_ne w1 20 (by decide), h20],
    by rw [wr_ne w16 21 (by decide), wr_ne w15 21 (by decide), wr_ne w14 21 (by decide), wr_ne w13 21 (by decide), wr_ne w12 21 (by decide), wr_ne w11 21 (by decide), wr_ne w10 21 (by decide), wr_ne w9 21 (by decide), wr_ne w8 21 (by decide), wr_ne w7 21 (by decide), wr_ne w6 21 (by decide), wr_ne w5 21 (by decide), wr_ne w4 21 (by decide), wr_ne w3 21 (by decide), wr_ne w2 21 (by decide), wr_ne w1 21 (by decide), h21],
    by rw [wr_ne w16 22 (by decide), wr_ne w15 22 (by decide), wr_ne w14 22 (by decide), wr_ne w13 22 (by decide), wr_ne w12 22 (by decide), wr_ne w11 22 (by decide), wr_ne w10 22 (by decide), wr_ne w9 22 (by decide), wr_ne w8 22 (by decide), wr_ne w7 22 (by decide), wr_ne w6 22 (by decide), wr_ne w5 22 (by decide), wr_ne w4 22 (by decide), wr_ne w3 22 (by decide), wr_ne w2 22 (by decide), wr_ne w1 22 (by decide), h22],
    by rw [wr_ne w16 23 (by decide), wr_ne w15 23 (by decide), wr_ne w14 23 (by decide), wr_ne w13 23 (by decide), wr_ne w12 23 (by decide), wr_ne w11 23 (by decide), wr_ne w10 23 (by decide), wr_ne w9 23 (by decide), wr_ne w8 23 (by decide), wr_ne w7 23 (by decide), wr_ne w6 23 (by decide), wr_ne w5 23 (by decide), wr_ne w4 23 (by decide), wr_ne w3 23 (by decide), wr_ne w2 23 (by decide), wr_ne w1 23 (by decide), h23],
    by rw [wr_ne w16 24 (by decide), wr_ne w15 24 (by decide), wr_ne w14 24 (by decide), wr_ne w13 24 (by decide), wr_ne w12 24 (by decide), wr_ne w11 24 (by decide), wr_ne w10 24 (by decide), wr_ne w9 24 (by decide), wr_ne w8 24 (by decide), wr_ne w7 24 (by decide), wr_ne w6 24 (by decide), wr_ne w5 24 (by decide), wr_ne w4 24 (by decide), wr_ne w3 24 (by decide), wr_ne w2 24 (by decide), v1],
    by rw [wr_ne w16 25 (by decide), wr_ne w15 25 (by decide), wr_ne w14 25 (by decide), wr_ne w13 25 (by decide), wr_ne w12 25 (by decide), wr_ne w11 25 (by decide), wr_ne w10 25 (by decide), wr_ne w9 25 (by decide), wr_ne w8 25 (by decide), wr_ne w7 25 (by decide), wr_ne w6 25 (by decide), wr_ne w5 25 (by decide), wr_ne w4 25 (by decide), v3, ← eω],
    by rw [wr_ne w16 26 (by decide), wr_ne w15 26 (by decide), wr_ne w14 26 (by decide), wr_ne w13 26 (by decide), wr_ne w12 26 (by decide), wr_ne w11 26 (by decide), wr_ne w10 26 (by decide), wr_ne w9 26 (by decide), wr_ne w8 26 (by decide), wr_ne w7 26 (by decide), wr_ne w6 26 (by decide), wr_ne w5 26 (by decide), v4, ew],
    by rw [wr_ne w16 27 (by decide), wr_ne w15 27 (by decide), wr_ne w14 27 (by decide), wr_ne w13 27 (by decide), wr_ne w12 27 (by decide), wr_ne w11 27 (by decide), wr_ne w10 27 (by decide), wr_ne w9 27 (by decide), wr_ne w8 27 (by decide), wr_ne w7 27 (by decide), wr_ne w6 27 (by decide), v5, ← eτ],
    by rw [wr_ne w16 28 (by decide), wr_ne w15 28 (by decide), wr_ne w14 28 (by decide), wr_ne w13 28 (by decide), wr_ne w12 28 (by decide), wr_ne w11 28 (by decide), wr_ne w10 28 (by decide), wr_ne w9 28 (by decide), wr_ne w8 28 (by decide), wr_ne w7 28 (by decide), v6],
    by rw [wr_ne w16 29 (by decide), wr_ne w15 29 (by decide), wr_ne w14 29 (by decide), wr_ne w13 29 (by decide), wr_ne w12 29 (by decide), wr_ne w11 29 (by decide), wr_ne w10 29 (by decide), wr_ne w9 29 (by decide), v8, hm],
    by rw [wr_ne w16 30 (by decide), wr_ne w15 30 (by decide), wr_ne w14 30 (by decide), wr_ne w13 30 (by decide), wr_ne w12 30 (by decide), wr_ne w11 30 (by decide), wr_ne w10 30 (by decide), v9],
    by rw [wr_ne w16 31 (by decide), wr_ne w15 31 (by decide), wr_ne w14 31 (by decide), wr_ne w13 31 (by decide), wr_ne w12 31 (by decide), wr_ne w11 31 (by decide), v10],
    by rw [wr_ne w16 32 (by decide), wr_ne w15 32 (by decide), wr_ne w14 32 (by decide), wr_ne w13 32 (by decide), wr_ne w12 32 (by decide), v11, ← eℓ],
    by rw [wr_ne w16 33 (by decide), wr_ne w15 33 (by decide), wr_ne w14 33 (by decide), wr_ne w13 33 (by decide), v12],
    by rw [wr_ne w16 34 (by decide), wr_ne w15 34 (by decide), wr_ne w14 34 (by decide), v13],
    by rw [wr_ne w16 35 (by decide), wr_ne w15 35 (by decide), v14],
    by rw [v16]⟩, ?_⟩
  exact ((((((((((((((((w1.mono (W' := PW) (by decide)).trans (w2.mono (W' := PW) (by decide))).trans (w3.mono (W' := PW) (by decide))).trans (w4.mono (W' := PW) (by decide))).trans (w5.mono (W' := PW) (by decide))).trans (w6.mono (W' := PW) (by decide))).trans (w7.mono (W' := PW) (by decide))).trans (w8.mono (W' := PW) (by decide))).trans (w9.mono (W' := PW) (by decide))).trans (w10.mono (W' := PW) (by decide))).trans (w11.mono (W' := PW) (by decide))).trans (w12.mono (W' := PW) (by decide))).trans (w13.mono (W' := PW) (by decide))).trans (w14.mono (W' := PW) (by decide))).trans (w15.mono (W' := PW) (by decide))).trans (w16.mono (W' := PW) (by decide)))

end NearCubicGates.Adapters.RAMACSP.Gen
