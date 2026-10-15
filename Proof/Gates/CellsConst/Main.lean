import Proof.Gates.CellsConst.Stores

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

theorem vecs_len (q : ℕ) : ∀ d, (vecs q d).length = q ^ d
  | 0 => by simp [vecs]
  | d + 1 => by
    simp only [vecs, List.length_flatMap, List.length_map, vecs_len q d]
    simp [pow_succ, mul_comm]

theorem parts_len (c : Call) : (parts c).length = if kindTag c.kind = 2 then 2 else 1 := by
  unfold parts; cases h : c.kind <;> simp [kindTag]

/-- `|reqIds| = |parts|·Σ_q q^{rc·(J+1)} + rc·(J+1)`, the primes in increasing order. -/
theorem reqIds_len (c : Call) (p : Params) :
    (reqIds c p).length = (if kindTag c.kind = 2 then 2 else 1) *
      ((p.primes.sort (· ≤ ·)).map (· ^ (roleCount c.kind * (p.J + 1)))).sum + roleCount c.kind * (p.J + 1) := by
  rw [← parts_len c]
  unfold reqIds
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, vecs_len]
  have : ∀ x : ℕ, x ^ (roleCount c.kind * p.J) * x ^ roleCount c.kind = x ^ (roleCount c.kind * (p.J + 1)) := by
    intro x; rw [← pow_add, show roleCount c.kind * p.J + roleCount c.kind = roleCount c.kind * (p.J + 1) by ring]
  simp only [this, List.length_range]

theorem tailL_eq (p : Params) (h : p.factors.length = p.J - 1) : tailL p = (List.range p.J).map (tProd p.factors) := by
  unfold tailL tProd
  congr 1; funext j
  rw [h]
  unfold tailProd rateOf
  rw [show (∏ t ∈ Finset.Ico j (p.J - 1), ((p.factors.getD t 0 : ℕ) : ℤ)) =
    ((∏ t ∈ Finset.Ico j (p.J - 1), p.factors.getD t 0 : ℕ) : ℤ) by push_cast; rfl]
  exact Int.toNat_natCast _

theorem mem_coordsOf {n : ℕ} (I : Finset (Fin n)) (i : ℕ) (hi : i < n) : i ∈ coordsOf I ↔ (⟨i, hi⟩ : Fin n) ∈ I := by
  unfold coordsOf
  simp only [List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨_, h, rfl⟩

theorem membL_eq {n : ℕ} (I : Finset (Fin n)) : membL I = mVec (coordsOf I) n := by
  unfold membL mVec
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  have hi : i < n := by simpa using h1
  by_cases h : (⟨i, hi⟩ : Fin n) ∈ I
  · rw [if_pos h, if_pos ((mem_coordsOf I i hi).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((mem_coordsOf I i hi).mp h'))]

theorem coordsOf_len {n : ℕ} (I : Finset (Fin n)) : (coordsOf I).length = I.card := by
  unfold coordsOf; simp

theorem cellBits_eq {n : ℕ} (I : Finset (Fin n)) : cellBits I = n - (coordsOf I).length := by
  rw [coordsOf_len]
  unfold cellBits outerCoords
  rw [Finset.length_sort, Finset.filter_not, Finset.card_sdiff]
  simp

/-! ## The layout of `cellN` -/

section Lay
variable (c : Call) (p : Params) (wt : Wit c.n)

theorem drop_factors : (cellN c p wt).drop (iPsi (cellN c p wt) + 24 + nPr (cellN c p wt) + 1) =
    p.factors ++ ([p.A, p.Lambda] ++ witN c p wt) := by
  have hl := lay c p wt
  set L := cellN c p wt
  have hP : paramsN p ++ witN c p wt = ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e,
      (p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·) ++ [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++
      ratN p.ell0 ++ [p.M1, p.J, p.factors.length]) ++ (p.factors ++ ([p.A, p.Lambda] ++ witN c p wt)) := by
    simp [paramsN, List.append_assoc]
  rw [show iPsi L + 24 + nPr L + 1 = iPsi L + (25 + (p.primes.sort (· ≤ ·)).length) by rw [hl.np]; ring,
    ← List.drop_drop, hl.params, hP, List.drop_left']
  simp [ratN_length]; ring

theorem drop_coords : (cellN c p wt).drop (iOm (cellN c p wt) + 1) =
    coordsOf wt.I ++ (srList c p).flatMap (fun sr => [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN) := by
  have hl := lay c p wt
  rw [← List.drop_drop, hl.wit]
  simp [witN]

theorem fld_iOm : fld (cellN c p wt) (iOm (cellN c p wt)) = (coordsOf wt.I).length :=
  fld_of_drop (B := coordsOf wt.I ++
    (srList c p).flatMap (fun sr => [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN))
    (by rw [(lay c p wt).wit]; simp [witN])

end Lay

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-- The facts the constants program uses. -/
structure CF (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : Prop where
  J1 : 1 ≤ p.J
  Jn : p.J ≤ c.n + 1
  nF : p.factors.length = p.J - 1
  Pn : p.P ≤ c.n
  kn : p.k ≤ c.n
  hE1 : 1 ≤ p.hE
  hEn : p.hE ≤ c.n
  WW : p.W = c.W
  NPn : (p.primes.sort (· ≤ ·)).length ≤ c.n
  NP0 : 0 < (p.primes.sort (· ≤ ·)).length
  rc2 : roleCount c.kind ≤ 2
  co : (coordsOf wt.I).length ≤ c.n
  Ln : (cellN c p wt).length ≤ 70 * (c.n + 1) ^ 5
  w1 : p.P + p.J + 4 ≤ C.Wd
  w2 : keyBits p * (roleCount c.kind * (p.J + 1) + 3) + roleCount c.kind * (p.J + 1) + 4 ≤ C.Wd
  w3 : p.J + 2 ≤ C.Wd
  w4 : valueWidth c p + Big + 1 ≤ C.Wd
  w5 : 2 * c.n + 2 < C.Wd
  LW : (cellN c p wt).length < 2 ^ C.Wd
  DB : deltaBound c p < 2 ^ C.Wd
  hEB : p.hE < 2 ^ Big
  LaB : p.Lambda < 2 ^ Big
  bn : (2 * p.hE - 1) ^ (roleCount c.kind * p.J) < 2 ^ C.Wd
  rJ : roleCount c.kind * p.J < 2 ^ C.Wd
  pr1 : roleCount c.kind * (p.J + 1) + p.J + 1 < 2 ^ C.Wd
  prS : 2 * ((p.primes.sort (· ≤ ·)).map (· ^ (roleCount c.kind * (p.J + 1)))).sum +
    roleCount c.kind * (p.J + 1) < 2 ^ C.Wd
  tprod : ∀ j u, j ≤ u → u ≤ p.factors.length → ∏ t ∈ Finset.Ico j u, p.factors.getD t 0 < 2 ^ C.Wd

theorem pow_lt_of {x W : ℕ} (h : x < W) : 2 ^ x < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) h
theorem pow_le_of {x W : ℕ} (h : x ≤ W) : 2 ^ x ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h

theorem db_lt (M1 A Wc J Big Wd : ℕ) (F : List ℕ) (hF : ∀ x ∈ F, x < 2 ^ Big) (hnF : F.length ≤ J)
    (M1B : M1 < 2 ^ Big) (AB : A < 2 ^ Big) (WB : Wc < 2 ^ Big) (hW : J + 2 + 2 * Big < Wd) :
    2 * (M1 + A + F.sum + 1) * (Wc + 1) < 2 ^ Wd := by
  have h2B : 1 ≤ 2 ^ Big := Nat.one_le_two_pow
  have hsum : F.sum ≤ J * 2 ^ Big := by
    have := List.sum_le_card_nsmul F (2 ^ Big) (fun x hx => (hF x hx).le)
    rw [smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hnF)
  have hJ2 : J + 2 ≤ 2 ^ (J + 1) := by have := Nat.lt_two_pow_self (n := J + 1); omega
  have e0 : (J + 2) * 2 ^ Big ≤ 2 ^ (J + 1) * 2 ^ Big := Nat.mul_le_mul_right _ hJ2
  have e1 : M1 + A + F.sum + 1 ≤ 2 ^ (J + 1) * 2 ^ Big := by
    have : (J + 2) * 2 ^ Big = J * 2 ^ Big + 2 * 2 ^ Big := by ring
    omega
  have e2 : Wc + 1 ≤ 2 ^ Big := by omega
  calc 2 * (M1 + A + F.sum + 1) * (Wc + 1) ≤ 2 * (2 ^ (J + 1) * 2 ^ Big) * 2 ^ Big :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) e2
    _ = 2 ^ (J + 2 + 2 * Big) := by ring
    _ < 2 ^ Wd := pow_lt_of hW

theorem bn_lt (H R J Big Wd : ℕ) (hH : H < 2 ^ Big) (hR : R ≤ 2) (hW : 2 * (J * Big) + 2 * J < Wd) :
    (2 * H - 1) ^ (R * J) < 2 ^ Wd := by
  have h1 : 2 * H - 1 ≤ 2 ^ (Big + 1) := by rw [pow_succ]; omega
  have h2 : (Big + 1) * (R * J) ≤ 2 * (J * Big) + 2 * J := by
    have : (Big + 1) * (R * J) ≤ (Big + 1) * (2 * J) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hR)
    have e : (Big + 1) * (2 * J) = 2 * (J * Big) + 2 * J := by ring
    omega
  calc (2 * H - 1) ^ (R * J) ≤ (2 ^ (Big + 1)) ^ (R * J) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ ((Big + 1) * (R * J)) := by rw [← pow_mul]
    _ < 2 ^ Wd := pow_lt_of (by omega)

theorem prS_lt (Q : List ℕ) (m n Big Wd : ℕ) (hq : ∀ q ∈ Q, q < 2 ^ Big) (hQn : Q.length ≤ n) (hB1 : 1 ≤ Big)
    (hW : n + Big * m + 2 ≤ Wd) : 2 * (Q.map (· ^ m)).sum + m < 2 ^ Wd := by
  have hq' : ∀ x ∈ Q.map (· ^ m), x ≤ 2 ^ (Big * m) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨q, hq1, rfl⟩ := hx
    rw [pow_mul]; exact Nat.pow_le_pow_left (hq q hq1).le _
  have hS := List.sum_le_card_nsmul _ _ hq'
  rw [smul_eq_mul, List.length_map] at hS
  have hS2 : (Q.map (· ^ m)).sum < 2 ^ (n + Big * m) := by
    calc _ ≤ Q.length * 2 ^ (Big * m) := hS
      _ < 2 ^ n * 2 ^ (Big * m) := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt hQn Nat.lt_two_pow_self)
          (Nat.two_pow_pos _)
      _ = 2 ^ (n + Big * m) := by rw [pow_add]
  have hm2 : m < 2 ^ (n + Big * m) := by
    have : m ≤ n + Big * m := by have := Nat.le_mul_of_pos_left m (show 0 < Big by omega); omega
    exact lt_of_lt_of_le Nat.lt_two_pow_self (pow_le_of this)
  have h4 : 2 ^ (n + Big * m) * 2 * 2 ≤ 2 ^ Wd := by
    rw [← pow_succ, ← pow_succ]; exact pow_le_of (by omega)
  omega

theorem tprod_lt (F : List ℕ) (Big J Wd : ℕ) (hF : ∀ t, F.getD t 0 < 2 ^ Big) (hFJ : F.length ≤ J)
    (hW : J * Big < Wd) : ∀ j u, j ≤ u → u ≤ F.length → ∏ t ∈ Finset.Ico j u, F.getD t 0 < 2 ^ Wd := by
  intro j u hju hu
  have h1 := Finset.prod_le_pow_card (Finset.Ico j u) (fun t => F.getD t 0) (2 ^ Big) (fun t _ => (hF t).le)
  rw [Nat.card_Ico, ← pow_mul] at h1
  have h2 : Big * (u - j) ≤ J * Big := by rw [mul_comm J]; exact Nat.mul_le_mul_left _ (by omega)
  exact lt_of_le_of_lt h1 (pow_lt_of (by omega))

/-- The width budget, linearized. -/
theorem wd_split (J Big n RW Wd : ℕ) (h : 256 * (J + 4) * (Big + n + 16) + 4 * RW ≤ Wd) :
    256 * (J * Big + J * n + 16 * J + 4 * Big + 4 * n + 64) + 4 * RW ≤ Wd := by
  have : 256 * (J + 4) * (Big + n + 16) = 256 * (J * Big + J * n + 16 * J + 4 * Big + 4 * n + 64) := by ring
  rw [this] at h; exact h

theorem cf_of (C : Ctx) {cT B1 B2 : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (w : List Bool) (Big : ℕ)
    (hs : Spec cT (header c) p) (hw : decodeWitness c p w = some wt) (hadm : c.Admitted B1 B2)
    (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big) (hWd : wdNeed c p wt Big ≤ C.Wd) : CF C c p wt Big := by
  have hwd0 : 256 * (p.J + 4) * (Big + c.n + 16) + 4 * recWidth c p wt ≤ C.Wd := hWd
  have hwd := wd_split _ _ _ _ _ hwd0
  unfold recWidth at hwd
  obtain ⟨JB, hJB⟩ : ∃ JB, JB = p.J * Big := ⟨_, rfl⟩
  obtain ⟨Jn, hJnd⟩ : ∃ Jn, Jn = p.J * c.n := ⟨_, rfl⟩
  rw [← hJB, ← hJnd] at hwd
  have hJ1 := hs.J_pos
  have hJn : p.J ≤ c.n + 1 := (J_le_Jmax c p hs).trans (Jmax_le c p hadm hs)
  have hnF := factors_length hs
  have hPn := P_le_n c p hs
  have hkn : p.k ≤ c.n := hs.k_lt.le
  have hP100 := hs.P_large
  have hhE : p.hE = p.P / 4 := hs.hE_eq
  have hn4 : 4 ≤ c.n := hadm.1
  have hNP : (p.primes.sort (· ≤ ·)).length ≤ c.n := by
    rw [Finset.length_sort]; exact (primes_card_le c p hs).trans hPn
  have hNP0 : 0 < (p.primes.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact Finset.card_pos.mpr hs.primes_nonempty
  have hrc2 : roleCount c.kind ≤ 2 := by cases c.kind <;> decide
  have hco : (coordsOf wt.I).length ≤ c.n := by
    rw [coordsOf_len]; simpa using Finset.card_le_univ wt.I
  have mem : ∀ x ∈ paramsN p, x < 2 ^ Big := fun x hx => lt_of_big c p wt hBig (mem_cellN_params c p wt hx)
  have nB : c.n < 2 ^ Big := lt_of_big c p wt hBig (n_mem c p wt)
  have fB : ∀ t, p.factors.getD t 0 < 2 ^ Big := by
    intro t
    by_cases ht : t < p.factors.length
    · rw [List.getD_eq_getElem _ _ ht]; exact mem _ (by simp [paramsN, List.getElem_mem])
    · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.two_pow_pos _
  have qB : ∀ q ∈ p.primes.sort (· ≤ ·), q < 2 ^ Big := fun q hq => mem _ (by simp [paramsN] at hq ⊢; simp [hq])
  have hBig1 : 1 ≤ Big := by
    by_contra h0
    have : Big = 0 := by omega
    rw [this] at nB; omega
  have hKL : keyBits p * keyLen c p = keyBits p * (roleCount c.kind * (p.J + 1) + 3) := by
    unfold keyLen; ring_nf
  have hRJ : roleCount c.kind * (p.J + 1) ≤ 2 * p.J + 2 := by
    have := Nat.mul_le_mul_right (p.J + 1) hrc2; omega
  have hRJ' : roleCount c.kind * p.J ≤ 2 * p.J := Nat.mul_le_mul_right _ hrc2
  have hBm : Big * (roleCount c.kind * (p.J + 1)) ≤ 2 * JB + 2 * Big := by
    have := Nat.mul_le_mul_left Big hRJ
    have e : Big * (2 * p.J + 2) = 2 * JB + 2 * Big := by rw [hJB]; ring
    omega
  have hW5 : 5 * c.n + 7 ≤ C.Wd := by omega
  have hDB : deltaBound c p < 2 ^ C.Wd := by
    unfold deltaBound
    exact db_lt _ _ _ p.J Big _ p.factors (fun x hx => mem x (by simp [paramsN, hx])) (by omega)
      (mem _ (by simp [paramsN])) (mem _ (by simp [paramsN])) (by have h := mem p.W (by simp [paramsN]); rw [hs.W_eq] at h; exact h)
      (by omega)
  exact ⟨hJ1, hJn, hnF, hPn, hkn, by omega, by omega, hs.W_eq, hNP, hNP0, hrc2, hco, cellN_len c p wt hadm hs w hw,
    by omega, by rw [← hKL]; omega, by omega, by omega, by omega,
    lt_of_lt_of_le (cellN_len_lt c p wt hadm hs w hw) (pow_le_of hW5), hDB, mem _ (by simp [paramsN]),
    mem _ (by simp [paramsN]), bn_lt _ _ _ Big _ (mem _ (by simp [paramsN])) hrc2 (by rw [← hJB]; omega),
    lt_pow_of_le (by omega), lt_pow_of_le (by omega),
    prS_lt _ _ c.n Big _ qB hNP hBig1 (by omega), tprod_lt _ Big p.J _ fB (by omega) (by omega)⟩

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-! ## The capped thresholds -/

def capsP : St VV MM := .seq (.op (.copy kE wK)) (.seq (.op (.shl kE)) (.seq (capP pTH vHE) (capP pTL vLam)))

theorem capsP_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (k H La V B : ℕ) (hk : a.env wK = k) (hH : a.env vHE = H)
    (hL : a.env vLam = La) (hV : a.env p2VW = 2 ^ V) (hHB : H < 2 ^ B) (hLB : La < 2 ^ B) (hVB : V + B ≤ C.Wd)
    (hkW : 2 * k < 2 ^ C.Wd) :
    Hs C capsP a (40 * k + 17) (fun e => e.env pTH = min (H ^ (2 * k)) (2 ^ V) ∧
      e.env pTL = min (La ^ (2 * k)) (2 ^ V) ∧ e.sh = a.sh ∧ Fr a e [kE, pTH, pTL, kU, kT1, vJ]) := by
  apply Hx.hs
  refine Hs.then (Hs.setx (hs_copy C kE wK a (by decide))) (fun b1 ⟨e1, s1, f1⟩ n1 hn1 => ?_)
  rw [hk] at e1
  refine Hs.then (Hs.setx (hs_shl C kE b1 (by rw [e1]; exact hkW))) (fun b2 ⟨e2, s2, f2⟩ n2 hn2 => ?_)
  rw [e1] at e2
  have F2 : Fr a b2 [kE, pTH, pTL, kU, kT1, vJ] := frA (Fr.weaken f1 (by decide)) f2 (by decide)
  refine Hs.then (capP_spec C pTH vHE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b2 (cstF hc F2 (by decide)) H (2 * k) V B
    (by rw [F2 vHE (by decide), hH]) e2 (by rw [F2 p2VW (by decide), hV]) hHB hVB hkW)
    (fun b3 ⟨v3, s3, f3⟩ n3 hn3 => ?_)
  have F3 := frA F2 f3 (by decide)
  refine Hs.last (capP_spec C pTL vLam (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) b3 (cstF hc F3 (by decide)) La (2 * k) V B
    (by rw [F3 vLam (by decide), hL]) (by rw [f3 kE (by decide), e2]) (by rw [F3 p2VW (by decide), hV]) hLB hVB hkW)
    (fun b4 ⟨v4, s4, f4⟩ n4 hn4 => ?_)
  exact ⟨⟨by rw [f4 pTH (by decide)]; exact v3, v4, by rw [s4, s3, s2, s1], frA F3 f4 (by decide)⟩, by omega⟩

/-! ## Part A: the constants that need no store -/

def constA : St VV MM :=
  .seq keys1 (.seq keys2 (.seq sumF (.seq vwA (.seq vwB (.seq capsP (.seq bnP ncP))))))

def tA : List (Fin VV) := [kT1, kKB, vKB, kI, kKL, kKW, p2K, p2KF, kPos, c0, vJ, kAc, kU, kX, kDB, kS, kVW, p2VW,
  kE, pTH, pTL, kT2, vBN, gNC]

/-- The cost of part A. -/
def costA (c : Call) (p : Params) (wt : Wit c.n) : ℕ :=
  (10 * (p.P + p.J) + 60) + (10 * keyW c p + 40) + (6 * (cellN c p wt).length + 7 * p.factors.length + 30) +
    (5 * Nat.size (deltaBound c p) + 20) + (5 * valueWidth c p + 20) + (40 * p.k + 17) +
    (7 * (roleCount c.kind * p.J) + 20) + (5 * c.n + 10) + 7

theorem keyLen_eq (c : Call) (p : Params) : keyLen c p = roleCount c.kind * (p.J + 1) + 3 := by
  unfold keyLen; omega

theorem valueWidth_eq (c : Call) (p : Params) (h : p.W = c.W) :
    valueWidth c p = p.k + 2 * p.k * Nat.size (2 * (p.M1 + p.A + p.factors.sum + 1) * (p.W + 1)) + 1 := by
  unfold valueWidth deltaBound; rw [h]

theorem constA_spec (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (a : DS VV MM)
    (cp : ConstPre c p wt a) (cf : CF C c p wt Big) :
    Hs C constA a (costA c p wt) (fun e => e.env vKB = 2 ^ keyBits p ∧ e.env p2K = 2 ^ keyW c p ∧
      e.env p2KF = 2 ^ (keyW c p - keyBits p) ∧ e.env p2VW = 2 ^ valueWidth c p ∧
      e.env pTH = min (p.hE ^ (2 * p.k)) (2 ^ valueWidth c p) ∧
      e.env pTL = min (p.Lambda ^ (2 * p.k)) (2 ^ valueWidth c p) ∧
      e.env vBN = (wWin p) ^ (nDig c p) ∧ e.env gNC = 2 ^ cellBits wt.I ∧
      e.ram = a.ram ∧ (∀ m, m ≠ sN → e.rc m = a.rc m) ∧ e.rc sN ≤ (cellN c p wt).length ∧ Sm a e ∧ Fr a e tA) := by
  have hc := cp.cst
  have hN := cp.sN
  have hrc0 : a.rc sN ≤ (cellN c p wt).length := by have := cp.rcur sN; rwa [hN] at this
  have hKL := keyLen_eq c p
  have hVW := valueWidth_eq c p cf.WW
  have hdf := drop_factors c p wt
  rw [← cp.FS] at hdf
  have hg1 : a.env gFS + 1 ≤ (cellN c p wt).length := by
    have := len_of_drop (X := p.factors ++ [p.A, p.Lambda]) (R := witN c p wt) (by rw [hdf]; simp) (by simp)
    omega
  have hFsum : p.factors.sum < 2 ^ C.Wd := by
    have h := cf.DB
    unfold deltaBound at h
    have : p.factors.sum ≤ 2 * (p.M1 + p.A + p.factors.sum + 1) * (c.W + 1) := by
      have h1 : p.M1 + p.A + p.factors.sum + 1 ≤ 2 * (p.M1 + p.A + p.factors.sum + 1) * (c.W + 1) := by
        have := Nat.le_mul_of_pos_right (2 * (p.M1 + p.A + p.factors.sum + 1)) (show 0 < c.W + 1 by omega)
        omega
      omega
    omega
  apply Hx.hs
  -- keys
  refine Hs.then (keys1_spec C a hc p.P p.J cp.P cp.J cf.w1) (fun b1 ⟨v1, k1, s1, f1⟩ n1 hn1 => ?_)
  have F1 : Fr a b1 tA := Fr.weaken f1 (by decide)
  refine Hs.then (keys2_spec C b1 (cstF hc F1 (by decide)) p.J (roleCount c.kind) (Nat.size (p.P + p.J + 3))
    (by rw [F1 gJ (by decide), cp.J]) (by rw [F1 gRC (by decide), cp.rc]) k1 cf.w2 cf.w3)
    (fun b2 ⟨v2, w2, s2, f2⟩ n2 hn2 => ?_)
  have F2 := frA F1 f2 (by decide)
  have s2a : b2.sh = a.sh := by rw [s2, s1]
  obtain ⟨q1, q2⟩ := ram_of_sh s2a
  -- valueWidth
  refine Hs.then (sumF_spec C b2 (cellN c p wt) p.factors _ (a.env gFS) (by rw [q1, hN]) (by rw [q2]; exact hrc0)
    (by rw [F2 gFS (by decide)]) hdf (by rw [F2 wNF (by decide), cp.NF]) hg1 cf.LW hFsum)
    (fun b3 ⟨v3, r3, rc3, ag3⟩ n3 hn3 => ?_)
  have F3 := frA F2 ag3.fr (by decide)
  refine Hs.then (vwA_spec C b3 (cstF hc F3 (by decide)) p.factors.sum p.M1 p.A p.W v3
    (by rw [F3 vM1 (by decide), cp.M1]) (by rw [F3 vA (by decide), cp.A]) (by rw [F3 wW (by decide), cp.W])
    (by have h := cf.DB; unfold deltaBound at h; rw [cf.WW]; exact h)) (fun b4 ⟨v4, s4, f4⟩ n4 hn4 => ?_)
  have F4 := frA F3 f4 (by decide)
  refine Hs.then (vwB_spec C b4 (cstF hc F4 (by decide)) p.k _ (by rw [F4 wK (by decide), cp.K]) v4
    (by rw [← hVW]; have := cf.w4; omega)) (fun b5 ⟨v5, s5, f5⟩ n5 hn5 => ?_)
  have F5 := frA F4 f5 (by decide)
  rw [← hVW] at v5
  -- thresholds
  refine Hs.then (capsP_spec C b5 (cstF hc F5 (by decide)) p.k p.hE p.Lambda (valueWidth c p) Big
    (by rw [F5 wK (by decide), cp.K]) (by rw [F5 vHE (by decide), cp.hE]) (by rw [F5 vLam (by decide), cp.Lam])
    v5 cf.hEB cf.LaB (by have := cf.w4; omega) (lt_pow_of_le (by have := cf.w5; have := cf.kn; omega)))
    (fun b6 ⟨v6h, v6l, s6, f6⟩ n6 hn6 => ?_)
  have F6 := frA F5 f6 (by decide)
  -- digit vectors, cells
  refine Hs.then (bnP_spec C b6 (cstF hc F6 (by decide)) p.hE p.J (roleCount c.kind)
    (by rw [F6 vHE (by decide), cp.hE]) (by rw [F6 gJ (by decide), cp.J]) (by rw [F6 gRC (by decide), cp.rc])
    cf.hE1 (lt_pow_of_le (by have := cf.w5; have := cf.hEn; omega)) cf.rJ cf.bn)
    (fun b7 ⟨v7, s7, f7⟩ n7 hn7 => ?_)
  have F7 := frA F6 f7 (by decide)
  refine Hs.last (ncP_spec C b7 (cstF hc F7 (by decide)) c.n (coordsOf wt.I).length
    (by rw [F7 gN (by decide), cp.n]) (by rw [F7 wCo (by decide), cp.Co]) cf.co (by have := cf.w5; omega))
    (fun b8 ⟨v8, s8, f8⟩ n8 hn8 => ?_)
  have F8 := frA F7 f8 (by decide)
  have s84 : b8.sh = b3.sh := by rw [s8, s7, s6, s5, s4]
  obtain ⟨q8, q8c⟩ := ram_of_sh s84
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [q8, r3, q1], fun m hm => by rw [q8c, ag3.rc m hm, q2],
    by rw [q8c]; exact rc3, Sm.trans (Sm.of_sh s2a) (Sm.trans ⟨ag3.ip, ag3.out, ag3.kin, ag3.kout, ag3.kc⟩
      (Sm.of_sh s84)), F8⟩, ?_⟩
  · rw [f8 vKB (by decide), f7 vKB (by decide), f6 vKB (by decide), f5 vKB (by decide), f4 vKB (by decide),
      ag3.fr vKB (by decide), f2 vKB (by decide)]; exact v1
  · rw [f8 p2K (by decide), f7 p2K (by decide), f6 p2K (by decide), f5 p2K (by decide), f4 p2K (by decide),
      ag3.fr p2K (by decide), v2]; unfold keyW; rw [hKL]; rfl
  · rw [f8 p2KF (by decide), f7 p2KF (by decide), f6 p2KF (by decide), f5 p2KF (by decide), f4 p2KF (by decide),
      ag3.fr p2KF (by decide), w2]; unfold keyW; rw [hKL]; rfl
  · rw [f8 p2VW (by decide), f7 p2VW (by decide), f6 p2VW (by decide)]; exact v5
  · rw [f8 pTH (by decide), f7 pTH (by decide)]; exact v6h
  · rw [f8 pTL (by decide), f7 pTL (by decide)]; exact v6l
  · rw [f8 vBN (by decide), v7]
  · rw [v8, cellBits_eq]
  · unfold costA keyW
    rw [hKL, hVW]
    have e2 : Nat.size (p.P + p.J + 3) = keyBits p := rfl
    rw [e2] at hn2
    have e4 : Nat.size (2 * (p.M1 + p.A + p.factors.sum + 1) * (p.W + 1)) = Nat.size (deltaBound c p) := by
      unfold deltaBound; rw [cf.WW]
    rw [e4] at hn4 hn5 ⊢
    omega

end NearCubicGates.Close.CellsConst

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CellsConst

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-! ## Part B: the request count and the stores -/

def constB : St VV MM := .seq prA (.seq prB (.seq tailSP membP))

def tB : List (Fin VV) := [kE, kQ, kAc, c0, vJ, kU, kX, kP, kI, kT1, pR, kPos, kN, kJ, kF]

/-- The cost of part B. -/
def costB (c : Call) (p : Params) (wt : Wit c.n) : ℕ :=
  (6 * (cellN c p wt).length + (p.primes.sort (· ≤ ·)).length * (7 * (roleCount c.kind * (p.J + 1)) + 14) + 30) +
    8 + (p.J * (6 * (cellN c p wt).length + 9 * p.factors.length + 34) + 4) +
    (c.n * (6 * (cellN c p wt).length + 8 * (coordsOf wt.I).length + 19) + 10) + 3

theorem constB_spec (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (a e : DS VV MM)
    (cp : ConstPre c p wt a) (cf : CF C c p wt Big) (hfr : Fr a e tA) (hram : e.ram = a.ram)
    (hrc : ∀ m, m ≠ sN → e.rc m = a.rc m) (hrcN : e.rc sN ≤ (cellN c p wt).length) :
    Hs C constB e (costB c p wt) (fun f => f.env pR = (reqIds c p).length ∧ f.ram sP = tailL p ∧
      f.ram sR = membL wt.I ∧ (∀ m, m ≠ sP → m ≠ sR → f.ram m = a.ram m) ∧ Sm e f ∧ Fr e f tB) := by
  have hc : Cst e := cstF cp.cst hfr (by decide)
  have hN : e.ram sN = (cellN c p wt) := by rw [hram, cp.sN]
  have hP0 : e.rc sP = 0 := by have := cp.rcur sP; rw [cp.sP0] at this; rw [hrc sP (by decide)]; simpa using this
  have hR0 : e.rc sR = 0 := by have := cp.rcur sR; rw [cp.sR0] at this; rw [hrc sR (by decide)]; simpa using this
  -- the primes
  have hIPr := cp.IPr
  rw [← hfr vIPr (by decide)] at hIPr
  have hi0 : e.env vIPr ≤ (cellN c p wt).length := by
    have := len_of_drop hIPr cf.NP0; omega
  set m := roleCount c.kind * (p.J + 1) with hm
  set S := ((p.primes.sort (· ≤ ·)).map (· ^ m)).sum with hS
  apply Hx.hs
  refine Hs.then (prA_spec C e hc (cellN c p wt) (p.primes.sort (· ≤ ·)) _ (e.env vIPr) p.J (roleCount c.kind) hN hrcN rfl hIPr
    (by rw [hfr vNP (by decide), cp.NP]) hi0 (by rw [hfr gJ (by decide), cp.J]) (by rw [hfr gRC (by decide), cp.rc])
    cf.LW cf.pr1 (by have := cf.prS; omega)) (fun b1 ⟨v1, q1, r1, rc1, ag1⟩ n1 hn1 => ?_)
  have G1 : Fr e b1 tB := Fr.weaken ag1.fr (by decide)
  refine Hs.then (prB_spec C b1 (cstF hc G1 (by decide)) (kindTag c.kind) S m
    (by rw [G1 gKd (by decide), hfr gKd (by decide), cp.kind]) v1 q1 cf.prS) (fun b2 ⟨v2, s2, f2⟩ n2 hn2 => ?_)
  have G2 := frA G1 f2 (by decide)
  obtain ⟨w2, w2c⟩ := ram_of_sh s2
  -- the tail products
  have hdf := drop_factors c p wt
  rw [← cp.FS, ← hfr gFS (by decide)] at hdf
  have hg1 : e.env gFS + 1 ≤ (cellN c p wt).length := by
    have := len_of_drop (X := p.factors ++ [p.A, p.Lambda]) (R := witN c p wt) (by rw [hdf]; simp) (by simp)
    omega
  have hJF : p.J = p.factors.length + 1 := by have := cf.nF; have := cf.J1; omega
  refine Hs.then (tailSP_spec b2 (cstF hc G2 (by decide)) (cellN c p wt) p.factors _ (e.env gFS) p.J (by rw [w2, r1, hN])
    (by rw [w2c]; exact rc1) hdf hg1 (by rw [G2 gFS (by decide)])
    (by rw [G2 wNF (by decide), hfr wNF (by decide), cp.NF]) (by rw [G2 gJ (by decide), hfr gJ (by decide), cp.J])
    hJF (by rw [w2, r1, hram, cp.sP0]) (by rw [w2c, ag1.rc sP (by decide), hP0]) cf.LW
    (lt_pow_of_le (by have := cf.w3; omega)) cf.tprod) (fun b3 ⟨v3, r3, c3, rc3, m3, f3⟩ n3 hn3 => ?_)
  have G3 : Fr e b3 tB := Fr.trans G2 (Fr.weaken f3 (by decide))
  -- the membership vector
  have hco := drop_coords c p wt
  have hfl := fld_iOm c p wt
  have hWS : e.env gWS = iOm (cellN c p wt) + 1 + (coordsOf wt.I).length := by rw [hfr gWS (by decide), cp.WS, hfl]
  have hiOm : iOm (cellN c p wt) + 1 ≤ (cellN c p wt).length := by
    have h := (lay c p wt).wit
    have := len_of_drop (X := witN c p wt) (R := []) (by rw [h]; simp) (by simp [witN])
    have : 0 < (witN c p wt).length := by simp [witN]
    omega
  refine Hs.last (membP_spec b3 (cstF hc G3 (by decide)) (cellN c p wt) (coordsOf wt.I) _ (e.env gWS) c.n
    (by rw [r3 sN (by decide), w2, r1, hN]) rc3 (G3 gWS (by decide)) (by rw [G3 wCo (by decide), hfr wCo (by decide), cp.Co])
    (by omega) (by rw [show e.env gWS - (coordsOf wt.I).length = iOm (cellN c p wt) + 1 by omega]; exact hco)
    (by have := le_of_drop hco hiOm; omega) (by rw [G3 gN (by decide), hfr gN (by decide), cp.n])
    (by rw [r3 sR (by decide), w2, r1, hram, cp.sR0]) (by rw [c3 sR (by decide) (by decide), w2c,
      ag1.rc sR (by decide), hR0]) cf.LW (lt_pow_of_le (by have := cf.w5; omega)))
    (fun b4 ⟨v4, r4, c4, rc4, m4, f4⟩ n4 hn4 => ?_)
  refine ⟨⟨?_, by rw [r4 sP (by decide), v3, tailL_eq p cf.nF], by rw [v4, membL_eq], fun m' h1 h2 => ?_,
    Sm.trans ⟨ag1.ip, ag1.out, ag1.kin, ag1.kout, ag1.kc⟩ (Sm.trans (Sm.of_sh s2) (Sm.trans m3 m4)),
    Fr.trans G3 (Fr.weaken f4 (by decide))⟩, ?_⟩
  · rw [f4 pR (by decide), f3 pR (by decide), v2, reqIds_len]
    split_ifs <;> ring
  · rw [r4 m' h2, r3 m' h1, w2, r1, hram]
  · unfold costB; omega

/-! ## The goal -/

def constP : St VV MM := .seq constA constB

def constCost (C : Ctx) (c : Call) (_p : Params) (Big : ℕ) : ℕ := 4096 * (c.n + Big + C.Wd + 2) ^ 6

theorem cost_le (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (cf : CF C c p wt Big) :
    costA c p wt + costB c p wt + 1 ≤ constCost C c p Big := by
  unfold costA costB constCost
  obtain ⟨M, hM⟩ : ∃ M, M = c.n + Big + C.Wd + 2 := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := by omega
  have hX5 : M ≤ M ^ 5 := by simpa using Nat.pow_le_pow_right hM1 (show 1 ≤ 5 by omega)
  have hX6 : M ^ 6 = M * M ^ 5 := by ring
  have hM2 : M * M ≤ M ^ 6 := by rw [hX6]; exact Nat.mul_le_mul_left _ hX5
  have hX56 : M ^ 5 ≤ M ^ 6 := by rw [hX6]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hMM : M ≤ M * M := Nat.le_mul_of_pos_left _ (by omega)
  have hL : (cellN c p wt).length ≤ 70 * M ^ 5 :=
    cf.Ln.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := cf.w5; omega) 5))
  have hKW : keyW c p ≤ M := by
    have := cf.w2; unfold keyW; rw [keyLen_eq]; omega
  have hSZ : Nat.size (deltaBound c p) ≤ M := by
    have := Nat.size_le.mpr cf.DB; omega
  have hVW : valueWidth c p ≤ M := by have := cf.w4; omega
  have hRJ : roleCount c.kind * p.J ≤ 2 * M := by
    have := Nat.mul_le_mul_right p.J cf.rc2; have := cf.Jn; omega
  have hm : 7 * (roleCount c.kind * (p.J + 1)) + 14 ≤ 28 * M := by
    have := Nat.mul_le_mul_right (p.J + 1) cf.rc2; have := cf.Jn; omega
  have hF : p.factors.length ≤ M := by have := cf.nF; have := cf.Jn; omega
  have hQ : (coordsOf wt.I).length ≤ M := by have := cf.co; omega
  have hNP : (p.primes.sort (· ≤ ·)).length ≤ M := by have := cf.NPn; omega
  have hJ : p.J ≤ M := by have := cf.Jn; omega
  have hn : c.n ≤ M := by omega
  have b1 : (p.primes.sort (· ≤ ·)).length * (7 * (roleCount c.kind * (p.J + 1)) + 14) ≤ M * (28 * M) :=
    Nat.mul_le_mul hNP hm
  have b2 : p.J * (6 * (cellN c p wt).length + 9 * p.factors.length + 34) ≤ M * (420 * M ^ 5 + 9 * M + 34) :=
    Nat.mul_le_mul hJ (by omega)
  have b3 : c.n * (6 * (cellN c p wt).length + 8 * (coordsOf wt.I).length + 19) ≤ M * (420 * M ^ 5 + 8 * M + 19) :=
    Nat.mul_le_mul hn (by omega)
  have e1 : M * (28 * M) = 28 * (M * M) := by ring
  have e2 : M * (420 * M ^ 5 + 9 * M + 34) = 420 * M ^ 6 + 9 * (M * M) + 34 * M := by ring
  have e3 : M * (420 * M ^ 5 + 8 * M + 19) = 420 * M ^ 6 + 8 * (M * M) + 19 * M := by ring
  have hk := cf.kn
  have hP := cf.Pn
  omega

theorem constP_spec : ConstGoal constP constCost := by
  intro C cT c p wt a Big hs ⟨w, hw⟩ ⟨B1, B2, hadm⟩ cp hBig hWd
  have cf := cf_of C c p wt w Big hs hw hadm hBig hWd
  have hA := constA_spec C c p wt Big a cp cf
  have hAB : Hs C constP a (costA c p wt + costB c p wt + 1) (fun f =>
      (f.env vKB = 2 ^ keyBits p ∧ f.env p2K = 2 ^ keyW c p ∧ f.env p2KF = 2 ^ (keyW c p - keyBits p) ∧
        f.env p2VW = 2 ^ valueWidth c p ∧ f.env pTH = min (p.hE ^ (2 * p.k)) (2 ^ valueWidth c p) ∧
        f.env pTL = min (p.Lambda ^ (2 * p.k)) (2 ^ valueWidth c p) ∧ f.env vBN = (wWin p) ^ (nDig c p) ∧
        f.env gNC = 2 ^ cellBits wt.I) ∧ f.env pR = (reqIds c p).length ∧ f.ram sP = tailL p ∧
      f.ram sR = membL wt.I ∧ (∀ m, m ≠ sP → m ≠ sR → f.ram m = a.ram m) ∧ Sm a f ∧ Fr a f (tA ++ tB)) := by
    refine Hs.seq hA (fun e ⟨v1, v2, v3, v4, v5, v6, v7, v8, r, rc, rcN, sm, fr⟩ => ?_)
    refine Hs.mono (constB_spec C c p wt Big a e cp cf fr r rc rcN) le_rfl ?_
    rintro f ⟨u1, u2, u3, u4, u5, u6⟩
    have g : ∀ y, y ∈ tA → y ∉ tB → f.env y = e.env y := fun y _ hy => u6 y hy
    refine ⟨⟨by rw [g vKB (by decide) (by decide)]; exact v1, by rw [g p2K (by decide) (by decide)]; exact v2,
      by rw [g p2KF (by decide) (by decide)]; exact v3, by rw [g p2VW (by decide) (by decide)]; exact v4,
      by rw [g pTH (by decide) (by decide)]; exact v5, by rw [g pTL (by decide) (by decide)]; exact v6,
      by rw [g vBN (by decide) (by decide)]; exact v7, by rw [g gNC (by decide) (by decide)]; exact v8⟩,
      u1, u2, u3, u4, Sm.trans sm u5, Fr.trans (Fr.weaken fr (fun y hy => List.mem_append_left _ hy))
        (Fr.weaken u6 (fun y hy => List.mem_append_right _ hy))⟩
  have hT : ∀ y ∈ tA ++ tB, cScratch y := by
    unfold cScratch gScratch
    decide
  obtain ⟨b, n, hx, hn, ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩, u1, u2, u3, u4, sm, fr⟩ := hAB
  refine ⟨b, n, hx, hn.trans (cost_le C c p wt Big cf), v5, v6, v4, v2, v3, v1, u1, v7, v8, u2, u3, u4,
    hx.rc_le cp.rcur, sm.ip, sm.out, sm.kin, sm.kout, sm.kc, fun x hx' => fr x (fun hm => hx' (hT x hm))⟩

theorem constP_class : ConstClass constCost := ⟨4096, 6, fun _ _ _ _ => le_rfl⟩

end NearCubicGates.Close.CellsConst

