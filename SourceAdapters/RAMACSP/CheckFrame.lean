import SourceAdapters.RAMACSP.CheckClauses

/-!
# Numeric and syntax facts for the affine instance

`def:acsp`, `lem:acsp-degree` and `app:affine-embedding`, "Neighbors", supply
the mathematical context. `frameNeighbors` proves `c_N ≥ 1`, affine slopes
one, and `c_N ≤ 8k_N+q+16C+3`. `frameBounds` proves the field and neighbor
bounds, and the padded-input facts `|x̄| = 2^m`, `1 ≤ m < mH`, `m ≤ τ`,
`|x̄| ≤ K(n+logScale t)` under the length guard.

The estimates use `|H| = 16·N·S·C`, `N=2T`, `S=2^ℓ < 4k_N`, `C=2^d·w`
and `2^f < 8(mH+4)|H|`. Since `m ≤ τ < k_N < mH`, the input subspace fits.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters
open NearCubicWires NearCubicWires.RepairOrdinary Polynomial

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)

/-! ## C4: the neighbors -/

theorem ownInst_cN (r : ClockRequest) :
    (ownInst V irrPoly cons r).cN = (Routing.globalBank (ownLayout V r.2)).length := by
  simp [ACSP.Affine.Instance.cN, ownInst]

/-- `c_N = 8k_N + q + 16C + 3` (`app:affine-embedding` Complete global affine bank). -/
theorem globalBank_length (t : ℕ) :
    (Routing.globalBank (ownLayout V t)).length =
      8 * laneExp V t + colExp V t + 16 * 2 ^ colExp V t + 3 := by
  have hk : 1 ≤ laneExp V t := by unfold laneExp; omega
  simp only [Routing.globalBank, Routing.routingBank, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil, Routing.switchCount, Routing.Layout.C]
  simp only [ownLayout]
  omega

/-- **C4 [J3]** (the neighbor description in `app:affine-embedding`; the identity neighbor gives `c_N ≥ 1`). -/
theorem frameNeighbors (hI : Published.Shoup.IrreducibleChoice irrPoly) : FrameNeighbors V irrPoly cons := by
  intro r _ _
  haveI := ownIrr_fact V irrPoly cons r hI
  have hlen := (ownInst_cN V irrPoly cons r).trans (globalBank_length V r.2)
  refine ⟨by rw [hlen]; omega, fun p hp => ?_⟩
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hp
  change elt (ownIrr V irrPoly cons r) (WireExponent3_5.GF.toPoly 1) ≠ 0
  simp [elt]

/-! ## C3, C8: the bounds -/

/-- `⌈lg t⌉ ≤ τ`. (Copied from the old-route `ShortPCP/Succinct.lean`, `clog_le_timeExp`.) -/
theorem clog_le_tau (t : ℕ) : Nat.clog 2 t ≤ tau V t := by
  unfold tau timeExp
  apply Nat.clog_mono_right
  have := Nat.le_mul_of_pos_left (t + wordWidth (clockConst V) t)
    (show 0 < clockConst V by have := sixteen_le_clockConst V; omega)
  omega

/-- `2^f ≤ K t L^e` gives `f ≤ (K + 1 + e)(L + 1)` (`t < 2^L`). (Copied from the old-route `ShortPCP/Succinct.lean`,
`f_le_of_two_pow`.) -/
theorem f_le_of_two_pow (K e t f : ℕ) (h : 2 ^ f ≤ K * t * logScale t ^ e) :
    f ≤ (K + 1 + e) * (logScale t + 1) := by
  obtain ⟨hL1, -, -, htL⟩ := logScale_facts t
  have hK : K < 2 ^ K := Nat.lt_two_pow_self
  have hLL : logScale t ^ e ≤ 2 ^ (e * logScale t) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le e
  have h1 : K * t ≤ 2 ^ K * 2 ^ logScale t := Nat.mul_le_mul hK.le htL.le
  have h2 : K * t * logScale t ^ e ≤ 2 ^ K * 2 ^ logScale t * 2 ^ (e * logScale t) := Nat.mul_le_mul h1 hLL
  have h3 : 2 ^ f < 2 ^ (K + logScale t + e * logScale t + 1) := by
    rw [pow_succ, pow_add, pow_add]
    have : 0 < 2 ^ K * 2 ^ logScale t * 2 ^ (e * logScale t) := by positivity
    omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  nlinarith

/-- `|H| = 2^{mH} ≤ 128·D·(τ + 1)·w·T` with `D = 2^d` (`lem:acsp-degree` Size of `H`: `16·N·S·C`, `S < 4k_N`). -/
theorem two_pow_domExp_le (t : ℕ) :
    2 ^ domExp V t ≤ 128 * 2 ^ tagExp V * (tau V t + 1) * wordW V t * 2 ^ tau V t := by
  have hS : 2 ^ stageExp V t < 2 * (2 * laneExp V t) := two_pow_clog_lt _ (by unfold laneExp; omega)
  have e : 2 ^ domExp V t = 16 * 2 * 2 ^ tau V t * 2 ^ stageExp V t * (2 ^ tagExp V * wordW V t) := by
    unfold domExp laneExp colExp
    rw [wordW_eq]
    simp only [pow_add, pow_one]
    ring
  rw [e]
  have hS' : 2 ^ stageExp V t ≤ 4 * (tau V t + 1) := by unfold laneExp at hS; omega
  calc 16 * 2 * 2 ^ tau V t * 2 ^ stageExp V t * (2 ^ tagExp V * wordW V t)
      ≤ 16 * 2 * 2 ^ tau V t * (4 * (tau V t + 1)) * (2 ^ tagExp V * wordW V t) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hS')
    _ = 128 * 2 ^ tagExp V * (tau V t + 1) * wordW V t * 2 ^ tau V t := by ring

/-- `mH + 4 ≤ (d + 11)(τ + w + 1)`. -/
theorem domExp_add_four_le (t : ℕ) :
    domExp V t + 4 ≤ (tagExp V + 11) * (tau V t + wordW V t + 1) := by
  have hl : stageExp V t ≤ 2 * laneExp V t := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hw : wordExp V t ≤ wordW V t := by rw [wordW_eq]; exact (Nat.lt_two_pow_self).le
  unfold domExp colExp laneExp at *
  nlinarith

/-- `|x̄| ≤ (4c + 6)(n + logScale t)` (`app:affine-embedding`; copied argument of the old-route `clock_xbar`). -/
theorem xbar_length_le (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (ownXbar V r).length ≤ (4 * clockConst V + 6) * (r.1.1 + logScale r.2) := by
  have h16 := sixteen_le_clockConst V
  obtain ⟨h1, -, h3, -⟩ := inputPad_facts (clockConst V) r.1.1 r.2 h16 (by omega) hnt
  have hlen : (ownXbar V r).length = inputPadLength (clockConst V) r.1.1 r.2 :=
    padInput_length (clockConst V) r.2 r.1.2 h1
  have hw := wordWidth_lt (clockConst V) r.2 (by omega)
  have hL := (logScale_facts r.2).2.1
  have hL1 := (logScale_facts r.2).1
  rw [hlen]
  generalize inputPadLength (clockConst V) r.1.1 r.2 = P at h3 ⊢
  generalize wordWidth (clockConst V) r.2 = w at h3 hw
  generalize logScale r.2 = L at hL hL1 ⊢
  generalize Nat.clog 2 r.2 = g at hL hw
  generalize clockConst V = c at h16 h3 hw ⊢
  generalize r.1.1 = n at hn h3 ⊢
  have e : (4 * c + 6) * (n + L) = 4 * c * n + 6 * n + 4 * c * L + 6 * L := by ring
  have a1 : 4 * c * 2 ≤ 4 * c * n := Nat.mul_le_mul_left _ hn
  have a2 : 4 * c * 1 ≤ 4 * c * L := Nat.mul_le_mul_left _ hL1
  omega

/-- **C3 [J5] and C8 [J1, J5, M2]** (`lem:acsp-degree` Size of `H`, `app:affine-embedding` `c_N = O(log T)`, `def:acsp`). -/
theorem frameBounds : FrameBounds V irrPoly cons := by
  have h16 := sixteen_le_clockConst V
  obtain ⟨Ka, ea, hF⟩ := field_instantiation (1024 * (tagExp V + 11) * 2 ^ tagExp V) 1 (clockConst V) 1 1
    (by omega)
  obtain ⟨Kc, hN⟩ := neighbor_instantiation (16 * 2 ^ tagExp V + tagExp V + 11) 1 (clockConst V) (by omega)
  refine ⟨Ka + 1 + ea + Kc + (16 * 2 ^ tagExp V + tagExp V + 11) * (2 * clockConst V + 3) +
    (4 * clockConst V + 6), ea, fun r hn hnt => ?_⟩
  have ht : 1 ≤ r.2 := by omega
  have eτ : tau V r.2 = timeExp (clockConst V) r.2 := rfl
  have ew : wordW V r.2 = wordWidth (clockConst V) r.2 := rfl
  -- 2^f ≤ C (τ + w + 1)(τ + 1)(w + 1) 2^τ
  have hB : 2 ^ fieldExp V r.2 ≤ 1024 * (tagExp V + 11) * 2 ^ tagExp V *
      (tau V r.2 + 1 * wordW V r.2 + 1) * (tau V r.2 + 1) * (wordW V r.2 + 1) * 2 ^ tau V r.2 := by
    have h1 := two_pow_fieldExp_lt V r.2
    have h2 := two_pow_domExp_le V r.2
    have h3 := domExp_add_four_le V r.2
    calc 2 ^ fieldExp V r.2 ≤ 8 * (domExp V r.2 + 4) * 2 ^ domExp V r.2 := h1.le
      _ ≤ 8 * ((tagExp V + 11) * (tau V r.2 + wordW V r.2 + 1)) *
          (128 * 2 ^ tagExp V * (tau V r.2 + 1) * wordW V r.2 * 2 ^ tau V r.2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h2
      _ = (1024 * (tagExp V + 11) * 2 ^ tagExp V * (tau V r.2 + 1 * wordW V r.2 + 1) * (tau V r.2 + 1) *
          2 ^ tau V r.2) * wordW V r.2 := by ring
      _ ≤ (1024 * (tagExp V + 11) * 2 ^ tagExp V * (tau V r.2 + 1 * wordW V r.2 + 1) * (tau V r.2 + 1) *
          2 ^ tau V r.2) * (wordW V r.2 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  rw [eτ, ew] at hB
  have hFa := hF r.2 (fieldExp V r.2) (wordWidth (clockConst V) r.2) ht (by simp) hB
  have hfL := f_le_of_two_pow Ka ea r.2 _ hFa
  -- c_N
  have hcN := (ownInst_cN V irrPoly cons r).trans (globalBank_length V r.2)
  have hq : 2 ^ colExp V r.2 = 2 ^ tagExp V * wordW V r.2 := by
    unfold colExp; rw [pow_add, wordW_eq]
  have hωw : wordExp V r.2 ≤ wordW V r.2 := by rw [wordW_eq]; exact (Nat.lt_two_pow_self).le
  have hcN' : (ownInst V irrPoly cons r).cN ≤
      (16 * 2 ^ tagExp V + tagExp V + 11) * (tau V r.2 + 1 * wordW V r.2 + 1) := by
    rw [hcN, hq]; unfold laneExp colExp
    have e : (16 * 2 ^ tagExp V + tagExp V + 11) * (tau V r.2 + 1 * wordW V r.2 + 1) =
        16 * (2 ^ tagExp V * (tau V r.2 + wordW V r.2 + 1)) + tagExp V * (tau V r.2 + wordW V r.2 + 1) +
          11 * (tau V r.2 + wordW V r.2 + 1) := by ring
    have a1 : tagExp V ≤ tagExp V * (tau V r.2 + wordW V r.2 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have a2 : 2 ^ tagExp V * wordW V r.2 ≤ 2 ^ tagExp V * (tau V r.2 + wordW V r.2 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [e]; omega
  have hcNL := hN r.2 _ ht hcN'
  have hτf : tau V r.2 + 1 ≤ fieldExp V r.2 := by
    have := tau_lt_domExp V r.2; have := domExp_add_two_le_fieldExp V r.2; omega
  have hwf : tau V r.2 + 1 * wordW V r.2 + 1 ≤ (2 * clockConst V + 3) * fieldExp V r.2 := by
    have hw := wordWidth_lt (clockConst V) r.2 (by omega)
    have hcl := clog_le_tau V r.2
    rw [← ew] at hw
    have e : (2 * clockConst V + 3) * fieldExp V r.2 = 2 * (clockConst V * fieldExp V r.2) + 3 * fieldExp V r.2 := by
      ring
    have a1 : clockConst V * 1 ≤ clockConst V * fieldExp V r.2 := Nat.mul_le_mul_left _ (by omega)
    rw [e]; omega
  have hcNf : (ownInst V irrPoly cons r).cN ≤
      (16 * 2 ^ tagExp V + tagExp V + 11) * (2 * clockConst V + 3) * fieldExp V r.2 := by
    rw [Nat.mul_assoc]; exact hcN'.trans (Nat.mul_le_mul_left _ hwf)
  have hL := (logScale_facts r.2).1
  obtain ⟨hx1, hm1, -, hmτ, -⟩ := inExp_facts V r hn hnt
  set Kt := Ka + 1 + ea + Kc + (16 * 2 ^ tagExp V + tagExp V + 11) * (2 * clockConst V + 3) +
    (4 * clockConst V + 6) with hKt
  refine ⟨⟨hFa.trans ?_, hfL.trans (Nat.mul_le_mul_right _ (by omega)),
    hcNL.trans (Nat.mul_le_mul_right _ (by omega)), hcNf.trans (Nat.mul_le_mul_right _ (by omega))⟩,
    ⟨⟨by rw [ownInst_m]; exact hx1, by rw [ownInst_m]; exact hm1, ?_⟩,
      (xbar_length_le V r hn hnt).trans (Nat.mul_le_mul_right _ (by omega))⟩⟩
  · rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  · rw [ownInst_m]
    change inExp V r < (ownInst V irrPoly cons r).hBasis.length
    rw [ownInst_hBasis_length]
    have := tau_lt_domExp V r.2
    omega

/-! ## C2 without the degree conjunct: syntax, `H` and the selected input space (the instance conditions of `def:acsp`) -/

/-- An affine element is the class of `offset + Σ_{c_j} basis_j`. -/
theorem affineElt_eq_mk (irr : (ZMod 2)[X]) (κ : ℕ) (basis : ℕ → (ZMod 2)[X]) (offset : (ZMod 2)[X])
    (c : Fin κ → Bool) :
    affineElt irr κ basis offset c =
      AdjoinRoot.mk irr (offset + ∑ j : Fin κ, if c j then basis j else 0) := by
  simp only [affineElt, elt, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The affine element depends only on the first `κ` basis entries. -/
theorem affineElt_congr (irr : (ZMod 2)[X]) (κ : ℕ) (b b' : ℕ → (ZMod 2)[X]) (offset : (ZMod 2)[X])
    (h : ∀ j < κ, b j = b' j) : affineElt irr κ b offset = affineElt irr κ b' offset := by
  funext c
  simp only [affineElt]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j j.isLt]

/-- Polynomials of degree `< deg irr` are distinct modulo `irr`. -/
theorem mk_injOn (irr p q : (ZMod 2)[X]) (hirr : irr ≠ 0) (hp : p.degree < irr.natDegree)
    (hq : q.degree < irr.natDegree) (h : AdjoinRoot.mk irr p = AdjoinRoot.mk irr q) : p = q := by
  rw [AdjoinRoot.mk_eq_mk] at h
  have hdeg : (p - q).degree < irr.degree := by
    rw [Polynomial.degree_eq_natDegree hirr]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hq)
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt h hdeg)

/-- The monomial sum `Σ_{c_j} X^{p_j}`. -/
def monoSum (κ : ℕ) (p : ℕ → ℕ) (c : Fin κ → Bool) : (ZMod 2)[X] :=
  ∑ j : Fin κ, if c j then (X : (ZMod 2)[X]) ^ p j else 0

theorem monoSum_coeff (κ : ℕ) (p : ℕ → ℕ) (hp : ∀ i j, i < κ → j < κ → p i = p j → i = j)
    (c : Fin κ → Bool) (j : Fin κ) : (monoSum κ p c).coeff (p j) = if c j then 1 else 0 := by
  unfold monoSum
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro i _ hij
    split_ifs
    · rw [Polynomial.coeff_X_pow, if_neg]
      intro h; exact hij (Fin.ext (hp _ _ i.isLt j.isLt h.symm))
    · simp
  · simp

theorem monoSum_degree (κ : ℕ) (p : ℕ → ℕ) (B : ℕ) (hB : ∀ j < κ, p j < B) (c : Fin κ → Bool) :
    (monoSum κ p c).degree < B := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  unfold monoSum
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs
  · rw [Polynomial.coeff_X_pow, if_neg]; have := hB j j.isLt; omega
  · simp

/-- A monomial affine element is the class of `o + Σ_{c_j} X^{p_j}`. -/
theorem affineElt_mono_eq (irr : (ZMod 2)[X]) (κ : ℕ) (p : ℕ → ℕ) (o : (ZMod 2)[X]) (c : Fin κ → Bool) :
    affineElt irr κ (fun j => X ^ p j) o c = AdjoinRoot.mk irr (o + monoSum κ p c) := by
  rw [affineElt_eq_mk]; rfl

/-- **Independence of a monomial affine subspace** (`app:affine-embedding` These monomials are `F₂`-independent; the instance conditions of `def:acsp`). -/
theorem affine_mono_injective (irr : (ZMod 2)[X]) (hirr : irr ≠ 0) (κ : ℕ) (p : ℕ → ℕ)
    (hp : ∀ i j, i < κ → j < κ → p i = p j → i = j) (hdeg : ∀ j < κ, p j < irr.natDegree)
    (o : (ZMod 2)[X]) : Function.Injective (affineElt irr κ (fun j => X ^ p j) o) := by
  intro c c' h
  rw [affineElt_eq_mk, affineElt_eq_mk, AdjoinRoot.mk_eq_mk, add_sub_add_left_eq_sub,
    ← AdjoinRoot.mk_eq_mk] at h
  have h' := mk_injOn irr _ _ hirr (monoSum_degree κ p _ hdeg c) (monoSum_degree κ p _ hdeg c') h
  funext j
  have := congrArg (fun q => Polynomial.coeff q (p j)) h'
  simp only [monoSum_coeff κ p hp] at this
  cases hc : c j <;> cases hc' : c' j <;> simp_all
/-- Every polynomial of degree `< mH` is a point of `H` when `H` has the monomial basis and offset `0`. -/
theorem hElt_surj (s : ACSP.Affine.Instance) (hb : ∀ j < s.mH, s.hBasisPoly j = X ^ j)
    (ho : WireExponent3_5.GF.toPoly s.hOffset = 0)
    (P : (ZMod 2)[X]) (hP : P.degree < s.mH) : ∃ c', s.hElt c' = AdjoinRoot.mk s.irrPoly P := by
  refine ⟨fun j => decide (P.coeff j = 1), ?_⟩
  unfold ACSP.Affine.Instance.hElt
  rw [affineElt_congr s.irrPoly s.mH s.hBasisPoly (fun j => X ^ j) (WireExponent3_5.GF.toPoly s.hOffset) hb, affineElt_eq_mk, ho, zero_add]
  congr 1
  have hdeg := monoSum_degree s.mH id s.mH (fun j hj => hj) (fun j : Fin s.mH => decide (P.coeff j = 1))
  ext m
  by_cases hm : m < s.mH
  · have := monoSum_coeff s.mH id (fun i j _ _ h => h) (fun j : Fin s.mH => decide (P.coeff j = 1)) ⟨m, hm⟩
    simp only [id] at this
    change (monoSum s.mH id _).coeff m = _ at this
    rw [show (∑ j : Fin s.mH, if decide (P.coeff ↑j = 1) = true then (X : (ZMod 2)[X]) ^ (j : ℕ) else 0) =
      monoSum s.mH id (fun j : Fin s.mH => decide (P.coeff j = 1)) from rfl, this]
    have h01 : P.coeff m = 0 ∨ P.coeff m = 1 := by
      rcases WireExponent3_5.GF.zmod2_ne_zero (P.coeff m) |> fun h => (em (P.coeff m = 0)).imp_right h with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h01 with h | h <;> simp [h]
  · rw [show (∑ j : Fin s.mH, if decide (P.coeff ↑j = 1) = true then (X : (ZMod 2)[X]) ^ (j : ℕ) else 0) =
      monoSum s.mH id (fun j : Fin s.mH => decide (P.coeff j = 1)) from rfl,
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.mp hm)),
      Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hP (by exact_mod_cast not_lt.mp hm))]

/-- A monomial input basis and an offset of degree below mH lie in the
monomial span H, for every coefficient vector. -/
theorem input_contained_of_monomials (s : ACSP.Affine.Instance) (p : ℕ → ℕ)
    (hbH : ∀ j < s.mH, s.hBasisPoly j = X ^ j)
    (hoH : WireExponent3_5.GF.toPoly s.hOffset = 0)
    (hbI : ∀ j < s.m, s.iBasisPoly j = X ^ p j)
    (hp : ∀ j < s.m, p j < s.mH)
    (hOff : (WireExponent3_5.GF.toPoly s.iOffset).degree < s.mH) :
    ∀ c, ∃ c', s.iEltOf c = s.hElt c' := by
  intro c
  unfold ACSP.Affine.Instance.iEltOf
  rw [affineElt_congr _ _ _ _ _ hbI, affineElt_mono_eq]
  have hSum := monoSum_degree s.m p s.mH hp c
  have hP : (WireExponent3_5.GF.toPoly s.iOffset + monoSum s.m p c).degree < s.mH :=
    (Polynomial.degree_add_le _ _).trans_lt (max_lt hOff hSum)
  obtain ⟨c', hc'⟩ := hElt_surj s hbH hoH _ hP
  exact ⟨c', hc'.symm⟩

/-- The position of basis entry j in the direct column-first input basis. -/
def inPos (r : ClockRequest) (j : ℕ) : ℕ :=
  if j < wordExp V r.2 then laneExp V r.2 + stageExp V r.2 + j else j - wordExp V r.2

theorem ownInst_hOffset (r : ClockRequest) : (ownInst V irrPoly cons r).hOffset = 0 := rfl

theorem ownInst_irr (r : ClockRequest) :
    (ownInst V irrPoly cons r).irr = modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2) := rfl

theorem ownInst_hBasis_list (r : ClockRequest) :
    (ownInst V irrPoly cons r).hBasis = (List.range (domExp V r.2)).map (2 ^ ·) := rfl

theorem inputBasisMasks_getD (r : ClockRequest) (j : ℕ) (hj : j < inExp V r) :
    (inputBasisMasks V r).getD j 0 = 2 ^ inPos V r j := by
  unfold inputBasisMasks inPos
  rw [List.getD_eq_getElem?_getD]
  by_cases hjw : j < wordExp V r.2
  · rw [if_pos hjw, List.getElem?_append_left (by simpa using hjw), List.getElem?_map, List.getElem?_range hjw,
      Option.map_some, Option.getD_some]
  · rw [if_neg hjw, List.getElem?_append_right (by simp; omega)]
    have hj' : j - wordExp V r.2 < inExp V r - wordExp V r.2 := by
      have := wordExp_le_inExp V r
      omega
    simp only [List.length_map, List.length_range]
    rw [List.getElem?_map, List.getElem?_range hj', Option.map_some, Option.getD_some]

theorem inPos_lt (r : ClockRequest) (j : ℕ) (hm : inExp V r ≤ tau V r.2) (hj : j < inExp V r) :
    inPos V r j < domExp V r.2 := by
  unfold inPos domExp colExp laneExp
  split_ifs <;> omega

theorem inPos_inj (r : ClockRequest) (hm : inExp V r ≤ tau V r.2) :
    ∀ i j, i < inExp V r → j < inExp V r → inPos V r i = inPos V r j → i = j := by
  intro i j hi hj
  unfold inPos laneExp
  split_ifs <;> omega

theorem inputOffsetMask_lt (r : ClockRequest) : inputOffsetMask V r < 2 ^ domExp V r.2 :=
  Nat.pow_lt_pow_right (by norm_num) (tau_lt_domExp V r.2)

/-- The frame and its selected input subspace satisfy all guarded geometric clauses.
The arbitrary constraint circuit's constants are supplied separately. -/
theorem frameSyntax (hI : Published.Shoup.IrreducibleChoice irrPoly) : FrameSyntax V irrPoly cons := by
  intro r hn hnt
  obtain ⟨hirr, hdeg⟩ := ownIrr_irreducible V irrPoly cons r hI
  have hf1 : 1 ≤ fieldExp V r.2 := by have := domExp_add_two_le_fieldExp V r.2; omega
  have hmf := domExp_add_two_le_fieldExp V r.2
  have hirrP := hI _ hf1
  have hsm : (ownInst V irrPoly cons r).mH = domExp V r.2 := by
    exact ownInst_hBasis_length V irrPoly cons r
  have hsi := ownInst_m V irrPoly cons r
  have hmτ : inExp V r ≤ tau V r.2 := (inExp_facts V r hn hnt).2.2.2.1.le
  have hpow : ∀ b, b < domExp V r.2 → 2 ^ b < 2 ^ fieldExp V r.2 :=
    fun b hb => Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdomf : 2 ^ domExp V r.2 ≤ 2 ^ fieldExp V r.2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbH : ∀ j < (ownInst V irrPoly cons r).mH, (ownInst V irrPoly cons r).hBasisPoly j = X ^ j := by
    intro j hj
    rw [hsm] at hj
    unfold ACSP.Affine.Instance.hBasisPoly
    rw [ownInst_hBasis_getD V irrPoly cons r j hj, WireExponent3_5.GF.toPoly_two_pow]
  have hoH : WireExponent3_5.GF.toPoly (ownInst V irrPoly cons r).hOffset = 0 := by
    rw [ownInst_hOffset]; simp [WireExponent3_5.GF.toPoly]
  have hbI : ∀ j < (ownInst V irrPoly cons r).m,
      (ownInst V irrPoly cons r).iBasisPoly j = X ^ inPos V r j := by
    intro j hj
    rw [hsi] at hj
    rw [ownInst_iBasis V irrPoly cons r j hj, WireExponent3_5.GF.toPoly_two_pow]
    rfl
  refine ⟨?_, hirr, hdeg, ?_, ?_, ?_⟩
  · dsimp only [FrameMasks]
    rw [ownInst_f, ownInst_irr, ownInst_hOffset]
    refine ⟨?_, WireExponent3_5.GF.ofPoly_lt _ _, ?_, Nat.two_pow_pos _,
      clause_nbr_consts V irrPoly cons r, ?_, (inputOffsetMask_lt V r).trans_le hdomf⟩
    · rw [modMask, WireExponent3_5.GF.ofPoly, WireExponent3_5.GF.testBit_equivBitIndices_symm]
      simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
      refine ⟨Nat.lt_succ_self _, ?_⟩
      have hc := Polynomial.coeff_natDegree (p := irrPoly (fieldExp V r.2))
      rw [hirrP.2] at hc
      rw [hc]; exact Polynomial.leadingCoeff_ne_zero.mpr hirrP.1.ne_zero
    · intro a ha
      rw [ownInst_hBasis_list] at ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hpow b (List.mem_range.mp hb)
    · intro a ha
      rw [ownInst_iBasis_list] at ha
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      have hj' : j < inExp V r := by rwa [inputBasisMasks_length] at hj
      have he := inputBasisMasks_getD V r j hj'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at he
      rw [he]
      exact hpow _ (inPos_lt V r j hmτ hj')
  · unfold ACSP.AffineIndependent
    rw [affineElt_congr _ _ _ (fun j => X ^ j) _ hbH, hoH]
    exact affine_mono_injective _ hirr.ne_zero _ id (fun i j _ _ h => h)
      (fun j hj => by rw [hsm] at hj; rw [hdeg]; simp only [id]; omega) 0
  · unfold ACSP.AffineIndependent
    rw [affineElt_congr _ _ _ _ _ hbI]
    apply affine_mono_injective _ hirr.ne_zero
    · intro i j hi hj hij
      rw [hsi] at hi hj
      exact inPos_inj V r hmτ i j hi hj hij
    · intro j hj
      rw [hsi] at hj
      rw [hdeg]
      have := inPos_lt V r j hmτ hj
      omega
  · apply input_contained_of_monomials _ (inPos V r) hbH hoH hbI
    · intro j hj
      rw [hsi] at hj
      rw [hsm]
      exact inPos_lt V r j hmτ hj
    · rw [hsm]
      exact WireExponent3_5.GF.degree_toPoly_lt _ _ (inputOffsetMask_lt V r)

end NearCubicGates.Adapters.RAMACSP
