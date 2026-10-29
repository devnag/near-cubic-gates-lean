import SourceAdapters.ShortPCP.Proximity
import Mathlib.Algebra.Polynomial.Roots

/-!
# The verifier with single sub-verifier runs

The proof of `thm:short-pcp-ours`, Step 2, uses five tables over F and runs
each proximity sub-verifier once on a prefix of a shared random string. Its
completeness and four-case soundness argument are proved here for generic
`StrongPCPP` sub-verifiers and an `ACSPInstance` satisfying `Good`.

Construction 8.5 of BCGT13 supplies the arrangement of the tests; parameter
instantiation is explicit data, and its consistency test is `consist`.
The current paper's affine instance and the degree bound d_H for the composition
table are supplied when this generic verifier is instantiated.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP

open Finset Polynomial NearCubicGates.Published.BCGT13

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The sACSP instance as P04 consumes it -/

/-- One sACSP instance `(x, 1^t)` with its parameters (BCGT13 Def 7.1): `H = H_t`, `I = I_{t, log|x|}`, the
neighbors `N_{t,i}`, the constraint `P_t` (as a function `F × F^{c_N} → F`), the degree bound `dA = 2^{mH} − 1` of
the assignment, the degree bound `dB` of `B = P_t(x, A∘N_1, …)` (proof of `thm:short-pcp-ours`), and the evaluation
`px` of the low-degree extension of `x` over `I` (Construction 8.5 step 5). -/
structure ACSPInstance (F : Type) where
  H : Finset F
  I : Finset F
  cN : ℕ
  nbr : Fin cN → F → F
  P : F → (Fin cN → F) → F
  dA : ℕ
  dB : ℕ
  px : F → F

namespace ACSPInstance

variable (D : ACSPInstance F)

/-- Membership `(x, 1^t) ∈ sACSP(par)` (BCGT13 Def 7.1): an assignment polynomial of degree at most `dA` that
satisfies the constraint on `H` (item (i)) and agrees with the instance on `I` (item (ii), through `px`). -/
def Mem : Prop :=
  ∃ A : F[X], A.natDegree ≤ D.dA ∧ (∀ α ∈ D.H, D.P α (fun i => A.eval (D.nbr i α)) = 0) ∧
    ∀ α ∈ D.I, A.eval α = D.px α

/-- The instance hypotheses used by the generic verifier. -/
structure Good : Prop where
  /-- `c_N ≥ 1` (proof of `thm:short-pcp-ours`). -/
  cN_pos : 1 ≤ D.cN
  /-- J3: each neighbor is a nonconstant affine map, hence a bijection. The instances used in
Step 1 of the proof of `thm:short-pcp-ours` have translation neighbors. -/
  nbr_inj : ∀ i, Function.Injective (D.nbr i)
  /-- `px` is the evaluation of a polynomial of degree at most `dA` (the low-degree extension over `I`, J1). -/
  px_low : ∃ Px : F[X], Px.natDegree ≤ D.dA ∧ ∀ α, D.px α = Px.eval α
  /-- J4: `deg B ≤ dB` for every assignment of degree at most `dA`. -/
  B_low : ∀ A : F[X], A.natDegree ≤ D.dA →
    ∃ Bp : F[X], Bp.natDegree ≤ D.dB ∧ ∀ α, Bp.eval α = D.P α (fun i => A.eval (D.nbr i α))
  /-- `dA < 3|F|/4` (uniqueness of `A`, `A′` in Case 4; BCGT13 Remark 8.6 has `dA < |F|/4` under J2). -/
  dA_small : 4 * D.dA < 3 * Fintype.card F
  /-- `dB ≤ |F|/2` (Case 4; BCGT13 uses `dB ≤ |F|/4` from Eq. (3), which needs J2 when `dB ≥ |H|`). -/
  dB_small : 2 * D.dB ≤ Fintype.card F

end ACSPInstance

/-! ## The verifier `V0` -/

/-- The three single-run proximity verifiers of Steps 2, 3, 5 and the encoding of `F` by `f` coins used by the
consistency test of Step 4 ("The consistency test uses f bits", proof of `thm:short-pcp-ours`). -/
structure SubVerifiers (D : ACSPInstance F) (sR sH sI : ℝ) where
  f : ℕ
  elem : (Fin f → Bool) ≃ F
  VR : StrongPCPP F univ (RS univ D.dA) sR
  VH : StrongPCPP F univ (VRS univ D.H D.dB) sH
  VI : StrongPCPP F univ (VRS univ D.I D.dA) sI

namespace SubVerifiers

variable {D : ACSPInstance F} {sR sH sI : ℝ} (W : SubVerifiers D sR sH sI)

/-- `r0`: "As the steps share their random string" the shared length is the maximum (proof of `thm:short-pcp-ours`). -/
def r0 : ℕ := max (max W.VR.rand W.VH.rand) (max W.f W.VI.rand)

theorem le_r0_R : W.VR.rand ≤ W.r0 := by unfold r0; omega
theorem le_r0_H : W.VH.rand ≤ W.r0 := by unfold r0; omega
theorem le_r0_f : W.f ≤ W.r0 := by unfold r0; omega
theorem le_r0_I : W.VI.rand ≤ W.r0 := by unfold r0; omega

end SubVerifiers

/-- BCGT13 Definition 8.4: "π = (p0, π0, p1, π1, πc)". -/
structure ProofTable {D : ACSPInstance F} {sR sH sI : ℝ} (W : SubVerifiers D sR sH sI) where
  p0 : F → F
  π0 : Fin W.VR.length → F
  p1 : F → F
  π1 : Fin W.VH.length → F
  πc : Fin W.VI.length → F

/-- Construction 8.5 Step 4: "Verify that p1(α) = ω" with `ω = P_t(α, p0(α_1), …, p0(α_{c_N}))`. -/
def consist (D : ACSPInstance F) (p0 p1 : F → F) (a : F) : Bool :=
  decide (p1 a = D.P a fun i => p0 (D.nbr i a))

namespace SubVerifiers

variable {D : ACSPInstance F} {sR sH sI : ℝ} (W : SubVerifiers D sR sH sI)

/-- `V0` on coins `R ∈ {0,1}^r` for any `r` at least every sub-verifier's randomness: Steps 2, 3, 4, 5 of
Construction 8.5, each sub-verifier run once on a prefix of `R` (proof of `thm:short-pcp-ours`); `V0` "rejects whenever one of its
steps rejects" (proof of `thm:short-pcp-ours`). -/
def acceptsAt (r : ℕ) (hR : W.VR.rand ≤ r) (hH : W.VH.rand ≤ r) (hf : W.f ≤ r) (hI : W.VI.rand ≤ r)
    (pf : ProofTable W) (R : Fin r → Bool) : Bool :=
  W.VR.accepts pf.p0 pf.π0 (pre W.VR.rand hR R) &&
  W.VH.accepts pf.p1 pf.π1 (pre W.VH.rand hH R) &&
  consist D pf.p0 pf.p1 (W.elem (pre W.f hf R)) &&
  W.VI.accepts (fun a => pf.p0 a - D.px a) pf.πc (pre W.VI.rand hI R)

/-- **`V0`** on coins `R ∈ {0,1}^{r0}` (`r0` the maximum, proof of `thm:short-pcp-ours`). -/
def accepts (pf : ProofTable W) (R : Fin W.r0 → Bool) : Bool :=
  W.acceptsAt W.r0 W.le_r0_R W.le_r0_H W.le_r0_f W.le_r0_I pf R

end SubVerifiers

/-! ## Generic counting facts -/

theorem acceptFrac_mono {r : ℕ} {t u : (Fin r → Bool) → Bool} (h : ∀ R, t R = true → u R = true) :
    acceptFrac t ≤ acceptFrac u := by
  unfold acceptFrac
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card fun R hR => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢; exact h R hR

omit [Field F] [DecidableEq F] in
/-- The acceptance fraction of the consistency test through the coin encoding of `F`. -/
theorem acceptFrac_elem {f : ℕ} (e : (Fin f → Bool) ≃ F) (t : F → Bool) :
    acceptFrac (fun c => t (e c)) =
      ((univ.filter fun a => t a = true).card : ℝ) / (Fintype.card F : ℝ) := by
  unfold acceptFrac
  have hcard : (Fintype.card F : ℝ) = (2 : ℝ) ^ f := by
    rw [← Fintype.card_congr e]; simp
  rw [hcard]
  congr 2
  rw [← Finset.card_map ⟨e, e.injective⟩]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact hc
  · intro ha; exact ⟨e.symm a, by simpa using ha, by simp⟩

/-- Two distinct polynomials of degree at most `d` agree on at most `d` points (BCGT13 Lemma 4.10). -/
theorem card_agree_le {P Q : F[X]} {d : ℕ} (hPQ : P ≠ Q) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) :
    (univ.filter fun a => P.eval a = Q.eval a).card ≤ d := by
  by_contra hlt
  push Not at hlt
  apply hPQ
  have h0 : P - Q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (P - Q)
      (univ.filter fun a => P.eval a = Q.eval a)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp [ha]
    · exact lt_of_le_of_lt ((natDegree_sub_le P Q).trans (max_le hP hQ)) hlt
  exact sub_eq_zero.mp h0

/-- `fracDist univ p q ≤ δ` bounds the number of disagreements by `δ·|F|`. -/
theorem card_ne_le_of_fracDist {p q : F → F} {δ : ℝ} (h : fracDist univ p q ≤ δ) :
    ((univ.filter fun a => p a ≠ q a).card : ℝ) ≤ δ * Fintype.card F := by
  unfold fracDist at h
  have hpos : (0 : ℝ) < (univ : Finset F).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, Finset.mem_univ _⟩
  rw [div_le_iff₀ hpos] at h
  simpa using h

/-! ## Completeness (proof of `thm:short-pcp-ours`) -/

namespace SubVerifiers

variable {D : ACSPInstance F} {sR sH sI : ℝ} (W : SubVerifiers D sR sH sI)

/-- **Completeness.** For the generic verifier in this file, the assignment and composition tables
are `p0 = A` and `p1 = B`, with proximity proofs from BCGT13 Construction 8.3. Perfect completeness
of the strong single-run verifiers (Definition 4.15) and the consistency identity make every test accept
on every random string. The affine instance of this argument is Step 2, “Completeness”, in the proof
of `thm:short-pcp-ours`. -/
theorem completeAt (hG : D.Good) (hmem : D.Mem) : ∃ pf : ProofTable W,
    ∀ (r : ℕ) (hR : W.VR.rand ≤ r) (hH : W.VH.rand ≤ r) (hf : W.f ≤ r) (hI : W.VI.rand ≤ r) (R : Fin r → Bool),
      W.acceptsAt r hR hH hf hI pf R = true := by
  obtain ⟨A, hAdeg, hAH, hAI⟩ := hmem
  obtain ⟨Px, hPxdeg, hPx⟩ := hG.px_low
  obtain ⟨Bp, hBdeg, hBp⟩ := hG.B_low A hAdeg
  have h0 : (fun a => A.eval a) ∈ RS univ D.dA := ⟨A, hAdeg, fun s _ => rfl⟩
  have h1 : (fun a => Bp.eval a) ∈ VRS univ D.H D.dB :=
    ⟨Bp, hBdeg, fun s _ => rfl, fun h hh => by rw [hBp]; exact hAH h hh⟩
  have hc : (fun a => A.eval a - D.px a) ∈ VRS univ D.I D.dA := by
    refine ⟨A - Px, (natDegree_sub_le A Px).trans (max_le hAdeg hPxdeg), fun s _ => by simp [hPx], ?_⟩
    intro h hh
    simp [← hPx, hAI h hh]
  obtain ⟨π0, hπ0⟩ := W.VR.complete _ h0
  obtain ⟨π1, hπ1⟩ := W.VH.complete _ h1
  obtain ⟨πc, hπc⟩ := W.VI.complete _ hc
  refine ⟨⟨fun a => A.eval a, π0, fun a => Bp.eval a, π1, πc⟩, fun r hR hH hf hI R => ?_⟩
  simp only [acceptsAt, hπ0, hπ1, hπc, Bool.true_and, Bool.and_true, consist, decide_eq_true_eq]
  exact hBp _

/-- **Completeness** at `r0`. -/
theorem complete (hG : D.Good) (hmem : D.Mem) : ∃ pf : ProofTable W, ∀ R, W.accepts pf R = true := by
  obtain ⟨pf, h⟩ := W.completeAt hG hmem
  exact ⟨pf, fun R => h _ _ _ _ _ R⟩

end SubVerifiers

/-! ## Base soundness: the four cases (proof of `thm:short-pcp-ours`) -/

namespace SubVerifiers

variable {D : ACSPInstance F} {sR sH sI : ℝ} (W : SubVerifiers D sR sH sI)

variable (r : ℕ) (hR : W.VR.rand ≤ r) (hH : W.VH.rand ≤ r) (hf : W.f ≤ r) (hI : W.VI.rand ≤ r)

/-- Step 2 alone bounds `V0`'s acceptance. -/
theorem acceptFrac_le_R (pf : ProofTable W) :
    acceptFrac (W.acceptsAt r hR hH hf hI pf) ≤ acceptFrac (W.VR.accepts pf.p0 pf.π0) := by
  rw [← acceptFrac_pre hR]
  apply acceptFrac_mono
  intro R hR'
  simp only [acceptsAt, Bool.and_eq_true] at hR'
  exact hR'.1.1.1

theorem acceptFrac_le_H (pf : ProofTable W) :
    acceptFrac (W.acceptsAt r hR hH hf hI pf) ≤ acceptFrac (W.VH.accepts pf.p1 pf.π1) := by
  rw [← acceptFrac_pre hH]
  apply acceptFrac_mono
  intro R hR'
  simp only [acceptsAt, Bool.and_eq_true] at hR'
  exact hR'.1.1.2

theorem acceptFrac_le_I (pf : ProofTable W) :
    acceptFrac (W.acceptsAt r hR hH hf hI pf) ≤
      acceptFrac (W.VI.accepts (fun a => pf.p0 a - D.px a) pf.πc) := by
  rw [← acceptFrac_pre hI]
  apply acceptFrac_mono
  intro R hR'
  simp only [acceptsAt, Bool.and_eq_true] at hR'
  exact hR'.2

theorem acceptFrac_le_consist (pf : ProofTable W) :
    acceptFrac (W.acceptsAt r hR hH hf hI pf) ≤
      ((univ.filter fun a => consist D pf.p0 pf.p1 a = true).card : ℝ) / (Fintype.card F : ℝ) := by
  rw [← acceptFrac_elem W.elem, ← acceptFrac_pre hf]
  apply acceptFrac_mono
  intro R hR'
  simp only [acceptsAt, Bool.and_eq_true] at hR'
  exact hR'.1.2

omit r hR hH hf hI

/-- **Case 4.** The consistency-test argument of BCGT13, proof of Theorem 8.1, is used here
under the generic instance hypotheses. The proof of `thm:short-pcp-ours`, Step 2, “Base soundness”,
gives the affine instance explicitly: after Cases 1–3 fail, the test rejects with probability at least
`3/4 - 1/4 = 1/2`. -/
theorem case4 (hG : D.Good) (hnot : ¬ D.Mem) (pf : ProofTable W)
    (h1 : ∃ q ∈ RS univ D.dA, fracDist univ pf.p0 q ≤ 1 / (8 * D.cN))
    (h2 : ∃ q ∈ VRS univ D.H D.dB, fracDist univ pf.p1 q ≤ 1 / 8)
    (h3 : ∃ q ∈ VRS univ D.I D.dA, fracDist univ (fun a => pf.p0 a - D.px a) q ≤ 1 / (8 * D.cN)) :
    ((univ.filter fun a => consist D pf.p0 pf.p1 a = true).card : ℝ) / (Fintype.card F : ℝ) ≤ 3 / 4 := by
  classical
  obtain ⟨w0, ⟨A, hAdeg, hA⟩, hdA⟩ := h1
  obtain ⟨w1, ⟨B', hB'deg, hB', hB'H⟩, hdB⟩ := h2
  obtain ⟨wc, ⟨A', hA'deg, hA', hA'I⟩, hdc⟩ := h3
  obtain rfl : w0 = fun a => A.eval a := funext fun s => hA s (Finset.mem_univ s)
  obtain rfl : w1 = fun a => B'.eval a := funext fun s => hB' s (Finset.mem_univ s)
  obtain rfl : wc = fun a => A'.eval a := funext fun s => hA' s (Finset.mem_univ s)
  obtain ⟨Px, hPxdeg, hPx⟩ := hG.px_low
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hqpos : (0 : ℝ) < q := by
    rw [hq]; exact_mod_cast Fintype.card_pos
  have hcN : (1 : ℝ) ≤ D.cN := by exact_mod_cast hG.cN_pos
  -- disagreement counts
  have eA := card_ne_le_of_fracDist hdA
  have eB := card_ne_le_of_fracDist hdB
  have eC := card_ne_le_of_fracDist hdc
  rw [← hq] at eA eB eC
  -- Step 1: A − Px = A′, so A is consistent with the instance
  have hAA' : A - Px = A' := by
    by_contra hne
    have hle := card_agree_le hne ((natDegree_sub_le A Px).trans (max_le hAdeg hPxdeg)) hA'deg
    -- the agreement set contains every point where both closeness relations hold
    have hsub : (univ.filter fun a => ¬ ((A - Px).eval a = A'.eval a)) ⊆
        (univ.filter fun a => pf.p0 a ≠ A.eval a) ∪
          (univ.filter fun a => pf.p0 a - D.px a ≠ A'.eval a) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
      by_contra hc
      push Not at hc
      apply ha
      rw [eval_sub, ← hc.1, ← hc.2, hPx]
    have hcard := Finset.card_le_card hsub
    have hunion := Finset.card_union_le (univ.filter fun a => pf.p0 a ≠ A.eval a)
      (univ.filter fun a => pf.p0 a - D.px a ≠ A'.eval a)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset F)) (fun a => (A - Px).eval a = A'.eval a)
    have hdAs : (4 * D.dA : ℝ) < 3 * q := by rw [hq]; exact_mod_cast hG.dA_small
    have hδ : (1 : ℝ) / (8 * D.cN) ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    have : (Fintype.card F : ℝ) ≤ D.dA + (1 / 8 * q + 1 / 8 * q) := by
      have h' : ((univ : Finset F).card : ℝ) ≤ D.dA +
          (((univ.filter fun a => pf.p0 a ≠ A.eval a).card : ℝ) +
            ((univ.filter fun a => pf.p0 a - D.px a ≠ A'.eval a).card : ℝ)) := by
        have := hsplit
        have h1' : ((univ.filter fun a => ¬ ((A - Px).eval a = A'.eval a)).card : ℝ) ≤
            (((univ.filter fun a => pf.p0 a ≠ A.eval a).card : ℝ) +
              ((univ.filter fun a => pf.p0 a - D.px a ≠ A'.eval a).card : ℝ)) := by
          exact_mod_cast hcard.trans hunion
        have h2' : ((univ : Finset F).card : ℝ) =
            ((univ.filter fun a => (A - Px).eval a = A'.eval a).card : ℝ) +
              ((univ.filter fun a => ¬ ((A - Px).eval a = A'.eval a)).card : ℝ) := by
          exact_mod_cast this.symm
        have h3' : ((univ.filter fun a => (A - Px).eval a = A'.eval a).card : ℝ) ≤ D.dA := by
          exact_mod_cast hle
        linarith
      simp only [Finset.card_univ] at h'
      rw [← hq] at h'
      have := mul_le_mul_of_nonneg_right hδ hqpos.le
      linarith
    linarith
  have hAx : ∀ α ∈ D.I, A.eval α = D.px α := by
    intro α hα
    have := congrArg (fun P => P.eval α) hAA'
    simp only [eval_sub] at this
    rw [hPx, ← sub_eq_zero, this, hA'I α hα]
  -- Step 2: B and B′ are distinct
  obtain ⟨Bp, hBdeg, hBp⟩ := hG.B_low A hAdeg
  have hBB' : Bp ≠ B' := by
    intro hEq
    apply hnot
    refine ⟨A, hAdeg, fun α hα => ?_, hAx⟩
    rw [← hBp, hEq, hB'H α hα]
  -- Step 3: the union bound
  have hsub : (univ.filter fun a => consist D pf.p0 pf.p1 a = true) ⊆
      (univ.filter fun a => pf.p1 a ≠ B'.eval a) ∪
        ((Finset.univ : Finset (Fin D.cN)).biUnion fun i =>
          univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)) ∪
        (univ.filter fun a => Bp.eval a = B'.eval a) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, consist, decide_eq_true_eq] at ha
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    by_contra hc
    push Not at hc
    obtain ⟨⟨h1c, h2c⟩, h3c⟩ := hc
    apply h3c
    rw [hBp, ← h1c, ha]
    congr 1
    funext i
    exact (h2c i).symm
  have hN : ∀ i : Fin D.cN, ((univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card : ℝ) ≤
      1 / (8 * D.cN) * q := by
    intro i
    have hbij : Function.Bijective (D.nbr i) := (hG.nbr_inj i).bijective_of_finite
    have : (univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card =
        (univ.filter fun a => pf.p0 a ≠ A.eval a).card := by
      rw [← Finset.card_map ⟨D.nbr i, hG.nbr_inj i⟩]
      congr 1
      ext b
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hb
        obtain ⟨a, rfl⟩ := hbij.2 b
        exact ⟨a, hb, rfl⟩
    rw [this]
    exact eA
  have hbi : (((Finset.univ : Finset (Fin D.cN)).biUnion fun i =>
      univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card : ℝ) ≤ 1 / 8 * q := by
    have := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin D.cN)))
      (t := fun i => univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a))
    have hsum : (∑ i : Fin D.cN, ((univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card : ℝ)) ≤
        ∑ _i : Fin D.cN, 1 / (8 * D.cN) * q := Finset.sum_le_sum fun i _ => hN i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hcN0 : (D.cN : ℝ) ≠ 0 := by linarith
    have heq : (D.cN : ℝ) * (1 / (8 * D.cN) * q) = 1 / 8 * q := by field_simp
    calc _ ≤ (∑ i : Fin D.cN, ((univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card : ℝ)) := by
          exact_mod_cast this
      _ ≤ _ := hsum
      _ = _ := heq
  have hagree : ((univ.filter fun a => Bp.eval a = B'.eval a).card : ℝ) ≤ 1 / 2 * q := by
    have := card_agree_le hBB' hBdeg hB'deg
    have hdB : (2 * D.dB : ℝ) ≤ q := by rw [hq]; exact_mod_cast hG.dB_small
    have : ((univ.filter fun a => Bp.eval a = B'.eval a).card : ℝ) ≤ D.dB := by exact_mod_cast this
    linarith
  have hB1 : ((univ.filter fun a => pf.p1 a ≠ B'.eval a).card : ℝ) ≤ 1 / 8 * q := by
    exact eB
  have htot := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le
    ((univ.filter fun a => pf.p1 a ≠ B'.eval a) ∪
      ((Finset.univ : Finset (Fin D.cN)).biUnion fun i =>
        univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)))
    (univ.filter fun a => Bp.eval a = B'.eval a)
  have hu2 := Finset.card_union_le (univ.filter fun a => pf.p1 a ≠ B'.eval a)
    ((Finset.univ : Finset (Fin D.cN)).biUnion fun i =>
      univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a))
  have hc : ((univ.filter fun a => consist D pf.p0 pf.p1 a = true).card : ℝ) ≤ 3 / 4 * q := by
    have : ((univ.filter fun a => consist D pf.p0 pf.p1 a = true).card : ℝ) ≤
        ((univ.filter fun a => pf.p1 a ≠ B'.eval a).card : ℝ) +
        (((Finset.univ : Finset (Fin D.cN)).biUnion fun i =>
          univ.filter fun a => pf.p0 (D.nbr i a) ≠ A.eval (D.nbr i a)).card : ℝ) +
        ((univ.filter fun a => Bp.eval a = B'.eval a).card : ℝ) := by
      exact_mod_cast htot.trans (hu1.trans (Nat.add_le_add_right hu2 _))
    linarith
  rw [div_le_iff₀ hqpos]
  linarith

/-- **Base soundness** (proof of `thm:short-pcp-ours`). If the instance is not in sACSP, `V0` accepts **every** proof table with
probability at most `1 − σ`, where `σ = min{s_R·δ, s_H/8, s_I·δ, 1/4}`, `δ = 1/(8c_N)` (Cases 1–3: strong soundness
of the single run on the far table; Case 4: the consistency test, `1/4` in place of BCGT13's `1/2` because only
`dB ≤ |F|/2` is assumed). -/
theorem soundAt (r : ℕ) (hR : W.VR.rand ≤ r) (hH : W.VH.rand ≤ r) (hf : W.f ≤ r) (hI : W.VI.rand ≤ r)
    (hG : D.Good) (hnot : ¬ D.Mem) (pf : ProofTable W) :
    acceptFrac (W.acceptsAt r hR hH hf hI pf) ≤
      1 - min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) := by
  by_cases h1 : ∃ q ∈ RS univ D.dA, fracDist univ pf.p0 q ≤ 1 / (8 * D.cN)
  · by_cases h2 : ∃ q ∈ VRS univ D.H D.dB, fracDist univ pf.p1 q ≤ 1 / 8
    · by_cases h3 : ∃ q ∈ VRS univ D.I D.dA, fracDist univ (fun a => pf.p0 a - D.px a) q ≤ 1 / (8 * D.cN)
      · -- Case 4
        have := (W.acceptFrac_le_consist r hR hH hf hI pf).trans (W.case4 hG hnot pf h1 h2 h3)
        have hm : min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) ≤
            1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
        linarith
      · -- Case 3
        push Not at h3
        have := (W.acceptFrac_le_I r hR hH hf hI pf).trans (W.VI.sound _ pf.πc _ fun q hq => (h3 q hq).le)
        have hm : min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) ≤
            sI * (1 / (8 * D.cN)) := (min_le_right _ _).trans (min_le_left _ _)
        linarith
    · -- Case 2
      push Not at h2
      have := (W.acceptFrac_le_H r hR hH hf hI pf).trans (W.VH.sound _ pf.π1 _ fun q hq => (h2 q hq).le)
      have hm : min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) ≤
          sH * (1 / 8) := (min_le_left _ _).trans (min_le_right _ _)
      linarith
  · -- Case 1
    push Not at h1
    have := (W.acceptFrac_le_R r hR hH hf hI pf).trans (W.VR.sound _ pf.π0 _ fun q hq => (h1 q hq).le)
    have hm : min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) ≤
        sR * (1 / (8 * D.cN)) := (min_le_left _ _).trans (min_le_left _ _)
    linarith

/-- **Base soundness** at `r0`. -/
theorem sound (hG : D.Good) (hnot : ¬ D.Mem) (pf : ProofTable W) :
    acceptFrac (W.accepts pf) ≤
      1 - min (min (sR * (1 / (8 * D.cN))) (sH * (1 / 8))) (min (sI * (1 / (8 * D.cN))) (1 / 4)) :=
  W.soundAt _ _ _ _ _ hG hnot pf

end SubVerifiers

end NearCubicGates.Adapters.ShortPCP
