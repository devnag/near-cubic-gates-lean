import Proof.Wire_3_5.TransferCompleteness

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared (uMean bitR uMean_mono uMean_add bitR_nonneg bitR_le_one
  bitR_eq_bitAsReal)
open NearCubicWires.ComponentwiseValidity (validityPenalty clauseValue literalValue booleanityPenalty
  systematicPenalty)
open NearCubicWires.ComponentwiseBranchExtraction (literalIndex literalNegated systematicConstraint clauseRealValue)

/-! ## Linear forms in the atoms and four-factor masked polynomials -/

section Forms
variable {α Ω : Type} [Fintype α] (A : α → Ω → Bool)

/-- A linear form in the atoms: `Σ_a w_a A_a(x)`. -/
noncomputable def linForm (w : α → ℝ) (x : Ω) : ℝ := ∑ a, w a * bitR (A a x)

/-- The ℓ¹ coefficient mass of a linear form. -/
noncomputable def linMass (w : α → ℝ) : ℝ := ∑ a, |w a|

theorem linMass_nonneg (w : α → ℝ) : 0 ≤ linMass w := Finset.sum_nonneg fun a _ => abs_nonneg (w a)

/-- A product of four linear forms expands over the tuples of atoms. -/
theorem prod_linForm (F : Fin 4 → α → ℝ) (x : Ω) :
    ∏ k, linForm A (F k) x = ∑ t : Fin 4 → α, (∏ k, F k (t k)) * ∏ k, bitR (A (t k) x) := by
  classical
  unfold linForm
  rw [Fintype.prod_sum (fun k a => F k a * bitR (A a x))]
  exact Finset.sum_congr rfl fun t _ => Finset.prod_mul_distrib

/-- The ℓ¹ mass of the expanded coefficients is the product of the factors' masses. -/
theorem sum_abs_prod (F : Fin 4 → α → ℝ) :
    ∑ t : Fin 4 → α, |∏ k, F k (t k)| = ∏ k, linMass (F k) := by
  classical
  unfold linMass
  rw [Fintype.prod_sum (fun k a => |F k a|)]
  exact Finset.sum_congr rfl fun t _ => Finset.abs_prod _ _

theorem uMean_finsum {ι Ω' : Type} [Fintype ι] [Fintype Ω'] (g : ι → Ω' → ℝ) :
    uMean (fun ω => ∑ t, g t ω) = ∑ t, uMean (g t) := by
  unfold uMean; rw [Finset.sum_comm, Finset.sum_div]

theorem abs_uMean_sub_le {Ω' : Type} [Fintype Ω'] (f g : Ω' → ℝ) :
    |uMean f - uMean g| ≤ uMean (fun ω => |f ω - g ω|) := by
  rw [← uMean_sub]
  unfold uMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card Ω' : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

noncomputable def tupleTruth {Seed : Type} [Fintype Seed] [Fintype Ω] (M : Seed → Ω → Bool) (t : Fin 4 → α) : ℝ :=
  uMean fun p : Seed × Ω => bitR (M p.1 p.2) * ∏ k, bitR (A (t k) p.2)

/-- A masked polynomial of degree at most four: four monomials `κ_j ∏_{k<4} L_{F j k}`. -/
structure Poly4 (α : Type) where
  κ : Fin 4 → ℝ
  F : Fin 4 → Fin 4 → α → ℝ

/-- Its value at `x`. -/
noncomputable def Poly4.eval (P : Poly4 α) (x : Ω) : ℝ := ∑ j, P.κ j * ∏ k, linForm A (P.F j k) x

/-- Its coefficient mass `Σ_j |κ_j| ∏_k ‖F_{jk}‖₁`. -/
noncomputable def Poly4.mass (P : Poly4 α) : ℝ := ∑ j, |P.κ j| * ∏ k, linMass (P.F j k)

/-- The coefficient of the call on tuple `t` from monomial `j`. -/
noncomputable def Poly4.coeff (P : Poly4 α) (j : Fin 4) (t : Fin 4 → α) : ℝ := P.κ j * ∏ k, P.F j k (t k)

/-- The machine's combination of per-call estimates. -/
noncomputable def Poly4.estimate (P : Poly4 α) (est : Fin 4 → (Fin 4 → α) → ℝ) : ℝ :=
  ∑ j, ∑ t, P.coeff j t * est j t

/-- The masked mean of a polynomial is the same combination of tuple truths (exact). -/
theorem Poly4.masked_expand {Seed : Type} [Fintype Seed] [Fintype Ω] (P : Poly4 α) (M : Seed → Ω → Bool) :
    uMean (fun p : Seed × Ω => bitR (M p.1 p.2) * P.eval A p.2) =
      ∑ j, ∑ t, P.coeff j t * tupleTruth A M t := by
  have hpt : ∀ p : Seed × Ω, bitR (M p.1 p.2) * P.eval A p.2 =
      ∑ j, ∑ t, P.coeff j t * (bitR (M p.1 p.2) * ∏ k, bitR (A (t k) p.2)) := by
    intro p
    unfold Poly4.eval Poly4.coeff
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [prod_linForm, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [show (fun p : Seed × Ω => bitR (M p.1 p.2) * P.eval A p.2) = fun p =>
    ∑ j, ∑ t, P.coeff j t * (bitR (M p.1 p.2) * ∏ k, bitR (A (t k) p.2)) from funext hpt]
  rw [uMean_finsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [uMean_finsum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tupleTruth
  exact uMean_mul_left _ _

/-- **The propagated error**: per-call errors `≤ err` on every call with a nonzero coefficient give a total error
at most the coefficient mass times `err`. -/
theorem Poly4.estimate_error (P : Poly4 α) (tr est : Fin 4 → (Fin 4 → α) → ℝ) (err : ℝ)
    (h : ∀ j t, P.coeff j t ≠ 0 → |est j t - tr j t| ≤ err) :
    |P.estimate est - ∑ j, ∑ t, P.coeff j t * tr j t| ≤ P.mass * err := by
  unfold Poly4.estimate
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j t, |P.coeff j t * est j t - P.coeff j t * tr j t| ≤ |P.coeff j t| * err := by
    intro j t
    rw [← mul_sub, abs_mul]
    by_cases hc : P.coeff j t = 0
    · simp [hc]
    · exact mul_le_mul_of_nonneg_left (h j t hc) (abs_nonneg _)
  calc |∑ j, (∑ t, P.coeff j t * est j t - ∑ t, P.coeff j t * tr j t)|
      ≤ ∑ j, |∑ t, P.coeff j t * est j t - ∑ t, P.coeff j t * tr j t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ t, |P.coeff j t| * err := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm j t)
    _ = P.mass * err := by
        unfold Poly4.mass Poly4.coeff
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, ← sum_abs_prod (P.F j)]
        simp only [abs_mul, ← Finset.mul_sum]

/-- The mass under factor bounds. -/
theorem Poly4.mass_le (P : Poly4 α) (m : Fin 4 → Fin 4 → ℝ) (hm : ∀ j k, linMass (P.F j k) ≤ m j k) :
    P.mass ≤ ∑ j, |P.κ j| * ∏ k, m j k := by
  unfold Poly4.mass
  refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact Finset.prod_le_prod (fun k _ => linMass_nonneg _) fun k _ => hm j k

/-- Four linear factors. -/
def fac4 (a b c d : α → ℝ) : Fin 4 → α → ℝ := ![a, b, c, d]

/-- A polynomial from four monomials. -/
def Poly4.mk4 (k0 k1 k2 k3 : ℝ) (F0 F1 F2 F3 : Fin 4 → α → ℝ) : Poly4 α := ⟨![k0, k1, k2, k3], ![F0, F1, F2, F3]⟩

theorem prod_fac4 (a b c d : α → ℝ) (x : Ω) :
    ∏ k, linForm A (fac4 a b c d k) x = linForm A a x * linForm A b x * linForm A c x * linForm A d x := by
  rw [Fin.prod_univ_four]; rfl

theorem mass_fac4 (a b c d : α → ℝ) :
    ∏ k, linMass (fac4 a b c d k) = linMass a * linMass b * linMass c * linMass d := by
  rw [Fin.prod_univ_four]; rfl

theorem eval_mk4 (k0 k1 k2 k3 : ℝ) (F0 F1 F2 F3 : Fin 4 → α → ℝ) (x : Ω) :
    (Poly4.mk4 k0 k1 k2 k3 F0 F1 F2 F3).eval A x =
      k0 * ∏ k, linForm A (F0 k) x + k1 * ∏ k, linForm A (F1 k) x + k2 * ∏ k, linForm A (F2 k) x +
        k3 * ∏ k, linForm A (F3 k) x := by
  unfold Poly4.eval Poly4.mk4; rw [Fin.sum_univ_four]; rfl

theorem mass_mk4 (k0 k1 k2 k3 : ℝ) (F0 F1 F2 F3 : Fin 4 → α → ℝ) :
    (Poly4.mk4 k0 k1 k2 k3 F0 F1 F2 F3).mass =
      |k0| * ∏ k, linMass (F0 k) + |k1| * ∏ k, linMass (F1 k) + |k2| * ∏ k, linMass (F2 k) +
        |k3| * ∏ k, linMass (F3 k) := by
  unfold Poly4.mass Poly4.mk4; rw [Fin.sum_univ_four]; rfl

end Forms

/-- Products of four bounded nonnegative factors. -/
theorem prod4_le {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : a ≤ a')
    (h2 : b ≤ b') (h3 : c ≤ c') (h4 : d ≤ d') : a * b * c * d ≤ a' * b' * c' * d' := by
  have hab := mul_le_mul h1 h2 hb (ha.trans h1)
  have habc := mul_le_mul hab h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))
  exact mul_le_mul habc h4 hd (mul_nonneg (mul_nonneg (ha.trans h1) (hb.trans h2)) (hc.trans h3))

/-! ## The three test polynomials -/

section TestPolys
variable {α : Type} [Fintype α]

def polyV (sys : Bool) (wS wOne wE : α → ℝ) : Poly4 α :=
  if sys then Poly4.mk4 1 (-2) 1 0 (fac4 wS wS wOne wOne) (fac4 wE wS wOne wOne) (fac4 wE wOne wOne wOne)
    (fac4 wOne wOne wOne wOne)
  else Poly4.mk4 1 (-2) 1 0 (fac4 wS wS wOne wOne) (fac4 wS wS wS wOne) (fac4 wS wS wS wS)
    (fac4 wOne wOne wOne wOne)

/-- The second-moment polynomial `S²`. -/
def polyQ (wS wOne : α → ℝ) : Poly4 α :=
  Poly4.mk4 1 0 0 0 (fac4 wS wS wOne wOne) (fac4 wOne wOne wOne wOne) (fac4 wOne wOne wOne wOne)
    (fac4 wOne wOne wOne wOne)

/-- The literal `ℓ = a + b·s` of a sign: `a = [negated]`, `b = ±1`. -/
def litA (n : Bool) : ℝ := if n then 1 else 0
/-- The slope of the literal. -/
def litB (n : Bool) : ℝ := if n then -1 else 1

def polyMu (n₀ n₁ : Bool) (wX wY wOne : α → ℝ) : Poly4 α :=
  Poly4.mk4 (litA n₀ + litA n₁ - litA n₀ * litA n₁) (litB n₀ * (1 - litA n₁)) (litB n₁ * (1 - litA n₀))
    (-(litB n₀ * litB n₁)) (fac4 wOne wOne wOne wOne) (fac4 wX wOne wOne wOne) (fac4 wY wOne wOne wOne)
    (fac4 wX wY wOne wOne)

variable {Ω : Type} (A : α → Ω → Bool)

theorem polyV_eval (sys : Bool) (wS wOne wE : α → ℝ) (x : Ω) (b : Bool) (hOne : linForm A wOne x = 1)
    (hE : linForm A wE x = bitR b) :
    (polyV sys wS wOne wE).eval A x = validityPenalty (if sys then some b else none) (linForm A wS x) := by
  cases sys
  · simp only [polyV, Bool.false_eq_true, if_false]
    rw [eval_mk4]
    simp only [prod_fac4]
    rw [hOne]
    simp only [validityPenalty, booleanityPenalty]
    ring
  · simp only [polyV, if_true]
    rw [eval_mk4]
    simp only [prod_fac4]
    rw [hOne, hE]
    simp only [validityPenalty, systematicPenalty]
    cases b <;> simp [bitR, bitAsReal] <;> ring

theorem polyQ_eval (wS wOne : α → ℝ) (x : Ω) (hOne : linForm A wOne x = 1) :
    (polyQ wS wOne).eval A x = linForm A wS x ^ 2 := by
  unfold polyQ
  rw [eval_mk4]
  simp only [prod_fac4]
  rw [hOne]
  ring

theorem polyMu_eval (n₀ n₁ : Bool) (wX wY wOne : α → ℝ) (x : Ω) (hOne : linForm A wOne x = 1) :
    (polyMu n₀ n₁ wX wY wOne).eval A x = clauseValue n₀ n₁ (linForm A wX x) (linForm A wY x) := by
  unfold polyMu
  rw [eval_mk4]
  simp only [prod_fac4]
  rw [hOne]
  simp only [clauseValue, literalValue]
  cases n₀ <;> cases n₁ <;> simp [litA, litB] <;> ring

/-- The validity polynomial's mass is at most `(1+Λ̄)⁴`, systematic parities included. -/
theorem polyV_mass_le (sys : Bool) (wS wOne wE : α → ℝ) (Λbar : ℝ) (hL : 0 ≤ Λbar) (hS : linMass wS ≤ Λbar)
    (hOne : linMass wOne ≤ 1) (hE : linMass wE ≤ 1) : (polyV sys wS wOne wE).mass ≤ (1 + Λbar) ^ 4 := by
  have s0 := linMass_nonneg wS
  have o0 := linMass_nonneg wOne
  have e0 := linMass_nonneg wE
  cases sys
  · simp only [polyV, Bool.false_eq_true, if_false]
    rw [mass_mk4]; simp only [mass_fac4]
    have t1 := prod4_le s0 s0 o0 o0 hS hS hOne hOne
    have t2 := prod4_le s0 s0 s0 o0 hS hS hS hOne
    have t3 := prod4_le s0 s0 s0 s0 hS hS hS hS
    norm_num
    nlinarith [pow_nonneg hL 2, pow_nonneg hL 3, mul_nonneg (mul_nonneg (mul_nonneg o0 o0) o0) o0]
  · simp only [polyV, if_true]
    rw [mass_mk4]; simp only [mass_fac4]
    have t1 := prod4_le s0 s0 o0 o0 hS hS hOne hOne
    have t2 := prod4_le e0 s0 o0 o0 hE hS hOne hOne
    have t3 := prod4_le e0 o0 o0 o0 hE hOne hOne hOne
    norm_num
    nlinarith [pow_nonneg hL 2, pow_nonneg hL 3, mul_nonneg (mul_nonneg (mul_nonneg o0 o0) o0) o0]

theorem polyQ_mass_le (wS wOne : α → ℝ) (Λbar : ℝ) (hL : 0 ≤ Λbar) (hS : linMass wS ≤ Λbar)
    (hOne : linMass wOne ≤ 1) : (polyQ wS wOne).mass ≤ (1 + Λbar) ^ 4 := by
  have s0 := linMass_nonneg wS
  have o0 := linMass_nonneg wOne
  unfold polyQ
  rw [mass_mk4]; simp only [mass_fac4]
  have t1 := prod4_le s0 s0 o0 o0 hS hS hOne hOne
  norm_num
  nlinarith [pow_nonneg hL 2, pow_nonneg hL 3, pow_nonneg hL 4]

theorem polyMu_mass_le (n₀ n₁ : Bool) (wX wY wOne : α → ℝ) (Λbar : ℝ) (hL : 0 ≤ Λbar) (hX : linMass wX ≤ Λbar)
    (hY : linMass wY ≤ Λbar) (hOne : linMass wOne ≤ 1) : (polyMu n₀ n₁ wX wY wOne).mass ≤ (1 + Λbar) ^ 4 := by
  have x0 := linMass_nonneg wX
  have y0 := linMass_nonneg wY
  have o0 := linMass_nonneg wOne
  unfold polyMu
  rw [mass_mk4]; simp only [mass_fac4]
  have t0 := prod4_le o0 o0 o0 o0 hOne hOne hOne hOne
  have t1 := prod4_le x0 o0 o0 o0 hX hOne hOne hOne
  have t2 := prod4_le y0 o0 o0 o0 hY hOne hOne hOne
  have t3 := prod4_le x0 y0 o0 o0 hX hY hOne hOne
  cases n₀ <;> cases n₁ <;> simp [litA, litB] <;>
    nlinarith [pow_nonneg hL 2, pow_nonneg hL 3, pow_nonneg hL 4]

end TestPolys

/-! ## The three estimates' accuracy -/

section Accuracy
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {Seed : Type} [Fintype Seed]
variable {α : Type} [Fintype α] (A : α → BitInput q → Bool)

structure AtomForms (Λbar : ℝ) where
  wS : PcppVar pcpp → α → ℝ
  wOne : α → ℝ
  wE : PcppVar pcpp → α → ℝ
  sys : PcppVar pcpp → Bool
  parity : PcppVar pcpp → BitInput q → Bool
  one_eq : ∀ x, linForm A wOne x = 1
  E_eq : ∀ X x, linForm A (wE X) x = bitR (parity X x)
  constraint_eq : ∀ X x, systematicConstraint pcpp x X = if sys X then some (parity X x) else none
  S_mass : ∀ X, linMass (wS X) ≤ Λbar
  one_mass : linMass wOne ≤ 1
  E_mass : ∀ X, linMass (wE X) ≤ 1

variable {pcpp A}

/-- The guess the forms define: `S_X(x) = Σ_a (wS X)_a A_a(x)`. -/
noncomputable def AtomForms.guess {Λbar : ℝ} (f : AtomForms pcpp A Λbar) : PcppVar pcpp → BitInput q → ℝ :=
  fun X x => linForm A (f.wS X) x

/-- The machine's `V̂`: the position average of each position's validity polynomial, estimated call by call. -/
noncomputable def AtomForms.Vhat {Λbar : ℝ} (f : AtomForms pcpp A Λbar)
    (est : Fin (2 ^ pcpp.clauseBits) × Fin 2 → Fin 4 → (Fin 4 → α) → ℝ) : ℝ :=
  uMean fun pos : Fin (2 ^ pcpp.clauseBits) × Fin 2 =>
    (polyV (f.sys (posVar pcpp pos.1 pos.2)) (f.wS (posVar pcpp pos.1 pos.2)) f.wOne
      (f.wE (posVar pcpp pos.1 pos.2))).estimate (est pos)

/-- The machine's `Q̂`. -/
noncomputable def AtomForms.Qhat {Λbar : ℝ} (f : AtomForms pcpp A Λbar)
    (est : Fin (2 ^ pcpp.clauseBits) × Fin 2 → Fin 4 → (Fin 4 → α) → ℝ) : ℝ :=
  uMean fun pos : Fin (2 ^ pcpp.clauseBits) × Fin 2 =>
    (polyQ (f.wS (posVar pcpp pos.1 pos.2)) f.wOne).estimate (est pos)

/-- The machine's `μ̂`: the clause average of each clause's polynomial. -/
noncomputable def AtomForms.μhat {Λbar : ℝ} (f : AtomForms pcpp A Λbar)
    (est : Fin (2 ^ pcpp.clauseBits) → Fin 4 → (Fin 4 → α) → ℝ) : ℝ :=
  uMean fun i : Fin (2 ^ pcpp.clauseBits) =>
    (polyMu (posNeg pcpp i 0) (posNeg pcpp i 1) (f.wS (posVar pcpp i 0)) (f.wS (posVar pcpp i 1)) f.wOne).estimate
      (est i)

theorem uMean_pos_split3 {C J Ω' : Type} [Fintype C] [Fintype J] [Fintype Ω'] (g : C → J → Ω' → ℝ) :
    uMean (fun p : C × J × Ω' => g p.1 p.2.1 p.2.2) =
      uMean (fun pos : C × J => uMean (fun ω => g pos.1 pos.2 ω)) := by
  rw [uMean_prod, uMean_prod (fun pos : C × J => uMean (fun ω => g pos.1 pos.2 ω))]
  congr 1; funext i
  exact uMean_prod (fun c : J × Ω' => g i c.1 c.2)

theorem propagated_V {Λbar : ℝ} (hL : 0 ≤ Λbar) (f : AtomForms pcpp A Λbar)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (est : Fin (2 ^ pcpp.clauseBits) × Fin 2 → Fin 4 → (Fin 4 → α) → ℝ) (err : ℝ) (herr : 0 ≤ err)
    (hest : ∀ pos j t, (polyV (f.sys (posVar pcpp pos.1 pos.2)) (f.wS (posVar pcpp pos.1 pos.2)) f.wOne
        (f.wE (posVar pcpp pos.1 pos.2))).coeff j t ≠ 0 →
      |est pos j t - tupleTruth A (G (posVar pcpp pos.1 pos.2)) t| ≤ err) :
    |f.Vhat est - testV pcpp f.guess G| ≤ (1 + Λbar) ^ 4 * err := by
  have hV : testV pcpp f.guess G = uMean (fun pos : Fin (2 ^ pcpp.clauseBits) × Fin 2 =>
      ∑ j, ∑ t, (polyV (f.sys (posVar pcpp pos.1 pos.2)) (f.wS (posVar pcpp pos.1 pos.2)) f.wOne
        (f.wE (posVar pcpp pos.1 pos.2))).coeff j t * tupleTruth A (G (posVar pcpp pos.1 pos.2)) t) := by
    unfold testV
    rw [uMean_pos_split3 (fun i j (ω : Seed × BitInput q) => bitR (G (posVar pcpp i j) ω.1 ω.2) *
      validityPenalty (systematicConstraint pcpp ω.2 (posVar pcpp i j)) (f.guess (posVar pcpp i j) ω.2))]
    congr 1; funext pos
    rw [← Poly4.masked_expand]
    congr 1; funext p
    rw [polyV_eval A _ _ _ _ p.2 (f.parity (posVar pcpp pos.1 pos.2) p.2) (f.one_eq p.2)
      (f.E_eq (posVar pcpp pos.1 pos.2) p.2), f.constraint_eq]
    rfl
  rw [hV]
  unfold AtomForms.Vhat
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun pos => ?_)
  exact ((Poly4.estimate_error _ _ _ err (hest pos)).trans
    (mul_le_mul_of_nonneg_right (polyV_mass_le _ _ _ _ Λbar hL (f.S_mass _) f.one_mass (f.E_mass _)) herr))

/-- **`|Q̂ − Q| ≤ (1+Λ̄)⁴·err`**. -/
theorem propagated_Q {Λbar : ℝ} (hL : 0 ≤ Λbar) (f : AtomForms pcpp A Λbar)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (est : Fin (2 ^ pcpp.clauseBits) × Fin 2 → Fin 4 → (Fin 4 → α) → ℝ) (err : ℝ) (herr : 0 ≤ err)
    (hest : ∀ pos j t, (polyQ (f.wS (posVar pcpp pos.1 pos.2)) f.wOne).coeff j t ≠ 0 →
      |est pos j t - tupleTruth A (G (posVar pcpp pos.1 pos.2)) t| ≤ err) :
    |f.Qhat est - testQ pcpp f.guess G| ≤ (1 + Λbar) ^ 4 * err := by
  have hQ : testQ pcpp f.guess G = uMean (fun pos : Fin (2 ^ pcpp.clauseBits) × Fin 2 =>
      ∑ j, ∑ t, (polyQ (f.wS (posVar pcpp pos.1 pos.2)) f.wOne).coeff j t *
        tupleTruth A (G (posVar pcpp pos.1 pos.2)) t) := by
    unfold testQ
    rw [uMean_pos_split3 (fun i j (ω : Seed × BitInput q) => bitR (G (posVar pcpp i j) ω.1 ω.2) *
      f.guess (posVar pcpp i j) ω.2 ^ 2)]
    congr 1; funext pos
    rw [← Poly4.masked_expand]
    congr 1; funext p
    rw [polyQ_eval A _ _ p.2 (f.one_eq p.2)]
    rfl
  rw [hQ]
  unfold AtomForms.Qhat
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun pos => ?_)
  exact ((Poly4.estimate_error _ _ _ err (hest pos)).trans
    (mul_le_mul_of_nonneg_right (polyQ_mass_le _ _ Λbar hL (f.S_mass _) f.one_mass) herr))

/-- **`|μ̂ − μ| ≤ (1+Λ̄)⁴·err`**: the clause calls are masked by `M_i` (the two-carrier calls). -/
theorem propagated_Mu {Λbar : ℝ} (hL : 0 ≤ Λbar) (f : AtomForms pcpp A Λbar)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (est : Fin (2 ^ pcpp.clauseBits) → Fin 4 → (Fin 4 → α) → ℝ) (err : ℝ) (herr : 0 ≤ err)
    (hest : ∀ i j t, (polyMu (posNeg pcpp i 0) (posNeg pcpp i 1) (f.wS (posVar pcpp i 0)) (f.wS (posVar pcpp i 1))
        f.wOne).coeff j t ≠ 0 → |est i j t - tupleTruth A (clauseMask pcpp G i) t| ≤ err) :
    |f.μhat est - testMu pcpp f.guess G| ≤ (1 + Λbar) ^ 4 * err := by
  have hμ : testMu pcpp f.guess G = uMean (fun i : Fin (2 ^ pcpp.clauseBits) =>
      ∑ j, ∑ t, (polyMu (posNeg pcpp i 0) (posNeg pcpp i 1) (f.wS (posVar pcpp i 0)) (f.wS (posVar pcpp i 1))
        f.wOne).coeff j t * tupleTruth A (clauseMask pcpp G i) t) := by
    unfold testMu
    rw [uMean_prod]
    congr 1; funext i
    rw [← Poly4.masked_expand]
    congr 1; funext p
    rw [polyMu_eval A _ _ _ _ _ p.2 (f.one_eq p.2)]
    simp only [clauseRealValue, posNeg_zero, posNeg_one, posVar_zero, posVar_one]
    rfl
  rw [hμ]
  unfold AtomForms.μhat
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun i => ?_)
  exact ((Poly4.estimate_error _ _ _ err (hest i)).trans
    (mul_le_mul_of_nonneg_right (polyMu_mass_le _ _ _ _ _ Λbar hL (f.S_mass _) (f.S_mass _) f.one_mass) herr))

end Accuracy

end NearCubicWires.WireExponent3_5.Transfer
