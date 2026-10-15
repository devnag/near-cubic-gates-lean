import Proof.Wire_3_5.TransferTests
import Proof.Wire_3_5.TransferSparse

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared (uMean bitR maskedMean uMean_mono uMean_add bitR_nonneg bitR_le_one
  maskedMean_true maskedMean_abs_mul_le markov_indicator uMean_marginal_le)
open NearCubicWires.ComponentwiseValidity (validityPenalty validityRound clauseValue booleanityPenalty
  systematicPenalty)
open NearCubicWires.ComponentwiseBranchExtraction (literalIndex literalNegated systematicConstraint clauseRealValue
  clauseRealValue_bitAsReal)

/-! ## Uniform means and `L²` norms on a finite uniform space -/

/-- Iterated means over a product. -/
theorem uMean_prod {A C : Type} [Fintype A] [Fintype C] (f : A × C → ℝ) :
    uMean f = uMean (fun a => uMean (fun c => f (a, c))) := by
  unfold uMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

/-- A statistic that ignores the seed has the seed-free mean. -/
theorem uMean_seed_drop {Seed A : Type} [Fintype Seed] [Fintype A] [Nonempty Seed] (g : A → ℝ) :
    uMean (fun p : Seed × A => g p.2) = uMean g := by
  rw [uMean_prod]
  exact uMean_const (Ω := Seed) (uMean g)

theorem uMean_nonneg {Ω : Type} [Fintype Ω] {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ uMean f := by
  unfold uMean; exact div_nonneg (Finset.sum_nonneg fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uMean_le_const' {Ω : Type} [Fintype Ω] (g : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ x, g x ≤ c) :
    uMean g ≤ c := by
  unfold uMean
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact hc
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    calc ∑ x, g x ≤ ∑ _x : Ω, c := Finset.sum_le_sum fun x _ => hg x
      _ = c * Fintype.card Ω := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- The `L²` norm `‖f‖₂ = √(E f²)`. -/
noncomputable def l2 {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : ℝ := Real.sqrt (uMean fun ω => f ω ^ 2)

theorem l2_nonneg {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : 0 ≤ l2 f := Real.sqrt_nonneg _

theorem l2_sq {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : l2 f ^ 2 = uMean fun ω => f ω ^ 2 :=
  Real.sq_sqrt (uMean_nonneg fun ω => sq_nonneg (f ω))

theorem uMean_mul_left {Ω : Type} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    uMean (fun ω => c * f ω) = c * uMean f := by
  unfold uMean; rw [← Finset.mul_sum, mul_div_assoc]

/-- Cauchy–Schwarz: `E|fg| ≤ ‖f‖₂‖g‖₂`. -/
theorem uMean_abs_mul_le {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    uMean (fun ω => |f ω * g ω|) ≤ l2 f * l2 g := by
  have h := maskedMean_abs_mul_le (fun _ : Ω => true) f g
  simp only [maskedMean_true] at h
  exact h

theorem l2_const_one_le {Ω : Type} [Fintype Ω] : l2 (fun _ : Ω => (1 : ℝ)) ≤ 1 := by
  unfold l2
  rw [Real.sqrt_le_one]
  exact uMean_le_const' _ 1 zero_le_one fun _ => by norm_num

/-- `E|f| ≤ ‖f‖₂`. -/
theorem uMean_abs_le_l2 {Ω : Type} [Fintype Ω] (f : Ω → ℝ) : uMean (fun ω => |f ω|) ≤ l2 f := by
  have h := uMean_abs_mul_le f (fun _ => 1)
  simp only [mul_one] at h
  calc _ ≤ l2 f * l2 (fun _ : Ω => (1 : ℝ)) := h
    _ ≤ l2 f * 1 := mul_le_mul_of_nonneg_left l2_const_one_le (l2_nonneg f)
    _ = l2 f := mul_one _

/-- Minkowski: `‖f+g‖₂ ≤ ‖f‖₂ + ‖g‖₂`. -/
theorem l2_add_le {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) : l2 (fun ω => f ω + g ω) ≤ l2 f + l2 g := by
  have hcs := uMean_abs_mul_le f g
  have hsq : (uMean fun ω => (f ω + g ω) ^ 2) ≤ (l2 f + l2 g) ^ 2 := by
    have e : (uMean fun ω => (f ω + g ω) ^ 2) =
        (uMean fun ω => f ω ^ 2) + 2 * uMean (fun ω => f ω * g ω) + uMean fun ω => g ω ^ 2 := by
      rw [← uMean_mul_left, ← uMean_add, ← uMean_add]
      congr 1; funext ω; ring
    have hfg : uMean (fun ω => f ω * g ω) ≤ uMean (fun ω => |f ω * g ω|) :=
      uMean_mono fun ω => le_abs_self _
    rw [e, add_sq, l2_sq, l2_sq]
    nlinarith [hfg, hcs]
  unfold l2 at hsq ⊢
  calc Real.sqrt (uMean fun ω => (f ω + g ω) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (uMean fun ω => f ω ^ 2) + Real.sqrt (uMean fun ω => g ω ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = _ := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Pointwise domination of absolute values dominates the `L²` norm. -/
theorem l2_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, |f ω| ≤ |g ω|) : l2 f ≤ l2 g := by
  unfold l2
  apply Real.sqrt_le_sqrt
  apply uMean_mono
  intro ω
  have := h ω
  nlinarith [abs_nonneg (f ω), sq_abs (f ω), sq_abs (g ω)]

theorem l2_le_of_sq_le {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : (uMean fun ω => f ω ^ 2) ≤ c ^ 2) : l2 f ≤ c := by
  unfold l2
  calc Real.sqrt (uMean fun ω => f ω ^ 2) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- `L²` from `L⁴`: `E D⁴ ≤ δ⁴` gives `‖D‖₂ ≤ δ` and `‖D²‖₂ ≤ δ²`. -/
theorem l2_of_fourth {Ω : Type} [Fintype Ω] (D : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h4 : (uMean fun ω => D ω ^ 4) ≤ δ ^ 4) : l2 D ≤ δ ∧ l2 (fun ω => D ω ^ 2) ≤ δ ^ 2 := by
  have hsq : l2 (fun ω => D ω ^ 2) ≤ δ ^ 2 := by
    apply l2_le_of_sq_le _ _ (by positivity)
    calc (uMean fun ω => (D ω ^ 2) ^ 2) = uMean fun ω => D ω ^ 4 := by
          congr 1; funext ω; ring
      _ ≤ δ ^ 4 := h4
      _ = (δ ^ 2) ^ 2 := by ring
  refine ⟨?_, hsq⟩
  apply l2_le_of_sq_le _ _ hδ
  have h1 := uMean_abs_le_l2 (fun ω => D ω ^ 2)
  calc (uMean fun ω => D ω ^ 2) = uMean fun ω => |D ω ^ 2| := by
        congr 1; funext ω; rw [abs_of_nonneg (sq_nonneg _)]
    _ ≤ l2 (fun ω => D ω ^ 2) := h1
    _ ≤ δ ^ 2 := hsq

/-- `S(1−S) = T(1−T) + E(1−2T) − E²` with `E = S − T`. -/
theorem sparse_identity (S T : ℝ) : S * (1 - S) = T * (1 - T) + (S - T) * (1 - 2 * T) - (S - T) ^ 2 := by ring

/-- `T(1−T) ≤ √|T−B|` for `T ∈ [0,1]` and Boolean `B` (from `T²(1−T)² ≤ |T−B|`). -/
theorem bool_penalty_le (T : ℝ) (b : Bool) (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    T * (1 - T) ≤ Real.sqrt |T - bitAsReal b| := by
  apply Real.le_sqrt_of_sq_le
  have hp : 0 ≤ T * (1 - T) := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hp1 : T * (1 - T) ≤ 1 := by nlinarith
  have hsq : (T * (1 - T)) ^ 2 ≤ T * (1 - T) := by nlinarith
  cases b
  · simp only [bitAsReal, Bool.false_eq_true, if_false, sub_zero, abs_of_nonneg h0]
    have : T * (1 - T) ≤ T := by nlinarith
    linarith
  · simp only [bitAsReal, if_true]
    rw [abs_of_nonpos (by linarith)]
    have : T * (1 - T) ≤ 1 - T := by nlinarith
    linarith

/-- `|T − B| ≤ √|T−B|` for `T ∈ [0,1]` and Boolean `B`. -/
theorem abs_sub_bool_le_sqrt (T : ℝ) (b : Bool) (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    |T - bitAsReal b| ≤ Real.sqrt |T - bitAsReal b| := by
  have hle : |T - bitAsReal b| ≤ 1 := by
    cases b <;> simp only [bitAsReal, Bool.false_eq_true, if_false, if_true] <;> rw [abs_le] <;>
      constructor <;> linarith
  have hnn := abs_nonneg (T - bitAsReal b)
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem validityPenalty_sparse_le (c : Option Bool) (b : Bool) (hc : ∀ e, c = some e → e = b) (S T : ℝ)
    (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    validityPenalty c S ≤ (Real.sqrt |T - bitAsReal b| + |S - T| + (S - T) ^ 2) ^ 2 := by
  have ha := Real.sqrt_nonneg |T - bitAsReal b|
  cases c with
  | none =>
    simp only [validityPenalty, booleanityPenalty]
    have hid := sparse_identity S T
    have hTT := bool_penalty_le T b h0 h1
    have hT0 : 0 ≤ T * (1 - T) := mul_nonneg h0 (sub_nonneg.mpr h1)
    have h12 : |1 - 2 * T| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hmid : |(S - T) * (1 - 2 * T)| ≤ |S - T| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h12
    have hbound : |S * (1 - S)| ≤ Real.sqrt |T - bitAsReal b| + |S - T| + (S - T) ^ 2 := by
      rw [hid]
      calc |T * (1 - T) + (S - T) * (1 - 2 * T) - (S - T) ^ 2|
          ≤ |T * (1 - T)| + |(S - T) * (1 - 2 * T)| + |(S - T) ^ 2| := by
            calc _ ≤ |T * (1 - T) + (S - T) * (1 - 2 * T)| + |(S - T) ^ 2| := abs_sub _ _
              _ ≤ _ := by gcongr; exact abs_add_le _ _
        _ ≤ _ := by
            rw [abs_of_nonneg hT0, abs_of_nonneg (sq_nonneg (S - T))]
            linarith
    calc S ^ 2 * (1 - S) ^ 2 = |S * (1 - S)| ^ 2 := by rw [sq_abs]; ring
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  | some e =>
    have heb := hc e rfl
    subst heb
    simp only [validityPenalty, systematicPenalty]
    have hTB := abs_sub_bool_le_sqrt T e h0 h1
    have hbound : |bitAsReal e - S| ≤ Real.sqrt |T - bitAsReal e| + |S - T| + (S - T) ^ 2 := by
      calc |bitAsReal e - S| = |(T - bitAsReal e) + (S - T)| := by rw [← abs_neg]; ring_nf
        _ ≤ |T - bitAsReal e| + |S - T| := abs_add_le _ _
        _ ≤ _ := by nlinarith [sq_nonneg (S - T)]
    calc (bitAsReal e - S) ^ 2 = |bitAsReal e - S| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hbound 2

theorem sparseGuess_exists {q : ℕ} {V : Type} {J : V → Type} [∀ X, Fintype (J X)]
    (C : ∀ X, J X → BitInput q → Bool) (α : ∀ X, J X → ℝ) (Λbar : ℝ) (s : ℕ) (hs : 1 ≤ s) (hΛ : 1 ≤ Λbar)
    (hmass : ∀ X, ∑ j, |α X j| ≤ Λbar) (δ : ℝ) (hsδ : 19 * Λbar ^ 4 ≤ (s : ℝ) ^ 2 * δ ^ 4) :
    ∃ (σ : V → Fin s → ℤ) (atom : ∀ X, Fin s → Option (J X)),
      (∀ X a, σ X a ∈ ({-1, 0, 1} : Finset ℤ)) ∧ (∀ X, Λbar / s * ∑ a, |(σ X a : ℝ)| ≤ Λbar) ∧
      ∀ X, uMean (fun x : BitInput q =>
        (Λbar / s * ∑ a, (σ X a : ℝ) * (match atom X a with | some j => bitR (C X j x) | none => 0) -
          ∑ j, α X j * bitR (C X j x)) ^ 4) ≤ δ ^ 4 := by
  have h := fun X => sparseWitness_delta (C X) (α X) Λbar s hs hΛ (hmass X) δ hsδ
  choose σ atom hσ hmassS hbound using h
  refine ⟨σ, atom, hσ, hmassS, fun X => Eq.trans_le ?_ (hbound X)⟩
  congr 1
  funext x
  congr 2
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases atom X a with _ | j <;> rfl

/-! ## Completeness at the tests -/

section Completeness
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)

/-- The honest proof's systematic constraint is the honest bit (the systematic block of `pcpp.assignment` is the
encoding parity). -/
theorem systematicConstraint_honest (x : BitInput q) (aux : BitInput pcpp.auxiliaryBits) (X : PcppVar pcpp) :
    ∀ e, systematicConstraint pcpp x X = some e → e = pcpp.assignment x aux X := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) X
  · intro e he
    simp only [systematicConstraint, Fin.addCases_left, Option.some.injEq] at he
    simp [PointwisePCPP.assignment, he]
  · intro e he
    simp [systematicConstraint] at he

/-- A statistic of the position and the input, averaged over positions, seeds and inputs, is its seed-free
average. -/
theorem uMean_pos_seed_drop {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (g : Fin (2 ^ pcpp.clauseBits) → Fin 2 → BitInput q → ℝ) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) => g p.1 p.2.1 p.2.2.2) =
      uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => g p.1 p.2.1 p.2.2) := by
  rw [uMean_prod, uMean_prod (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => g p.1 p.2.1 p.2.2)]
  congr 1; funext i
  rw [uMean_prod, uMean_prod (fun c : Fin 2 × BitInput q => g i c.1 c.2)]
  congr 1; funext j
  exact uMean_seed_drop (fun x => g i j x)

theorem uMean_clause_seed_drop {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (g : Fin (2 ^ pcpp.clauseBits) → BitInput q → ℝ) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => g p.1 p.2.2) =
      uMean (fun p : Fin (2 ^ pcpp.clauseBits) × BitInput q => g p.1 p.2) := by
  rw [uMean_prod, uMean_prod (fun p : Fin (2 ^ pcpp.clauseBits) × BitInput q => g p.1 p.2)]
  congr 1; funext i
  exact uMean_seed_drop (fun x => g i x)

/-- A per-variable bound averages to a per-position bound. -/
theorem uMean_pos_le {c : ℝ} (hc : 0 ≤ c) (f : PcppVar pcpp → BitInput q → ℝ)
    (hf : ∀ X, (uMean fun x => f X x) ≤ c) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => f (posVar pcpp p.1 p.2.1) p.2.2) ≤ c := by
  rw [uMean_prod]
  apply uMean_le_const' _ _ hc
  intro i
  rw [uMean_prod]
  exact uMean_le_const' _ _ hc fun j => hf (posVar pcpp i j)

variable (aux : BitInput q → BitInput pcpp.auxiliaryBits) (T S : PcppVar pcpp → BitInput q → ℝ) (ζ δ : ℝ)

/-- The honest Boolean proof `B_X(x)`: the PCPP assignment of `x` with its honest auxiliary bits. -/
noncomputable def honestBit (X : PcppVar pcpp) (x : BitInput q) : ℝ := bitAsReal (pcpp.assignment x (aux x) X)

/-- The hypotheses of `tr:completeness` on the witness: `T_X ∈ [0,1]`, `E_pos ‖T_X − B_X‖₁ ≤ ζ`, and the sparse
witness `S_X` at `L⁴` distance `≤ δ` from `T_X` (`tr:sparse`, `sparseWitness_delta`). -/
structure CompletenessWitness : Prop where
  T_mem : ∀ X x, 0 ≤ T X x ∧ T X x ≤ 1
  approx : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
    |T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2|) ≤ ζ
  sparse : ∀ X, (uMean fun x => (S X x - T X x) ^ 4) ≤ δ ^ 4
  ζ_nonneg : 0 ≤ ζ
  δ_nonneg : 0 ≤ δ

variable {pcpp aux T S ζ δ}

/-- Position-level `L²` bounds: `‖√|T−B|‖₂ ≤ √ζ`, `‖S−T‖₂ ≤ δ`, `‖(S−T)²‖₂ ≤ δ²`, `‖T−B‖₂ ≤ √ζ`. -/
theorem CompletenessWitness.l2_bounds (w : CompletenessWitness pcpp aux T S ζ δ) :
    l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
        Real.sqrt |T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2|) ≤
        Real.sqrt ζ ∧
      l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
        S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2) ≤ δ ∧
      l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
        (S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2) ^ 2) ≤ δ ^ 2 ∧
      l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
        T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2) ≤ Real.sqrt ζ := by
  have h4 : (uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      (S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2) ^ 4) ≤ δ ^ 4 :=
    uMean_pos_le pcpp (by have := w.δ_nonneg; positivity) (fun X x => (S X x - T X x) ^ 4) w.sparse
  obtain ⟨hD, hD2⟩ := l2_of_fourth _ δ w.δ_nonneg h4
  have hA : l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      Real.sqrt |T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2|) ≤
      Real.sqrt ζ := by
    unfold l2
    apply Real.sqrt_le_sqrt
    calc _ = uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          |T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2|) := by
          congr 1; funext p; exact Real.sq_sqrt (abs_nonneg _)
      _ ≤ ζ := w.approx
  refine ⟨hA, hD, hD2, le_trans (l2_mono fun p => ?_) hA⟩
  have hT := w.T_mem (posVar pcpp p.1 p.2.1) p.2.2
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_sub_bool_le_sqrt _ _ hT.1 hT.2

theorem completeness_testV {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (w : CompletenessWitness pcpp aux T S ζ δ) (G : PcppVar pcpp → Seed → BitInput q → Bool) :
    testV pcpp S G ≤ (Real.sqrt ζ + δ + δ ^ 2) ^ 2 := by
  obtain ⟨hA, hD, hD2, -⟩ := w.l2_bounds
  -- drop the masks, then the seed
  have hdrop : testV pcpp S G ≤ uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      validityPenalty (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 p.2.1)) (S (posVar pcpp p.1 p.2.1) p.2.2)) := by
    unfold testV
    rw [← uMean_pos_seed_drop pcpp (Seed := Seed)
      (fun i j x => validityPenalty (systematicConstraint pcpp x (posVar pcpp i j)) (S (posVar pcpp i j) x))]
    apply uMean_mono
    intro p
    have hP : 0 ≤ validityPenalty (systematicConstraint pcpp p.2.2.2 (posVar pcpp p.1 p.2.1))
        (S (posVar pcpp p.1 p.2.1) p.2.2.2) := by
      cases systematicConstraint pcpp p.2.2.2 (posVar pcpp p.1 p.2.1) <;>
        simp only [validityPenalty, booleanityPenalty, systematicPenalty] <;> positivity
    exact mul_le_of_le_one_left hP (bitR_le_one _)
  -- the pointwise bound and Minkowski
  set a := fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
    Real.sqrt |T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2|
  set D := fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
    S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2
  have hpt : ∀ p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q,
      validityPenalty (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 p.2.1)) (S (posVar pcpp p.1 p.2.1) p.2.2) ≤
        (a p + |D p| + D p ^ 2) ^ 2 := fun p =>
    validityPenalty_sparse_le _ _ (systematicConstraint_honest pcpp p.2.2 (aux p.2.2) _) _ _
      (w.T_mem _ _).1 (w.T_mem _ _).2
  have hmink : l2 (fun p => a p + |D p| + D p ^ 2) ≤ Real.sqrt ζ + δ + δ ^ 2 := by
    calc l2 (fun p => a p + |D p| + D p ^ 2) ≤ l2 (fun p => a p + |D p|) + l2 (fun p => D p ^ 2) :=
          l2_add_le _ _
      _ ≤ (l2 a + l2 (fun p => |D p|)) + l2 (fun p => D p ^ 2) := by gcongr; exact l2_add_le _ _
      _ ≤ (Real.sqrt ζ + δ) + δ ^ 2 := by
          have hDa : l2 (fun p => |D p|) ≤ δ :=
            (l2_mono fun p => by rw [abs_abs]).trans hD
          exact add_le_add (add_le_add hA hDa) hD2
  calc testV pcpp S G ≤ _ := hdrop
    _ ≤ uMean (fun p => (a p + |D p| + D p ^ 2) ^ 2) := uMean_mono hpt
    _ = l2 (fun p => a p + |D p| + D p ^ 2) ^ 2 := (l2_sq _).symm
    _ ≤ (Real.sqrt ζ + δ + δ ^ 2) ^ 2 := pow_le_pow_left₀ (l2_nonneg _) hmink 2

theorem completeness_testQ {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (w : CompletenessWitness pcpp aux T S ζ δ) (G : PcppVar pcpp → Seed → BitInput q → Bool) :
    testQ pcpp S G ≤ (1 + δ) ^ 2 := by
  obtain ⟨-, hD, -, -⟩ := w.l2_bounds
  have hdrop : testQ pcpp S G ≤ uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      S (posVar pcpp p.1 p.2.1) p.2.2 ^ 2) := by
    unfold testQ
    rw [← uMean_pos_seed_drop pcpp (Seed := Seed) (fun i j x => S (posVar pcpp i j) x ^ 2)]
    exact uMean_mono fun p => mul_le_of_le_one_left (sq_nonneg _) (bitR_le_one _)
  have hT : l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => T (posVar pcpp p.1 p.2.1) p.2.2) ≤ 1 :=
    l2_le_of_sq_le _ _ zero_le_one (by
      rw [one_pow]
      exact uMean_le_const' _ _ zero_le_one fun p => by
        have := w.T_mem (posVar pcpp p.1 p.2.1) p.2.2; nlinarith)
  have hS : l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => S (posVar pcpp p.1 p.2.1) p.2.2) ≤
      1 + δ := by
    calc _ = l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          T (posVar pcpp p.1 p.2.1) p.2.2 + (S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2)) := by
          congr 1; funext p; ring
      _ ≤ _ := l2_add_le _ _
      _ ≤ 1 + δ := add_le_add hT hD
  calc testQ pcpp S G ≤ _ := hdrop
    _ = l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => S (posVar pcpp p.1 p.2.1) p.2.2) ^ 2 :=
        (l2_sq _).symm
    _ ≤ (1 + δ) ^ 2 := pow_le_pow_left₀ (l2_nonneg _) hS 2

/-- The honest clause value `Cons_i(B(x))` is the Boolean clause value of the honest assignment. -/
theorem honestClause_eq (i : Fin (2 ^ pcpp.clauseBits)) (x : BitInput q) :
    clauseRealValue (pcpp.clauses i) (fun X => honestBit pcpp aux X x) =
      bitAsReal ((pcpp.clauses i).eval (pcpp.assignment x (aux x))) := by
  unfold honestBit
  exact clauseRealValue_bitAsReal _ _

/-- The honest proof's clause mean at `x` is its PCPP satisfied fraction. -/
theorem uMean_honestClause (x : BitInput q) :
    uMean (fun i => clauseRealValue (pcpp.clauses i) (fun X => honestBit pcpp aux X x)) =
      pcpp.satisfiedFraction x (aux x) := by
  rw [← ComponentwiseBranchExtraction.expect_bitAsReal_eq_satisfiedFraction, Finset.expect_eq_sum_div_card,
    Finset.card_univ]
  unfold uMean
  congr 1
  exact Finset.sum_congr rfl fun i _ => honestClause_eq i x

theorem completeness_testMu {Seed : Type} [Fintype Seed] [Nonempty Seed] {cp m : ℝ}
    (w : CompletenessWitness pcpp aux T S ζ δ) (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (hacc : cp ≤ uMean (fun x : BitInput q => pcpp.satisfiedFraction x (aux x)))
    (hmiss : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
      1 - bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)) ≤ m)
    (hu : Real.sqrt ζ + δ ≤ 2) :
    cp - m - 10 * (Real.sqrt ζ + δ) ≤ testMu pcpp S G := by
  obtain ⟨-, hD, -, hTB⟩ := w.l2_bounds
  set u := Real.sqrt ζ + δ with hu_def
  have hu0 : 0 ≤ u := add_nonneg (Real.sqrt_nonneg _) w.δ_nonneg
  -- the incidence-averaged distance from `S` to `B`
  set e := fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
    S (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2 with he
  have hel2 : l2 e ≤ u := by
    calc l2 e = l2 (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          (T (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2) +
            (S (posVar pcpp p.1 p.2.1) p.2.2 - T (posVar pcpp p.1 p.2.1) p.2.2)) := by
          congr 1; funext p; simp only [he]; ring
      _ ≤ _ := l2_add_le _ _
      _ ≤ u := add_le_add hTB hD
  have hesq : (uMean fun p => e p ^ 2) ≤ u ^ 2 := by
    rw [← l2_sq]; exact pow_le_pow_left₀ (l2_nonneg _) hel2 2
  -- one-position marginals
  set ej := fun (j : Fin 2) (p : Fin (2 ^ pcpp.clauseBits) × BitInput q) =>
    S (posVar pcpp p.1 j) p.2 - honestBit pcpp aux (posVar pcpp p.1 j) p.2 with hej
  have hesq' : (uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      (S (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2) ^ 2) ≤ u ^ 2 := hesq
  have hmarg : ∀ j, (uMean fun p => ej j p ^ 2) ≤ 2 * u ^ 2 := by
    intro j
    have h : (uMean fun p : Fin (2 ^ pcpp.clauseBits) × BitInput q =>
        (S (posVar pcpp p.1 j) p.2 - honestBit pcpp aux (posVar pcpp p.1 j) p.2) ^ 2) ≤
        2 * uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          (S (posVar pcpp p.1 p.2.1) p.2.2 - honestBit pcpp aux (posVar pcpp p.1 p.2.1) p.2.2) ^ 2) :=
      uMean_marginal_le (fun i j' x => (S (posVar pcpp i j') x - honestBit pcpp aux (posVar pcpp i j') x) ^ 2)
        (fun _ _ _ => sq_nonneg _) j
    calc (uMean fun p => ej j p ^ 2) = (uMean fun p : Fin (2 ^ pcpp.clauseBits) × BitInput q =>
          (S (posVar pcpp p.1 j) p.2 - honestBit pcpp aux (posVar pcpp p.1 j) p.2) ^ 2) := by rw [hej]
      _ ≤ _ := h
      _ ≤ 2 * u ^ 2 := by linarith
  have hmargl2 : ∀ j, l2 (ej j) ≤ Real.sqrt 2 * u := by
    intro j
    apply l2_le_of_sq_le _ _ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact hmarg j
  -- the clause error, averaged
  have hcons : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × BitInput q =>
      |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2) -
        clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2)|) ≤ 10 * u := by
    have hpt : ∀ p : Fin (2 ^ pcpp.clauseBits) × BitInput q,
        |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2) -
          clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2)| ≤
          |ej 0 p| + |ej 1 p| + |ej 0 p * ej 1 p| := by
      intro p
      have hb : ∀ X, 0 ≤ honestBit pcpp aux X p.2 ∧ honestBit pcpp aux X p.2 ≤ 1 := fun X =>
        Shared.bitAsReal_mem _
      have := Shared.clauseValue_sub_le (literalNegated (pcpp.clauses p.1).left)
        (literalNegated (pcpp.clauses p.1).right) (S (literalIndex (pcpp.clauses p.1).left) p.2)
        (S (literalIndex (pcpp.clauses p.1).right) p.2)
        (honestBit pcpp aux (literalIndex (pcpp.clauses p.1).left) p.2)
        (honestBit pcpp aux (literalIndex (pcpp.clauses p.1).right) p.2) (hb _) (hb _)
      simp only [hej, posVar_zero, posVar_one, abs_mul]
      exact this
    have h0 := uMean_abs_le_l2 (ej 0)
    have h1 := uMean_abs_le_l2 (ej 1)
    have h01 := uMean_abs_mul_le (ej 0) (ej 1)
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hl0 := hmargl2 0
    have hl1 := hmargl2 1
    have hprod : l2 (ej 0) * l2 (ej 1) ≤ (Real.sqrt 2 * u) * (Real.sqrt 2 * u) :=
      mul_le_mul hl0 hl1 (l2_nonneg _) (by positivity)
    have hsq2 : Real.sqrt 2 * u * (Real.sqrt 2 * u) = 2 * u ^ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith
    calc _ ≤ uMean (fun p => |ej 0 p| + |ej 1 p| + |ej 0 p * ej 1 p|) := uMean_mono hpt
      _ = uMean (fun p => |ej 0 p|) + uMean (fun p => |ej 1 p|) + uMean (fun p => |ej 0 p * ej 1 p|) := by
          rw [uMean_add, uMean_add]
      _ ≤ Real.sqrt 2 * u + Real.sqrt 2 * u + 2 * u ^ 2 := by linarith
      _ ≤ 10 * u := by nlinarith
  -- the honest clause mean over clauses, seeds and inputs
  haveI : Nonempty (Fin (2 ^ pcpp.clauseBits)) := ⟨⟨0, by positivity⟩⟩
  have hhon : cp ≤ uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
      clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)) := by
    rw [uMean_clause_seed_input (fun i x => clauseRealValue (pcpp.clauses i) (fun X => honestBit pcpp aux X x))]
    have e : (fun x : BitInput q => uMean (fun i => clauseRealValue (pcpp.clauses i)
        (fun X => honestBit pcpp aux X x))) = fun x => pcpp.satisfiedFraction x (aux x) := by
      funext x; exact uMean_honestClause x
    rw [e]; exact hacc
  have hcons' : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
      |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2) -
        clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)|) ≤ 10 * u := by
    rw [uMean_clause_seed_drop pcpp (fun i x => |clauseRealValue (pcpp.clauses i) (fun X => S X x) -
      clauseRealValue (pcpp.clauses i) (fun X => honestBit pcpp aux X x)|)]
    exact hcons
  -- pointwise: `M·Cons(S) ≥ Cons(B) − (1−M) − |Cons(S) − Cons(B)|`, the loss charged once
  have hpt : ∀ p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q),
      clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2) -
          (1 - bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)) -
          |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2) -
            clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)| ≤
        bitR (clauseMask pcpp G p.1 p.2.1 p.2.2) * clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2) := by
    intro p
    have hb0 := bitR_nonneg (clauseMask pcpp G p.1 p.2.1 p.2.2)
    have hb1 := bitR_le_one (clauseMask pcpp G p.1 p.2.1 p.2.2)
    have hc := Shared.bitAsReal_mem ((pcpp.clauses p.1).eval (pcpp.assignment p.2.2 (aux p.2.2)))
    rw [← honestClause_eq] at hc
    set b := bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)
    set cB := clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)
    set cS := clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2)
    have hd := neg_abs_le (cS - cB)
    have h1 : 0 ≤ (1 - b) * (1 - cB) := mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc.2)
    have h2 : b * (-|cS - cB|) ≤ b * (cS - cB) := mul_le_mul_of_nonneg_left hd hb0
    have h3 : 0 ≤ (1 - b) * |cS - cB| := mul_nonneg (sub_nonneg.mpr hb1) (abs_nonneg _)
    nlinarith [h1, h2, h3]
  calc cp - m - 10 * (Real.sqrt ζ + δ)
      ≤ uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
            clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)) -
          uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
            1 - bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)) -
          uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
            |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2) -
              clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)|) := by
        linarith
    _ = uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
          clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2) -
            (1 - bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)) -
            |clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2) -
              clauseRealValue (pcpp.clauses p.1) (fun X => honestBit pcpp aux X p.2.2)|) := by
        unfold uMean
        simp only [Finset.sum_sub_distrib]
        ring
    _ ≤ testMu pcpp S G := by
        unfold testMu
        exact uMean_mono hpt

/-- Means over the two positions of a clause. -/
theorem uMean_pos_split {C Ω : Type} [Fintype C] [Fintype Ω] (f : C → Fin 2 → Ω → ℝ) :
    uMean (fun p : C × Fin 2 × Ω => f p.1 p.2.1 p.2.2) =
      (uMean (fun p : C × Ω => f p.1 0 p.2) + uMean (fun p : C × Ω => f p.1 1 p.2)) / 2 := by
  rw [uMean_prod, uMean_prod (fun p : C × Ω => f p.1 0 p.2), uMean_prod (fun p : C × Ω => f p.1 1 p.2)]
  have h : ∀ i, uMean (fun c : Fin 2 × Ω => f i c.1 c.2) =
      (uMean (fun x => f i 0 x) + uMean (fun x => f i 1 x)) / 2 := by
    intro i
    rw [uMean_prod]
    unfold uMean
    rw [Fin.sum_univ_two, Fintype.card_fin]
    push_cast
    ring
  simp only [h]
  unfold uMean
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- Swapping the factors of a product does not change the mean. -/
theorem uMean_swap {A C : Type} [Fintype A] [Fintype C] (f : A × C → ℝ) :
    uMean f = uMean (fun p : C × A => f (p.2, p.1)) := by
  unfold uMean
  rw [Fintype.card_prod, Fintype.card_prod, mul_comm (Fintype.card A)]
  congr 1
  exact (Fintype.sum_equiv (Equiv.prodComm C A) _ _ fun _ => rfl).symm

theorem missingClause_le {Seed : Type} [Fintype Seed] (G : PcppVar pcpp → Seed → BitInput q → Bool) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
        1 - bitR (clauseMask pcpp G p.1 p.2.1 p.2.2)) ≤
      2 * uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
        1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) := by
  rw [uMean_pos_split (fun i j (ω : Seed × BitInput q) => 1 - bitR (G (posVar pcpp i j) ω.1 ω.2))]
  rw [mul_div_cancel₀ _ (two_ne_zero), ← uMean_add]
  apply uMean_mono
  intro p
  simp only [clauseMask]
  cases G (posVar pcpp p.1 0) p.2.1 p.2.2 <;> cases G (posVar pcpp p.1 1) p.2.1 p.2.2 <;> simp [bitR]

theorem missing_le {Seed : Type} [Fintype Seed] [Nonempty Seed] (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (R : PcppVar pcpp → BitInput q → ℝ) (Bc β ξ : ℝ) (hBc : 0 < Bc) (hξ : 0 ≤ ξ) (hR : ∀ X x, 0 ≤ R X x)
    (hfilt : ∀ X x, R X x ≤ Bc → uMean (fun e : Seed => 1 - bitR (G X e x)) ≤ ξ)
    (hpop : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => R (posVar pcpp p.1 p.2.1) p.2.2) ≤
      β * Bc) :
    uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
        1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤ β + ξ := by
  -- average the seed first
  have hseed : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
      1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) =
      uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
        uMean (fun e : Seed => 1 - bitR (G (posVar pcpp p.1 p.2.1) e p.2.2))) := by
    rw [uMean_prod, uMean_prod (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
      uMean (fun e : Seed => 1 - bitR (G (posVar pcpp p.1 p.2.1) e p.2.2)))]
    congr 1; funext i
    rw [uMean_prod, uMean_prod (fun c : Fin 2 × BitInput q =>
      uMean (fun e : Seed => 1 - bitR (G (posVar pcpp i c.1) e c.2)))]
    congr 1; funext j
    rw [uMean_swap, uMean_prod]
  rw [hseed]
  have hpt : ∀ p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q,
      uMean (fun e : Seed => 1 - bitR (G (posVar pcpp p.1 p.2.1) e p.2.2)) ≤
        ξ + bitR (decide (Bc < R (posVar pcpp p.1 p.2.1) p.2.2)) := by
    intro p
    by_cases h : Bc < R (posVar pcpp p.1 p.2.1) p.2.2
    · have h1 : uMean (fun e : Seed => 1 - bitR (G (posVar pcpp p.1 p.2.1) e p.2.2)) ≤ 1 :=
        uMean_le_const' _ _ zero_le_one fun e => by have := bitR_nonneg (G (posVar pcpp p.1 p.2.1) e p.2.2); linarith
      have hb : bitR (decide (Bc < R (posVar pcpp p.1 p.2.1) p.2.2)) = 1 := by simp [h, bitR]
      rw [hb]; linarith
    · have h1 := hfilt (posVar pcpp p.1 p.2.1) p.2.2 (not_lt.mp h)
      have hb : bitR (decide (Bc < R (posVar pcpp p.1 p.2.1) p.2.2)) = 0 := by simp [h, bitR]
      rw [hb]; linarith
  have hmarkov := markov_indicator (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
    R (posVar pcpp p.1 p.2.1) p.2.2) (fun p => hR _ _) hBc
  have hβ : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q => R (posVar pcpp p.1 p.2.1) p.2.2) / Bc
      ≤ β := by rw [div_le_iff₀ hBc]; exact hpop
  calc _ ≤ uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          ξ + bitR (decide (Bc < R (posVar pcpp p.1 p.2.1) p.2.2))) := uMean_mono hpt
    _ = ξ + uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × BitInput q =>
          bitR (decide (Bc < R (posVar pcpp p.1 p.2.1) p.2.2))) := by rw [uMean_add, uMean_const]
    _ ≤ β + ξ := by linarith

end Completeness

structure MaskedCompletenessParameters {cp sp : ℝ} (params : MaskedSoundnessParameters cp sp) where
  ζ : ℚ
  δ : ℚ
  β : ℚ
  ξ : ℚ
  ζ_nonneg : 0 ≤ ζ
  δ_nonneg : 0 ≤ δ
  β_nonneg : 0 ≤ β
  ξ_nonneg : 0 ≤ ξ
  ζ_le_one : ζ ≤ 1
  δ_le_one : δ ≤ 1
  V_slack : (Real.sqrt (ζ : ℝ) + δ + (δ : ℝ) ^ 2) ^ 2 + params.eps0 ≤ 2 * (params.v0 : ℝ)
  Q_slack : (1 + (δ : ℝ)) ^ 2 + params.eps0 ≤ 1 + (params.v0 : ℝ)
  μ_slack : (params.threshold : ℝ) + params.eps0 ≤ cp - 2 * ((β : ℝ) + ξ) - 10 * (Real.sqrt (ζ : ℝ) + δ)

theorem completeness_accepts {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    {params : MaskedSoundnessParameters cp sp} (cparams : MaskedCompletenessParameters params)
    {Seed : Type} [Fintype Seed] [Nonempty Seed] (aux : BitInput q → BitInput pcpp.auxiliaryBits)
    (T S : PcppVar pcpp → BitInput q → ℝ) (w : CompletenessWitness pcpp aux T S cparams.ζ cparams.δ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (hacc : cp ≤ uMean (fun x : BitInput q => pcpp.satisfiedFraction x (aux x)))
    (hmissing : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
        1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤ (cparams.β : ℝ) + cparams.ξ)
    (Vhat Qhat μhat : ℚ) (hV : |(Vhat : ℝ) - testV pcpp S G| ≤ params.eps0)
    (hQ : |(Qhat : ℝ) - testQ pcpp S G| ≤ params.eps0) (hμ : |(μhat : ℝ) - testMu pcpp S G| ≤ params.eps0) :
    MaskedAccepts params Vhat Qhat μhat := by
  have hζ1 : Real.sqrt (cparams.ζ : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast cparams.ζ_le_one
  have hδ1 : (cparams.δ : ℝ) ≤ 1 := by exact_mod_cast cparams.δ_le_one
  have hu : Real.sqrt (cparams.ζ : ℝ) + cparams.δ ≤ 2 := by linarith
  have hVb := completeness_testV w G
  have hQb := completeness_testQ w G
  have hmiss := (missingClause_le G).trans (mul_le_mul_of_nonneg_left hmissing zero_le_two)
  have hμb := completeness_testMu w G hacc hmiss hu
  have hVs := cparams.V_slack
  have hQs := cparams.Q_slack
  have hμs := cparams.μ_slack
  refine ⟨?_, ?_, ?_⟩
  · have : (Vhat : ℝ) ≤ 2 * params.v0 := by linarith [(abs_le.mp hV).2]
    exact_mod_cast this
  · have : (Qhat : ℝ) ≤ 1 + params.v0 := by linarith [(abs_le.mp hQ).2]
    exact_mod_cast this
  · have : (params.threshold : ℝ) ≤ μhat := by linarith [(abs_le.mp hμ).1]
    exact_mod_cast this

/-! ## The constants are jointly satisfiable -/

/-- Soundness constants with room for completeness: `v₀ = 10⁻⁵`, `ε₀ = v₀/2`, at the PCPP gap `c_p − s_p = 1/2`. -/
noncomputable def satJointSoundnessParameters : MaskedSoundnessParameters (3 / 4) (1 / 4) where
  v0 := 1 / 100000
  eps0 := 1 / 200000
  outerError := 1 / 100
  threshold := 1 / 2
  v0_pos := by norm_num
  v0_le := by norm_num
  eps0_nonneg := by norm_num
  eps0_le_v0 := by norm_num
  sp_nonneg := by norm_num
  thresholdAboveMidpoint := by norm_num
  roundingReserve := by
    have hs : Real.sqrt (24 * ((1 / 100000 : ℚ) : ℝ)) ≤ 1 / 50 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    push_cast at hs ⊢
    linarith
  outerReserve := by norm_num

/-- Completeness constants at those soundness constants: `ζ = δ = 10⁻⁶`, `β = ξ = 1/100`. -/
noncomputable def satMaskedCompletenessParameters : MaskedCompletenessParameters satJointSoundnessParameters where
  ζ := 1 / 1000000
  δ := 1 / 1000000
  β := 1 / 100
  ξ := 1 / 100
  ζ_nonneg := by norm_num
  δ_nonneg := by norm_num
  β_nonneg := by norm_num
  ξ_nonneg := by norm_num
  ζ_le_one := by norm_num
  δ_le_one := by norm_num
  V_slack := by
    have h : Real.sqrt ((1 / 1000000 : ℚ) : ℝ) = 1 / 1000 := by
      rw [show ((1 / 1000000 : ℚ) : ℝ) = (1 / 1000 : ℝ) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h]; simp only [satJointSoundnessParameters]; norm_num
  Q_slack := by simp only [satJointSoundnessParameters]; norm_num
  μ_slack := by
    have h : Real.sqrt ((1 / 1000000 : ℚ) : ℝ) = 1 / 1000 := by
      rw [show ((1 / 1000000 : ℚ) : ℝ) = (1 / 1000 : ℝ) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h]; simp only [satJointSoundnessParameters]; norm_num

end NearCubicWires.WireExponent3_5.Transfer
