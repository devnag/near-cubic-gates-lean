import Proof.Wire_3_5.StarRange

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-! ## The four corners and the indicators -/

def corners {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) : Fin 4 → Bool :=
  ![T (xorInput (xorInput c u) v), T (xorInput c u), T (xorInput c v), T c]

/-- The mixed difference as a function of the corners. -/
def cornerDelta (ρ : Fin 4 → Bool) : ℤ := bitZ (ρ 0) - bitZ (ρ 1) - bitZ (ρ 2) + bitZ (ρ 3)

/-- `Z⁺` as a function of the four corner values. -/
def cornerPlus (ρ : Fin 4 → Bool) : Bool := decide (cornerDelta ρ = 1)

/-- `Z⁻` as a function of the four corner values. -/
def cornerMinus (ρ : Fin 4 → Bool) : Bool := decide (cornerDelta ρ = -1)

theorem mixedDifference_eq_corner {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    mixedDifference T c u v = cornerDelta (corners T c u v) := rfl

theorem residualPlus_eq_corner {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualPlus T c u v = cornerPlus (corners T c u v) := rfl

theorem residualMinus_eq_corner {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualMinus T c u v = cornerMinus (corners T c u v) := rfl

theorem residual_disjoint {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    ¬ (residualPlus T c u v = true ∧ residualMinus T c u v = true) := by
  simp only [residualPlus, residualMinus, decide_eq_true_eq]
  rintro ⟨h1, h2⟩; omega

theorem mixedDifference_eq_residuals {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n)
    (h : mixedDifference T c u v ∈ ({-1, 0, 1} : Finset ℤ)) :
    mixedDifference T c u v = bitZ (residualPlus T c u v) - bitZ (residualMinus T c u v) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold residualPlus residualMinus bitZ
  rcases h with h | h | h <;> simp [h]

/-- The algebraic normal form of `Z⁺` over `𝔽₂` in the corners `0 = T(c+u+v)`, `1 = T(c+u)`, `2 = T(c+v)`,
`3 = T(c)`. -/
def zPlusF2 : F2Poly (Fin 4) :=
  [[0], [3], [0, 1], [0, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

/-- The algebraic normal form of `Z⁻` over `𝔽₂`. -/
def zMinusF2 : F2Poly (Fin 4) :=
  [[1], [2], [0, 1], [0, 2], [1, 3], [2, 3], [0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]

/-- A single corner as an `𝔽₂` factor. -/
def corner (i : Fin 4) : F2Poly (Fin 4) := [[i]]

/-- The integer multilinear form of `Z⁺`: `Σ_S c_S ∏_{i∈S} x_i` with the Möbius coefficients. -/
def zPlusInt : IntExpression (Fin 4) :=
  [(1, [corner 0]), (1, [corner 3]), (-1, [corner 0, corner 1]), (-1, [corner 0, corner 2]),
   (-2, [corner 0, corner 3]), (-1, [corner 1, corner 3]), (-1, [corner 2, corner 3]),
   (1, [corner 0, corner 1, corner 2]), (3, [corner 0, corner 1, corner 3]), (3, [corner 0, corner 2, corner 3]),
   (1, [corner 1, corner 2, corner 3]), (-4, [corner 0, corner 1, corner 2, corner 3])]

/-- The integer multilinear form of `Z⁻`. -/
def zMinusInt : IntExpression (Fin 4) :=
  [(1, [corner 1]), (1, [corner 2]), (-1, [corner 0, corner 1]), (-1, [corner 0, corner 2]),
   (-2, [corner 1, corner 2]), (-1, [corner 1, corner 3]), (-1, [corner 2, corner 3]),
   (3, [corner 0, corner 1, corner 2]), (1, [corner 0, corner 1, corner 3]), (1, [corner 0, corner 2, corner 3]),
   (3, [corner 1, corner 2, corner 3]), (-4, [corner 0, corner 1, corner 2, corner 3])]

theorem fin4_fun_eq (ρ : Fin 4 → Bool) : ρ = ![ρ 0, ρ 1, ρ 2, ρ 3] := by
  funext i; fin_cases i <;> rfl

theorem zPlusF2_eval_bool : ∀ a b c d : Bool, F2Poly.eval zPlusF2 ![a, b, c, d] = cornerPlus ![a, b, c, d] := by
  decide

theorem zMinusF2_eval_bool : ∀ a b c d : Bool, F2Poly.eval zMinusF2 ![a, b, c, d] = cornerMinus ![a, b, c, d] := by
  decide

theorem zPlusInt_eval_bool :
    ∀ a b c d : Bool, IntExpression.eval zPlusInt ![a, b, c, d] = bitZ (cornerPlus ![a, b, c, d]) := by
  decide

theorem zMinusInt_eval_bool :
    ∀ a b c d : Bool, IntExpression.eval zMinusInt ![a, b, c, d] = bitZ (cornerMinus ![a, b, c, d]) := by
  decide

/-- **The `𝔽₂` representation of `Z⁺`** at every corner pattern. -/
theorem zPlusF2_eval (ρ : Fin 4 → Bool) : F2Poly.eval zPlusF2 ρ = cornerPlus ρ := by
  rw [fin4_fun_eq ρ]; exact zPlusF2_eval_bool _ _ _ _

/-- **The `𝔽₂` representation of `Z⁻`** at every corner pattern. -/
theorem zMinusF2_eval (ρ : Fin 4 → Bool) : F2Poly.eval zMinusF2 ρ = cornerMinus ρ := by
  rw [fin4_fun_eq ρ]; exact zMinusF2_eval_bool _ _ _ _

/-- **The integer representation of `Z⁺`** at every corner pattern. -/
theorem zPlusInt_eval (ρ : Fin 4 → Bool) : IntExpression.eval zPlusInt ρ = bitZ (cornerPlus ρ) := by
  rw [fin4_fun_eq ρ]; exact zPlusInt_eval_bool _ _ _ _

/-- **The integer representation of `Z⁻`** at every corner pattern. -/
theorem zMinusInt_eval (ρ : Fin 4 → Bool) : IntExpression.eval zMinusInt ρ = bitZ (cornerMinus ρ) := by
  rw [fin4_fun_eq ρ]; exact zMinusInt_eval_bool _ _ _ _

theorem residual_degrees :
    F2Poly.degree zPlusF2 ≤ 4 ∧ F2Poly.degree zMinusF2 ≤ 4 ∧
      zPlusInt.maxFactors ≤ 4 ∧ zPlusInt.maxDegree ≤ 1 ∧ zMinusInt.maxFactors ≤ 4 ∧ zMinusInt.maxDegree ≤ 1 := by
  decide

/-- The residual bits of a gate at `(c, u, v)` through its corners, in both rings. -/
theorem residualPlus_f2 {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualPlus T c u v = F2Poly.eval zPlusF2 (corners T c u v) := by rw [zPlusF2_eval]; rfl

theorem residualMinus_f2 {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    residualMinus T c u v = F2Poly.eval zMinusF2 (corners T c u v) := by rw [zMinusF2_eval]; rfl

theorem residualPlus_int {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    bitZ (residualPlus T c u v) = IntExpression.eval zPlusInt (corners T c u v) := by rw [zPlusInt_eval]; rfl

theorem residualMinus_int {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    bitZ (residualMinus T c u v) = IntExpression.eval zMinusInt (corners T c u v) := by rw [zMinusInt_eval]; rfl

section Identity
variable {R : Type} [CommRing R] {n : ℕ}

def scoreLeft (gates : List (R × NormalizedThresholdGate n)) (c u : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput c u)) : R)).sum

def scoreRight (gates : List (R × NormalizedThresholdGate n)) (c v : BitInput n) : R :=
  (gates.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c v)) : R) - (bitZ (p.2.eval c) : R))).sum

/-- The signed residual term `Σ_i w_i (Z_i^+ − Z_i^-)`. -/
def residualTerm (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n) : R :=
  (gates.map fun p => p.1 * ((bitZ (residualPlus p.2.eval c u v) : R) - (bitZ (residualMinus p.2.eval c u v) : R))).sum

/-- The weighted top score at `c + u + v`. -/
def topScore (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput (xorInput c u) v)) : R)).sum

/-- One gate's decomposition over the integers, when the left and right flips are disjoint. -/
theorem gate_decomposition (g : NormalizedThresholdGate n) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    bitZ (g.eval (xorInput (xorInput c u) v)) =
      bitZ (g.eval (xorInput c u)) + (bitZ (g.eval (xorInput c v)) - bitZ (g.eval c)) +
        (bitZ (residualPlus g.eval c u v) - bitZ (residualMinus g.eval c u v)) := by
  rw [← mixedDifference_eq_residuals g.eval c u v (mixedDifference_range g c u v hdisj)]
  unfold mixedDifference; ring

theorem mixed_score (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    topScore gates c u v = scoreLeft gates c u + scoreRight gates c v + residualTerm gates c u v := by
  induction gates with
  | nil => simp [topScore, scoreLeft, scoreRight, residualTerm]
  | cons p gates ih =>
    simp only [topScore, scoreLeft, scoreRight, residualTerm, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have h := congrArg (fun z : ℤ => (z : R)) (gate_decomposition p.2 c u v hdisj)
    simp only [Int.cast_add, Int.cast_sub] at h
    rw [h]; ring

def rowLeft (a0 : R) (gates : List (R × NormalizedThresholdGate n)) (c u : BitInput n) : R :=
  a0 + (gates.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c u)) : R) - (bitZ (p.2.eval c) : R))).sum

def rowRight (gates : List (R × NormalizedThresholdGate n)) (c v : BitInput n) : R :=
  (gates.map fun p => p.1 * (bitZ (p.2.eval (xorInput c v)) : R)).sum

theorem row_identity (a0 : R) (gates : List (R × NormalizedThresholdGate n)) (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    a0 + topScore gates c u v = rowLeft a0 gates c u + rowRight gates c v + residualTerm gates c u v := by
  rw [mixed_score gates c u v hdisj]
  unfold scoreLeft scoreRight rowLeft rowRight
  have : ∀ l : List (R × NormalizedThresholdGate n),
      (l.map fun p => p.1 * (bitZ (p.2.eval (xorInput c u)) : R)).sum +
        (l.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c v)) : R) - (bitZ (p.2.eval c) : R))).sum =
      (l.map fun p => p.1 * ((bitZ (p.2.eval (xorInput c u)) : R) - (bitZ (p.2.eval c) : R))).sum +
        (l.map fun p => p.1 * (bitZ (p.2.eval (xorInput c v)) : R)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp only [List.map_cons, List.sum_cons]; linear_combination ih
  rw [← add_assoc a0, add_assoc a0 (List.sum _), ← this]

end Identity

theorem star_mixed_score {R : Type} [CommRing R] (P : StarParams) (gates : List (R × NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    topScore gates c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) =
      scoreLeft gates c (P.errorVector P.leftBlock u) + scoreRight gates c (P.errorVector P.rightBlock v) +
        residualTerm gates c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) :=
  mixed_score gates c _ _ (errorVector_disjoint P u v)

/-- `row:identity` at the star parametrization. -/
theorem star_row_identity {R : Type} [CommRing R] (P : StarParams) (a0 : R)
    (gates : List (R × NormalizedThresholdGate P.n)) (c : BitInput P.n) (u v : P.Errors) :
    a0 + topScore gates c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) =
      rowLeft a0 gates c (P.errorVector P.leftBlock u) + rowRight gates c (P.errorVector P.rightBlock v) +
        residualTerm gates c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) :=
  row_identity a0 gates c _ _ (errorVector_disjoint P u v)

end NearCubicWires.WireExponent3_5.Stars
