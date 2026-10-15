import Proof.Wire_3_5.StarCarrier
import Proof.Wire_3_5.StarPopulation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline Finset

def Carrier.starPopulation (P : StarParams) (X : Carrier P.n) (c : BitInput P.n) (u v : P.Errors) : ℕ :=
  Carrier.population X c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

noncomputable def Carrier.popMean (P : StarParams) (X : Carrier P.n) : ℝ :=
  (∑ c : BitInput P.n, ∑ u : P.Errors, ∑ v : P.Errors, (Carrier.starPopulation P X c u v : ℝ)) /
    (2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2)

noncomputable def _root_.NearCubicWires.WireExponent3_5.Shared.StarParams.popRate (P : StarParams) : ℝ :=
  4 * Real.sqrt 2 * (P.r * Real.sqrt P.r) / (P.n * Real.sqrt P.n)

theorem popRate_nonneg (P : StarParams) : 0 ≤ P.popRate := by
  unfold StarParams.popRate; positivity

theorem atomResidual_star_eq (P : StarParams) (g : NormalizedThresholdGate P.n) (c : BitInput P.n)
    (u v : P.Errors) :
    Carrier.atomResidual g c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) =
      if mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0
      then 1 else 0 := by
  have h := star_range P g c u v
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold Carrier.atomResidual residualPlus residualMinus
  rcases h with h | h | h <;> simp [h]

/-- `Z⁺ + Z⁻ ≤ [Δ ≠ 0]` holds at every point. -/
theorem atomResidual_le_indicator {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) :
    Carrier.atomResidual g c u v ≤ if mixedDifference g.eval c u v ≠ 0 then 1 else 0 := by
  unfold Carrier.atomResidual residualPlus residualMinus
  by_cases h1 : mixedDifference g.eval c u v = 1
  · simp [h1]
  · by_cases h2 : mixedDifference g.eval c u v = -1
    · simp [h2]
    · simp [h1, h2]

/-- One atom's summed population is at most `C_0 r^{3/2} W/n^{3/2}` times the number of sample points
(`starPopulation_holds` with `f + 1 = W`). -/
theorem atom_sum_le (P : StarParams) (g : NormalizedThresholdGate P.n) :
    (∑ c : BitInput P.n, ∑ u : P.Errors, ∑ v : P.Errors,
        (Carrier.atomResidual g c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) : ℝ)) ≤
      P.popRate * (Carrier.atomWires g : ℝ) * (2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2) := by
  classical
  set D : ℝ := 2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2 with hD
  have hDpos : 0 < D := by
    have : 0 < Fintype.card P.Errors := Fintype.card_pos
    positivity
  -- pointwise, then exchange the center sum to the inside
  have h1 : (∑ c : BitInput P.n, ∑ u : P.Errors, ∑ v : P.Errors,
        (Carrier.atomResidual g c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) : ℝ)) ≤
      ((∑ u : P.Errors, ∑ v : P.Errors, (univ.filter fun c : BitInput P.n =>
          mixedDifference g.eval c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) ≠ 0).card : ℕ) : ℝ) := by
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro u _
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro v _
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_le_sum; intro c _
    have := atomResidual_le_indicator g c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)
    split_ifs with h
    · exact_mod_cast (by simpa [h] using this)
    · exact_mod_cast (by simpa [h] using this)
  have h2 := starPopulation_holds P g
  rw [div_le_iff₀ hDpos] at h2
  have hf : ((gateSupport g).card : ℝ) ≤ (Carrier.atomWires g : ℝ) := by
    unfold Carrier.atomWires gateSupport; push_cast; linarith
  have hr := popRate_nonneg P
  calc _ ≤ _ := h1
    _ ≤ 4 * Real.sqrt 2 * (P.r * Real.sqrt P.r) * (gateSupport g).card / (P.n * Real.sqrt P.n) * D := h2
    _ = P.popRate * ((gateSupport g).card : ℝ) * D := by unfold StarParams.popRate; ring
    _ ≤ P.popRate * (Carrier.atomWires g : ℝ) * D := by
        apply mul_le_mul_of_nonneg_right _ hDpos.le
        exact mul_le_mul_of_nonneg_left hf hr

theorem Carrier.popMean_le (P : StarParams) (X : Carrier P.n) :
    Carrier.popMean P X ≤ P.popRate * (Carrier.wires X : ℝ) := by
  set D : ℝ := 2 ^ P.n * (Fintype.card P.Errors : ℝ) ^ 2 with hD
  have hDpos : 0 < D := by
    have : 0 < Fintype.card P.Errors := Fintype.card_pos
    positivity
  unfold Carrier.popMean
  rw [div_le_iff₀ hDpos]
  induction X with
  | nil => simp [Carrier.starPopulation, Carrier.population, Carrier.wires]
  | cons g X ih =>
    have hsplit : ∀ c u v, (Carrier.starPopulation P (g :: X) c u v : ℝ) =
        (Carrier.atomResidual g c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v) : ℝ) +
          (Carrier.starPopulation P X c u v : ℝ) := by
      intro c u v
      simp [Carrier.starPopulation, Carrier.population]
    simp only [hsplit, Finset.sum_add_distrib]
    have hw : (Carrier.wires (g :: X) : ℝ) = (Carrier.atomWires g : ℝ) + (Carrier.wires X : ℝ) := by
      simp [Carrier.wires]
    rw [hw]
    have := atom_sum_le P g
    nlinarith

theorem popMean_thrGates_le (P : StarParams) (C : NormalizedThresholdThresholdCircuit P.n) :
    Carrier.popMean P (thrGates C) ≤ P.popRate * (C.wireCount : ℝ) :=
  (Carrier.popMean_le P _).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast wires_thrGates_le C) (popRate_nonneg P))

theorem popMean_symGates_le (P : StarParams) (C : NormalizedSymmetricThresholdCircuit P.n) :
    Carrier.popMean P (symGates C) ≤ P.popRate * (C.wireCount : ℝ) :=
  (Carrier.popMean_le P _).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast wires_symGates_le C) (popRate_nonneg P))

theorem weighted_popMean_le (P : StarParams) (pop : List (ℝ × Carrier P.n)) (hp : ∀ x ∈ pop, 0 ≤ x.1) :
    (pop.map fun x => x.1 * Carrier.popMean P x.2).sum ≤
      P.popRate * (pop.map fun x => x.1 * (Carrier.wires x.2 : ℝ)).sum := by
  induction pop with
  | nil => simp
  | cons x pop ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 : x.1 * Carrier.popMean P x.2 ≤ P.popRate * (x.1 * (Carrier.wires x.2 : ℝ)) := by
      have := Carrier.popMean_le P x.2
      have hx := hp x (List.mem_cons_self)
      nlinarith
    have h2 := ih fun y hy => hp y (List.mem_cons_of_mem _ hy)
    linarith

/-- The containment duty at the star: every admitted circuit's `R` is at most `Σ_X R_X` of the named carriers at
every star point, hence also on average. -/
theorem GatesIn.starPopulation_le (P : StarParams) {a : ℕ} {gates : Fin a → Carrier P.n}
    {named : List (Carrier P.n)} (h : GatesIn gates named) (i : Fin a) (c : BitInput P.n) (u v : P.Errors) :
    Carrier.starPopulation P (gates i) c u v ≤
      (named.map fun X => Carrier.starPopulation P X c u v).sum :=
  h.population_le i c _ _

end NearCubicWires.WireExponent3_5.Stars
