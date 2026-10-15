import Proof.Wire_3_5.Skeleton
import Proof.Wire_3_5.StarCarrier

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- At a call, every circuit's residual population is at most the named carriers' populations, at every star
point. -/
theorem call_population_le (I : PrimitiveInputs B) {req : PrimRequest} (h : I.Call req) (i : Fin req.a)
    (c u v : BitInput req.n) :
    Carrier.population (req.gates i) c u v ≤ (req.carriers.map fun X => Carrier.population X c u v).sum :=
  GatesIn.population_le h.1 i c u v

/-- At a call, every circuit's `R(x)` is at most `Σ_X R_X(x)` at every input `x`, through its decomposition in
any partition `σ` of the call's star (in particular the call's translation). -/
theorem call_inputPopulation_le (I : PrimitiveInputs B) {req : PrimRequest} (h : I.Call req) (hs : I.StarAt req.n)
    (i : Fin req.a) (σ : (I.starParams req.n hs).Translation) (x : BitInput req.n) :
    inputPopulation (I.starParams req.n hs) σ (req.gates i) x ≤
      (req.carriers.map fun X => inputPopulation (I.starParams req.n hs) σ X x).sum :=
  GatesIn.population_le h.1 i _ _ _

/-- The residual vector has two bits per atom occurrence. -/
theorem length_residualBits {n : ℕ} (X : Carrier n) (c u v : BitInput n) :
    (Carrier.residualBits X c u v).length = 2 * X.length := by
  induction X with
  | nil => rfl
  | cons g X ih =>
    simp only [Carrier.residualBits, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]; ring

theorem call_residualBits_len (I : PrimitiveInputs B) {req : PrimRequest} (h : I.Call req)
    (hs : I.StarAt req.n) (X : Carrier req.n) (hX : X ∈ req.carriers) (x : BitInput req.n) :
    (inputResidualBits (I.starParams req.n hs) ((I.starParams req.n hs).translationOfCodes req.translation)
      X x).length ≤ (I.filterParams req.mode req.n).len := by
  unfold inputResidualBits
  rw [length_residualBits]
  exact Nat.mul_le_mul_left 2 (h.2.1 X hX).1

theorem mask_of_call (I : PrimitiveInputs B) {req : PrimRequest} (hs : I.StarAt req.n) (e : I.Seed req.mode req.n)
    (x : BitInput req.n) :
    I.mask req e x = req.carriers.all fun X => gapFilter (I.filterParams req.mode req.n) e
      (inputResidualBits (I.starParams req.n hs) ((I.starParams req.n hs).translationOfCodes req.translation) X x) := by
  unfold PrimitiveInputs.mask
  rw [dif_pos hs]

end NearCubicWires.WireExponent3_5.Stars
