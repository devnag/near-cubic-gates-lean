import Proof.Wire_3_5.PrimAsmSymQ

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrQ
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime

/-- `Σ_{p ≤ c prime} p`: the number of `(p, s mod p)` rows. -/
def primeSum (c : ℕ) : ℕ := ∑ p ∈ primesUpTo c, p

/-- **The THR sample count as a formula** in the seed bits, `|𝒢|` and the cutoff. -/
def thrQval (D kh n seedBits G c : ℕ) : ℕ :=
  Sampler.sampleCount kh D n (2 ^ seedBits * (G * primeSum c) * (2 * G * c + 1) ^ 2 + 1)

theorem card_primeRows (c : ℕ) : Fintype.card (Σ pr : PrimeIndex c, ZMod pr.val) = primeSum c := by
  rw [Fintype.card_sigma]
  simp only [ZMod.card]
  exact Finset.sum_coe_sort (primesUpTo c) id

theorem card_thrEq (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) :
    Fintype.card (ThrEq P Cs alg) =
      ∏ i : Fin (List.ofFn Cs).length, (RepairOrdinary.ThresholdRows.children alg ((List.ofFn Cs).get i)).length := by
  unfold ThrEq RepairOrdinary.ThresholdRows.Selection
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]

/-- **The prime cutoff from the equations** (Theorem 2.5's tuned surrogate): `(max 24 (6(e+1)(den+1)))²` with
`e = ⌈log₂(Σ_g ‖L_g‖ + 1)⌉` over all child selections `g`. -/
theorem thrCutoff_eq (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) :
    thrCutoff P Cs alg den =
      (max 24 (6 * (Nat.clog 2 ((∑ g : ThrEq P Cs alg, equationMagnitudeBound (thrRealize P Cs alg g)) + 1) + 1) *
        (den + 1))) ^ 2 := rfl

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **`Q` at a THR call**: the sample count is the formula at the call's numbers. -/
theorem thrCount_eq (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) :
    SeedFix.thrCount alg I hs Cs =
      thrQval I.D (SeedFix.callKh (I.starParams n hs)) n (I.filterParams .thr n).seedBits
        (Fintype.card (ThrEq (I.starParams n hs) Cs alg))
        (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)) := by
  unfold SeedFix.thrCount thrQval SeedFix.thrMassNat
  refine congrArg (Sampler.sampleCount _ _ _) ?_
  rw [Fintype.card_prod, Fintype.card_prod, card_gapSeed, card_primeRows]

/-- The THR denominator `K = 8(|𝒢|+1)n^D` (the prime surrogate's error and the lists' target). -/
theorem thrCallDen_eq (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) :
    thrCallDen alg I hs Cs = 8 * (Fintype.card (ThrEq (I.starParams n hs) Cs alg) + 1) * n ^ I.D := rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrQ
