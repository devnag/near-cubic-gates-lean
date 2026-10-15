import Proof.Foundations.ComponentwiseValidity
import Proof.Foundations.SupplierPipeline
import Proof.Wire_3_5.MaskedExpectation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared
open NearCubicWires NearCubicWires.ComponentwiseValidity

theorem bitR_eq_bitAsReal (b : Bool) : bitR b = bitAsReal b := rfl

/-- REL's `booleanMean` is S7's `uMean` of the indicator (the §13.4 S7 gate: REL lemmas apply unchanged). -/
theorem booleanMean_eq_uMean {Ω : Type} [Fintype Ω] (b : Ω → Bool) :
    SupplierPipeline.booleanMean b = uMean (fun ω => bitR (b ω)) := rfl

def MaskedRounding : Prop :=
  ∀ {Clause Ω : Type} [Fintype Clause] [Fintype Ω]
    (S : Clause → Fin 2 → Ω → ℝ) (con : Clause → Fin 2 → Ω → Option Bool)
    (neg : Clause → Fin 2 → Bool) (G : Clause → Fin 2 → Ω → Bool) (v₀ : ℝ),
    0 < v₀ → v₀ ≤ 1 / 24 →
    uMean (fun p : Clause × Fin 2 × Ω =>
        bitR (G p.1 p.2.1 p.2.2) * validityPenalty (con p.1 p.2.1 p.2.2) (S p.1 p.2.1 p.2.2)) ≤ 3 * v₀ →
    uMean (fun p : Clause × Fin 2 × Ω => bitR (G p.1 p.2.1 p.2.2) * S p.1 p.2.1 p.2.2 ^ 2) ≤ 1 + 2 * v₀ →
    |uMean (fun p : Clause × Ω =>
        bitR (G p.1 0 p.2 && G p.1 1 p.2) *
          (clauseValue (neg p.1 0) (neg p.1 1) (S p.1 0 p.2) (S p.1 1 p.2) -
           clauseValue (neg p.1 0) (neg p.1 1)
             (bitAsReal (validityRound (con p.1 0 p.2) (S p.1 0 p.2)))
             (bitAsReal (validityRound (con p.1 1 p.2) (S p.1 1 p.2)))))| ≤
      5 * Real.sqrt (24 * v₀)

def SparseWitness : Prop :=
  ∀ {J Ω : Type} [Fintype J] [Fintype Ω] (C : J → Ω → Bool) (α : J → ℝ) (Λbar : ℝ) (s : ℕ),
    1 ≤ s → 1 ≤ Λbar → ∑ j, |α j| ≤ Λbar →
    ∃ (σ : Fin s → ℤ) (atom : Fin s → Option J), (∀ a, σ a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
      uMean (fun x : Ω =>
        (Λbar / s * ∑ a, (σ a : ℝ) * (match atom a with | some j => bitR (C j x) | none => 0) -
          ∑ j, α j * bitR (C j x)) ^ 4) ≤ 19 * Λbar ^ 4 / (s : ℝ) ^ 2

example (c : Option Bool) (v : ℝ) :
    (v - bitAsReal (validityRound c v)) ^ 2 ≤ 4 * validityPenalty c v :=
  validityRound_distance_sq_le c v

end NearCubicWires.WireExponent3_5.Shared
