import SourceAdapters.Proximity.AllocatedConstructor
import SourceAdapters.Proximity.CompilerGrowth
import SourceAdapters.Proximity.AddressSupplier

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the complete ordinary constructor, including its
paid length prefix, uniform allocation, source calls and exact trimming. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity SourceCallee

 theorem constructor_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime sourceCircuitWord (fun S => Joins.trimRequestWord (clauseTrimRequest V S)) := by
  obtain ⟨K, e, ⟨P⟩⟩ := hP
  obtain ⟨A, D, hA, halloc⟩ := sufficient_allocation V a K e hr
  let Q := allocatedConstructorWordFunction V proofLength honest K e P a A D hA hr
    (fun S => (halloc S).1) (fun S => (halloc S).2.1) (fun S => (halloc S).2.2)
  have hN := constructorCost_bounded V a hr (allocation A D) (allocation A D)
    (fun S => widthMeasure q (V S).randomBits (callBudgetCap q a K e (sourceMeasure S)))
    (allocation_bounded A D) (allocation_bounded A D) (widthMeasure_bounded V a hr K e)
  obtain ⟨B, d, hB⟩ := compiler_budget_bounded (callee V proofLength honest _ P) A D _ hN
  let F : WordFunction SourceCircuit sourceCircuitWord
      (fun S => frame (LengthPrefix.wrapped (sourceCircuitWord S)))
      (fun S => 10000 * ((sourceCircuitWord S).length + 1) ^ 2) := {
    program := LengthPrefix.polynomialWordFunction.program
    realizes := fun S => LengthPrefix.polynomialWordFunction.realizes (sourceCircuitWord S) }
  obtain ⟨C, f, hC⟩ := Code.composeFramed_budget_poly sourceCircuitWord _ _
    ⟨10000, 2, fun _ => le_rfl⟩ ⟨B, d, hB⟩
  exact ⟨C, f, ⟨(Code.composeFramed F Q).enlargeBudget hC⟩⟩

theorem source_verifier_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime sourceCircuitWord (fun S => (trimVerifier (clauseVerifier (V S))).word) :=
  source_composite_polynomial _ _ _ (constructor_polynomial V proofLength honest a hr hP)
    (trimming_algorithms V).1

theorem source_addresses_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime sourceCircuitWord (fun S => Joins.trimAddressWord (clauseTrimRequest V S)) :=
  source_composite_polynomial _ _ _ (constructor_polynomial V proofLength honest a hr hP)
    (trimming_algorithms V).2

theorem target_verifier_polynomial {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime Circuit.word (fun C => (convertedVerifier V C).word) := by
  apply source_composite_polynomial _ _ _ target_source_polynomial
  obtain ⟨K, e, ⟨P⟩⟩ := source_verifier_polynomial V proofLength honest a hr hP
  exact ⟨K, e, ⟨{ program := P.program, realizes := fun C => P.realizes (sourceCircuit C) }⟩⟩

end NearCubicGates.Adapters.Proximity
