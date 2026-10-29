import SourceAdapters.Proximity.ConstructorPolynomial

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the exact target constructor machine, obtained only
after all ordinary computations and representation adapters are composed. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.Published.CW19Proximity

theorem source_to_tm2 {A : Type} (input output : A → List Bool)
    (h : SourcePolyTime input output) :
    Nonempty (Turing.TM2ComputableInPolyTime input (fun w : List Bool => w) output) := by
  obtain ⟨K, e, hP⟩ := h
  exact Machine.ordinaryToTM2PolyTime input (fun w => w) output _ hP ⟨K, e, fun _ => le_rfl⟩

theorem target_verifier_computable {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    Nonempty (Turing.TM2ComputableInPolyTime Circuit.word (fun w : List Bool => w)
      (fun C => (convertedVerifier V C).word)) :=
  source_to_tm2 _ _ (target_verifier_polynomial V proofLength honest a hr hP)

end NearCubicGates.Adapters.Proximity
