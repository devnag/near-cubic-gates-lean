import SourceAdapters.Proximity.OrdinaryCalls

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": readable outputs for the actual source-call dispatcher.
Scalar and proof outputs receive paid framing. Query addresses retain their
own tag and framed natural; fixed-width outputs retain their exact raw word. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity

def normalizedConstructorOutput {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) : ConstructorCall V → List Bool :=
  TaggedCalls.payload (fun C => frame (V C).randomBits.bits)
    (TaggedCalls.payload (fun p => frame ((V p.1).queryCount p.2).bits)
      (TaggedCalls.payload (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2))
        (TaggedCalls.payload (fun p => [(V p.1).decision p.2.1 p.2.2]) blockTableWord)))

theorem normalized_constructor_polynomial {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (hr : SourcePolyTime sourceCircuitWord (fun C => (V C).randomBits.bits))
    (hc : SourcePolyTime (coinRequestWord (V := V)) (fun p => ((V p.1).queryCount p.2).bits))
    (hq : SourcePolyTime (queryRequestWord (V := V))
      (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2)))
    (hd : SourcePolyTime (decisionRequestWord (V := V)) (fun p => [(V p.1).decision p.2.1 p.2.2])) :
    SourcePolyTime (constructorCallInput V) (normalizedConstructorOutput V) :=
  TaggedCalls.polynomial _ _ _ _ (source_framed_polynomial _ _ hr)
    (TaggedCalls.polynomial _ _ _ _ (source_framed_polynomial _ _ hc)
      (TaggedCalls.polynomial _ _ _ _ hq
        (TaggedCalls.polynomial _ _ _ _ hd (blockTable_polynomial q))))

def normalizedProofOutput {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1)) :
    ProofCall V → List Bool :=
  TaggedCalls.payload (normalizedConstructorOutput V)
    (TaggedCalls.payload (fun p => frame (List.ofFn (honest p))) honestTableWord)

theorem normalized_proof_polynomial {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (hconstructor : SourcePolyTime (constructorCallInput V) (normalizedConstructorOutput V))
    (hh : SourcePolyTime acceptedSourceWord (fun p => List.ofFn (honest p))) :
    SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest) :=
  TaggedCalls.polynomial _ _ _ _ hconstructor
    (TaggedCalls.polynomial _ _ _ _ (source_framed_polynomial _ _ hh) (honestTable_polynomial q))

end NearCubicGates.Adapters.Proximity
