import SourceAdapters.Proximity.TaggedPolynomial
import SourceAdapters.Proximity.TableCompilers
import SourceAdapters.Proximity.SourceCalls

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the single ordinary callee used by the construction
and honest-proof loops. Every branch has an actual source or finite-table
program; dependent source request domains and promises are retained exactly. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

abbrev ConstructorCall {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  SourceCircuit ⊕ (CoinRequest V ⊕ (QueryRequest V ⊕ (DecisionRequest V ⊕ BitInput (2 ^ q))))

def constructorCallInput {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :
    ConstructorCall V → List Bool :=
  TaggedCalls.input sourceCircuitWord (TaggedCalls.input coinRequestWord
    (TaggedCalls.input queryRequestWord (TaggedCalls.input decisionRequestWord List.ofFn)))

def constructorCallOutput {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :
    ConstructorCall V → List Bool :=
  TaggedCalls.payload (fun C => (V C).randomBits.bits)
    (TaggedCalls.payload (fun p => ((V p.1).queryCount p.2).bits)
      (TaggedCalls.payload (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2))
        (TaggedCalls.payload (fun p => [(V p.1).decision p.2.1 p.2.2]) blockTableWord)))

theorem constructor_call_polynomial {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (hr : SourcePolyTime sourceCircuitWord (fun C => (V C).randomBits.bits))
    (hc : SourcePolyTime (coinRequestWord (V := V)) (fun p => ((V p.1).queryCount p.2).bits))
    (hq : SourcePolyTime (queryRequestWord (V := V))
      (fun p => queryAddressWord ((V p.1).query p.2.1 p.2.2)))
    (hd : SourcePolyTime (decisionRequestWord (V := V)) (fun p => [(V p.1).decision p.2.1 p.2.2])) :
    SourcePolyTime (constructorCallInput V) (constructorCallOutput V) :=
  TaggedCalls.polynomial _ _ _ _ hr (TaggedCalls.polynomial _ _ _ _ hc
    (TaggedCalls.polynomial _ _ _ _ hq (TaggedCalls.polynomial _ _ _ _ hd (blockTable_polynomial q))))

abbrev ProofCall {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :=
  ConstructorCall V ⊕ (AcceptedSourceInput ⊕ BitInput (2 ^ q + q))

def proofCallInput {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) :
    ProofCall V → List Bool :=
  TaggedCalls.input (constructorCallInput V) (TaggedCalls.input acceptedSourceWord List.ofFn)

def proofCallOutput {q : ℕ} (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1)) :
    ProofCall V → List Bool :=
  TaggedCalls.payload (constructorCallOutput V)
    (TaggedCalls.payload (fun p => List.ofFn (honest p)) honestTableWord)

theorem proof_call_polynomial (hX8 : CappedWordRun) {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (hconstructor : SourcePolyTime (constructorCallInput V) (constructorCallOutput V))
    (hh : SourcePolyTime acceptedSourceWord (fun p => List.ofFn (honest p))) :
    SourcePolyTime (proofCallInput V) (fun p => frame (proofCallOutput V proofLength honest p)) :=
  source_framed_polytime hX8 _ _
    (TaggedCalls.polynomial _ _ _ _ hconstructor (TaggedCalls.polynomial _ _ _ _ hh (honestTable_polynomial q)))

end NearCubicGates.Adapters.Proximity
