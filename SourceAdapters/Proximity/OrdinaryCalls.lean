import SourceAdapters.Proximity.TargetCodec
import SourceAdapters.Proximity.VerifierCalls
import SourceAdapters.Machine.CappedWordProof

/-! Q04: discharge the shared exact raw-output framing interface with its
proved ordinary implementation. All exports here have no X8 hypothesis. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.Published.CW19Proximity

theorem target_source_polynomial :
    SourcePolyTime Circuit.word (fun C => sourceCircuitWord (sourceCircuit C)) :=
  target_source_polytime Machine.Capped.cappedWordRun

theorem source_framed_polynomial {Request : Type} (input output : Request → List Bool)
    (source : SourcePolyTime input output) : SourcePolyTime input (fun r => frame (output r)) :=
  source_framed_polytime Machine.Capped.cappedWordRun input output source

theorem source_composite_polynomial {Request : Type} (input middle output : Request → List Bool)
    (first : SourcePolyTime input middle) (second : SourcePolyTime middle output) :
    SourcePolyTime input output := source_polytime_comp Machine.Capped.cappedWordRun input middle output first second

theorem proof_call_framed_polynomial {q : ℕ}
    (V : (C : SourceCircuit) → NonadaptiveVerifier C.arity q) (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (hconstructor : SourcePolyTime (constructorCallInput V) (constructorCallOutput V))
    (hh : SourcePolyTime acceptedSourceWord (fun p => List.ofFn (honest p))) :
    SourcePolyTime (proofCallInput V) (fun p => frame (proofCallOutput V proofLength honest p)) :=
  proof_call_polynomial Machine.Capped.cappedWordRun V proofLength honest hconstructor hh

end NearCubicGates.Adapters.Proximity
