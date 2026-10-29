import SourceAdapters.Proximity.HonestPreparationCalls
import SourceAdapters.Proximity.HonestDock
import SourceAdapters.Proximity.ConstructorMachine

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": full consumer assembly. The two ordinary
suppliers are explicit parameters of this conditional theorem. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.Published.CW19Proximity
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Adapters.Joins

variable (serializer : SourcePolyTime
  (fun p : List Bool × List Bool × List Bool => frame p.1 ++ frame p.2.1 ++ p.2.2)
  (fun p => natWord p.1.length ++ p.1 ++ frame p.2.2 ++ p.2.1))

include serializer

theorem honest_preparation_of_serializer {q : ℕ}
    (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (a : ℕ) (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 ((sourceCircuitWord S).length + 2))
    (hP : SourcePolyTime (proofCallInput V) (normalizedProofOutput V proofLength honest)) :
    SourcePolyTime acceptedCircuitInputWord (fun p => preparedHonestInput V (sourceAcceptedInput p)) := by
  apply source_composite_polynomial _ _ _ (honest_unordered_polynomial V proofLength honest a hr hP)
  obtain ⟨K, e, ⟨P⟩⟩ := serializer
  exact ⟨K, e, ⟨{
    program := P.program
    realizes := fun p => P.realizes (sourceCircuitWord (sourceCircuit p.1),
      trimAddressWord (clauseTrimRequest V (sourceCircuit p.1)), List.ofFn p.2.val) }⟩⟩

theorem perfect_from_restriction_and_serializer (restriction : HonestRestriction)
    (source : Lemma22Half) : PerfectThreeQueryProximityLiteral := by
  classical
  intro delta hdelta0 hdelta1
  obtain ⟨eta, heta0, heta1, hetadelta⟩ := exists_rational_proximity hdelta0 hdelta1
  obtain ⟨q, V, proofLength, hquery, ⟨a, hr⟩, hrTime, hcTime, hqTime, hdTime,
    hsound, sourceHonest, hcomplete, hhTime⟩ := source eta heta0 heta1
  have hP := normalized_proof_polynomial V proofLength sourceHonest
    (normalized_constructor_polynomial V hrTime hcTime hqTime hdTime) hhTime
  have hprepare := honest_preparation_of_serializer serializer V proofLength sourceHonest a hr hP
  have hhonest := honest_preparation_dock restriction V proofLength sourceHonest a hr hP hprepare
  let s : ℝ := 1 - (1 - (1 / 2 : ℝ)) / predicateBlockSize q
  have hB : 0 < predicateBlockSize q := by unfold predicateBlockSize; positivity
  have hs := block_soundness_range (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hB
  refine ⟨s, hs.1, hs.2, convertedVerifier V,
    target_verifier_computable V proofLength sourceHonest a hr hP,
    ⟨3 * (28 ^ a * predicateBlockSize q), 2 * a, convertedVerifier_size V a hr⟩, ?_, ?_⟩
  · intro C input hfar proof
    have hstrict : StrictlyFar eta (sourceCircuit C) input := source_strict_far (by linarith) hfar
    have hfinite := hsound (sourceCircuit C) input hstrict
    have hall := finite_source_soundness (V (sourceCircuit C)) (hquery (sourceCircuit C)) input (1 / 2) hfinite
    exact trim_soundness (clauseVerifier (V (sourceCircuit C))) input s
      (clauseVerifier_soundness (V (sourceCircuit C)) input (1 / 2) hall) proof
  · exact ⟨convertedHonest V proofLength sourceHonest,
      convertedHonest_complete V proofLength sourceHonest hcomplete, source_to_tm2 _ _ hhonest⟩

end NearCubicGates.Adapters.Proximity
