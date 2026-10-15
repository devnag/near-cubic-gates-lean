import Proof.PCP.ProjectionCompaction
import Proof.Foundations.SourceRegistry

/-! The exact P2 enclosing supplier. Its program runs from the hierarchy input
and binary clock to the literal normalized output, including padding, the ONE
selected source call and all local conversion. All fields here are LOCAL proof
obligations. None belongs to EightSources. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev normalizedSourcePCP {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (source.output (encode r)).queries ≤ Q r.1) :=
  compactProjectionPCP (normalizeProjectionPCP (machine := H.timedView) (T := H.time)
    (source.output ∘ encode) R Q hr hq)

structure NormalizedPCPRun {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (source.output (encode r)).queries ≤ Q r.1)
    (inputExponent : ℕ) where
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  logTimeExponent : ℕ
  queryExponent : ℕ
  proofExponent : ℕ
  length : ∀ r, r.1+1 ≤ (encode r).1
  language : ∀ r, H.verifier.language H.time r.1 r.2 ↔
    v.language U (encode r).1 (encode r).2
  proofBound : ∀ n, 1 ≤ n →
    2 ^ R n ≤ coefficient * H.time n * logScale (H.time n) ^ proofExponent
  queryBound : ∀ n, Q n ≤ coefficient * (R n + 1) ^ queryExponent
  constructor : OrdinaryWordFunction InputRequest
    (fun r => frame (List.ofFn r.2) ++ frame (H.time r.1).bits)
    (fun r => pcpWord (normalizedSourcePCP source H encode R Q hr hq) r.2)
    (fun r => coefficient * (r.1+1)^inputExponent *
      (natBitLength (H.time r.1)+1)^logTimeExponent)

theorem separated_le_coarse (C n b a d : ℕ) :
    C * (n+1)^a * (b+1)^d ≤ C * (n+b+1)^(a+d) := by
  calc
    _ ≤ C * (n+b+1)^a * (n+b+1)^d := by gcongr <;> omega
    _ = _ := by rw [pow_add]; ring

/-- Local actual constructor plus the checked source semantics inhabit the
literal separated result consumed by the same hierarchy/refuter/recovery. -/
noncomputable def separated_of_normalizedRun {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (source.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (source.output (encode r)).queries ≤ Q r.1)
    (a : ℕ) (realization : NormalizedPCPRun source H encode R Q hr hq a) :
    SeparatedPCPResult H a where
  degrees := ⟨a + realization.logTimeExponent, realization.queryExponent, realization.proofExponent⟩
  data :=
    { pcp := normalizedSourcePCP source H encode R Q hr hq
      coefficient := realization.coefficient
      coefficientPositive := realization.coefficientPositive
      proofBound := realization.proofBound
      queryBound := realization.queryBound
      decisionIndependent := fun n x r s =>
        congrArg compactThreeCNF (normalizeProjectionPCP_independent _ R Q hr hq ⟨n,x⟩ r s)
      constructor := realization.constructor.enlargeBudget (fun r =>
        separated_le_coarse _ _ _ _ _)
      complete := by
        intro n x yes
        obtain ⟨proof, complete⟩ := normalized_source_complete source H encode R Q hr hq
          (fun r => by have := realization.length r; omega) realization.language ⟨n,x⟩ yes
        exact ⟨proof, fun randomness => (compactProjectionPCP_accepts _ _ _ _).trans (complete randomness)⟩
      sound := by
        intro n hn x no proof
        change (compactProjectionPCP _).acceptanceFraction x proof ≤ _
        rw [compactProjectionPCP_fraction]
        have h := normalized_source_sound source H encode R Q hr hq
          realization.length realization.language ⟨n,x⟩ no proof
        refine h.trans ?_
        apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ)^10)
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ n) _ }
  coefficient := realization.coefficient
  coefficientPositive := realization.coefficientPositive
  logTimeExponent := realization.logTimeExponent
  fineConstructor := realization.constructor

/-- The ultimate changed PCP consumer has no factory argument: it receives
the result of this actual single-source transport. -/
noncomputable def outer_of_normalizedRun {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (pcpSource : ProjectionSourceAlgorithm v U) (source : JointOrdinarySource T)
    (encode : InputRequest → InputRequest) (R Q : ℕ → ℕ)
    (hr : ∀ r : InputRequest, (pcpSource.output (encode r)).width ≤ R r.1)
    (hq : ∀ r : InputRequest, (pcpSource.output (encode r)).queries ≤ Q r.1)
    (a : ℕ) (realization : NormalizedPCPRun pcpSource source.hierarchy encode R Q hr hq a) :
    ChangedHierarchyOuterPCP source
      (separated_of_normalizedRun pcpSource source.hierarchy encode R Q hr hq a realization).degrees :=
  ⟨(separated_of_normalizedRun pcpSource source.hierarchy encode R Q hr hq a realization).data⟩

end NearCubicWires.RepairSource
