import Proof.Foundations.SourceCore

/-! The full printed BV1.1 / CLW3.10 witness on an ordinary verifier.
Arity may depend on the actual input. Length-only padding, duplicate-clause
compaction and conversion to the enclosing PCP codec are LOCAL operations.
The imported witness retains its one actual ordinary construction algorithm.
There is no separated-degree factory over later hierarchy machines. -/
namespace NearCubicWires.RepairSource
open SourceInterfaces ExecutableInterfaces LocalBitMultitape CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure RawProjectionPCP where
  width : ℕ
  queries : ℕ
  queryBits : Fin queries → Fin width → ProjectedRandomBit width
  decision : ThreeCNF queries

def RawProjectionPCP.accepts (p : RawProjectionPCP)
    (proof : BitInput (2 ^ p.width)) (randomness : BitInput p.width) : Bool :=
  p.decision.eval fun j => proof (binaryAddress fun i => (p.queryBits j i).eval randomness)

noncomputable def RawProjectionPCP.acceptanceFraction (p : RawProjectionPCP)
    (proof : BitInput (2 ^ p.width)) : ℝ :=
  ((Finset.univ.filter fun r => p.accepts proof r).card : ℝ) /
    (Fintype.card (BitInput p.width) : ℝ)

/-- Ordinary explicit circuit description. Framing is linear in the listed
fields; unlike the legacy compact word, this format does not promise free
random access to a projection or clause. -/
def RawProjectionPCP.word (p : RawProjectionPCP) : List Bool :=
  frame p.width.bits ++ frame p.queries.bits ++
  (List.ofFn fun j : Fin p.queries =>
    (List.ofFn fun i : Fin p.width => frame (projectionCode (p.queryBits j i)).bits).flatten).flatten ++
  frame p.decision.clauses.length.bits ++
  (p.decision.clauses.map fun clause =>
    (List.ofFn fun i : Fin 3 => frame (literalCode (clause i)).bits).flatten).flatten

structure ProjectionSourceAlgorithm (verifier : OrdinaryVerifier) (T : ℕ → ℕ) where
  output : InputRequest → RawProjectionPCP
  degrees : PCPDegrees
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  constructor : OrdinaryWordFunction InputRequest
    (fun r => frame (List.ofFn r.2) ++ frame (T r.1).bits)
    (fun r => (output r).word)
    (fun r => coefficient * (r.1 + natBitLength (T r.1) + 1) ^ degrees.construction)
  proofBound : ∀ r : InputRequest, 1 ≤ r.1 →
    2 ^ (output r).width ≤ coefficient * T r.1 * logScale (T r.1) ^ degrees.proofLog
  queryBound : ∀ r : InputRequest, 1 ≤ r.1 →
    (output r).queries ≤ coefficient * ((output r).width + 1) ^ degrees.queries
  complete : ∀ r : InputRequest, 1 ≤ r.1 → verifier.language T r.1 r.2 →
    ∃ proof, ∀ randomness, (output r).accepts proof randomness = true
  sound : ∀ r : InputRequest, 1 ≤ r.1 → ¬verifier.language T r.1 r.2 →
    ∀ proof, (output r).acceptanceFraction proof ≤ 1 / (r.1 : ℝ) ^ 10

/-- The unrestricted printed T≥n domain is essential for the fixed-U route.
The binary value T(n) is supplied to the succinct constructor. No polynomial
upper bound on T and no SAT-oracle verifier are inserted into this source. -/
def ProjectionPCPSource : Prop :=
  ∀ (verifier : OrdinaryVerifier) (T : ℕ → ℕ),
    (∀ n, n ≤ T n) →
    (∀ n (x : BitInput n) (w : BitInput (T n)),
      ∃ receipt, run verifier.machine (T n)
        (verifier.inputTapes (List.ofFn x) (List.ofFn w)) = some receipt) →
    Nonempty (ProjectionSourceAlgorithm verifier T)

/-- Immediate source application: this is the actual returned constructor's
receipt and literal output, before any paid local normalization. -/
theorem projection_source_call {v : OrdinaryVerifier} {T : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v T) (r : InputRequest) :
    ∃ receipt, run source.constructor.program.machine
      (source.coefficient * (r.1 + natBitLength (T r.1) + 1) ^ source.degrees.construction)
      (source.constructor.program.inputTapes
        (frame (List.ofFn r.2) ++ frame (T r.1).bits)) = some receipt ∧
      receipt.final.tapes source.constructor.program.outputTape = (source.output r).word :=
  source.constructor.realizes r

/-- The same source witness supplies completeness after the actual hierarchy
input is encoded. The language equation is a local U/padding obligation. -/
theorem projection_padded_complete {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest)
    (positive : ∀ r, 1 ≤ (encode r).1)
    (language : ∀ r, H.verifier.language H.time r.1 r.2 ↔
      v.language U (encode r).1 (encode r).2)
    (r : InputRequest) (accepts : H.timedView.accepts r.1 r.2 = true) :
    ∃ proof, ∀ randomness, (source.output (encode r)).accepts proof randomness = true :=
  source.complete (encode r) (positive r)
    ((language r).mp ((hierarchy_language_exact H r.1 r.2).mp accepts))

/-- Source soundness transports with its literal padded length. The local
length slice, rather than a stronger imported soundness field, pays n+1. -/
theorem projection_padded_sound {v : OrdinaryVerifier} {T U : ℕ → ℕ}
    (source : ProjectionSourceAlgorithm v U) (H : OrdinaryHierarchy T)
    (encode : InputRequest → InputRequest)
    (length : ∀ r, r.1 + 1 ≤ (encode r).1)
    (language : ∀ r, H.verifier.language H.time r.1 r.2 ↔
      v.language U (encode r).1 (encode r).2)
    (r : InputRequest) (rejects : H.timedView.accepts r.1 r.2 = false)
    (proof : BitInput (2 ^ (source.output (encode r)).width)) :
    (source.output (encode r)).acceptanceFraction proof ≤ 1 / ((r.1 + 1 : ℕ) : ℝ) ^ 10 := by
  have positive : 1 ≤ (encode r).1 := by have := length r; omega
  have reject : ¬v.language U (encode r).1 (encode r).2 := by
    intro yes
    have h := (hierarchy_language_exact H r.1 r.2).mpr ((language r).mpr yes)
    simp [rejects] at h
  refine (source.sound (encode r) positive reject proof).trans ?_
  have hpos : (0 : ℝ) < ((r.1 + 1 : ℕ) : ℝ) ^ 10 := by positivity
  apply one_div_le_one_div_of_le hpos
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast length r) _

end NearCubicWires.RepairSource
