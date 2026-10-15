import Proof.Foundations.OuterPCPRecovery

/-! Pull back one selected source PCP along a length-indexed input encoding.
This keeps its exact random bits, proof addresses and decision predicates.
It is a semantic transport into the production outer-case consumer, not an
ordinary implementation of the encoding or a uniform PCP source factory.
The inherited constructionSteps field counts only the source construction;
the ordinary constructor must separately pay for producing the encoded input.
-/
namespace NearCubicWires.RepairOrdinary.PCPTransport
open SourceInterfaces OuterPCPRecovery RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pullback {sourceMachine : TimedDecisionMachine} {sourceTime : ℕ → ℕ}
    (pcp : ProjectionPCP sourceMachine sourceTime)
    (targetMachine : TimedDecisionMachine) (targetTime length : ℕ → ℕ)
    (encode : {n : ℕ} → BitInput n → BitInput (length n)) :
    ProjectionPCP targetMachine targetTime where
  nativeWidth n := pcp.nativeWidth (length n)
  queryCount n := pcp.queryCount (length n)
  queryAddressBits input := pcp.queryAddressBits (encode input)
  decision input := pcp.decision (encode input)
  constructionSteps n := pcp.constructionSteps (length n)

variable {sourceMachine targetMachine : TimedDecisionMachine}
  {sourceTime targetTime length : ℕ → ℕ}
  (pcp : ProjectionPCP sourceMachine sourceTime)
  (encode : {n : ℕ} → BitInput n → BitInput (length n))

@[simp] theorem accepts_eq {n : ℕ} (input : BitInput n) (proof randomness) :
    (pullback pcp targetMachine targetTime length encode).accepts input proof randomness =
      pcp.accepts (encode input) proof randomness := rfl

@[simp] theorem fraction_eq {n : ℕ} (input : BitInput n) (proof) :
    (pullback pcp targetMachine targetTime length encode).acceptanceFraction input proof =
      pcp.acceptanceFraction (encode input) proof := rfl

theorem complete
    (language : ∀ n (x : BitInput n),
      targetMachine.accepts n x = sourceMachine.accepts (length n) (encode x))
    (sourceComplete : ∀ n (x : BitInput n), sourceMachine.accepts n x = true →
      ∃ proof, ∀ randomness, pcp.accepts x proof randomness = true)
    {n : ℕ} (x : BitInput n) (hyes : targetMachine.accepts n x = true) :
    ∃ proof, ∀ randomness,
      (pullback pcp targetMachine targetTime length encode).accepts x proof randomness = true :=
  sourceComplete (length n) (encode x) ((language n x).symm.trans hyes)

/-- The source's N^-10 error implies the production (n+1)^-10 error.
No new proof table or random-string averaging is introduced by this transport. -/
theorem sound
    (language : ∀ n (x : BitInput n),
      targetMachine.accepts n x = sourceMachine.accepts (length n) (encode x))
    (sourceSound : ∀ n, 1 ≤ n → ∀ (x : BitInput n),
      sourceMachine.accepts n x = false → ∀ proof,
        pcp.acceptanceFraction x proof ≤ 1 / (n : ℝ)^10)
    (lengthBound : ∀ n, n+1 ≤ length n)
    {n : ℕ} (x : BitInput n) (hno : targetMachine.accepts n x = false) (proof) :
    (pullback pcp targetMachine targetTime length encode).acceptanceFraction x proof ≤
      1 / ((n+1 : ℕ) : ℝ)^10 := by
  rw [fraction_eq]
  apply (sourceSound (length n) (by have := lengthBound n; omega)
    (encode x) ((language n x).symm.trans hno) proof).trans
  have hpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ)^10 := by positivity
  apply one_div_le_one_div_of_le hpos
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast lengthBound n) 10

/-- The exact production Case-1/Case-2 split needs this one transported PCP.
Neither a source factory over all clocks nor a deterministic decider for the
nondeterministic hierarchy is a premise of this semantic application. -/
theorem outerCase
    (language : ∀ n (x : BitInput n),
      targetMachine.accepts n x = sourceMachine.accepts (length n) (encode x))
    (sourceComplete : ∀ n (x : BitInput n), sourceMachine.accepts n x = true →
      ∃ proof, ∀ randomness, pcp.accepts x proof randomness = true)
    {sizeBound : ℕ → ℕ} (amplifier : AmplifierWitness)
    (constructible : TimeConstructible sizeBound)
    {n : ℕ} (x : BitInput n) (hyes : targetMachine.accepts n x = true) :
    Nonempty (OuterOracleCase (sizeBound := sizeBound)
      (pullback pcp targetMachine targetTime length encode) amplifier x) :=
  existsOuterOracleCase _ amplifier constructible x
    (complete pcp encode language sourceComplete x hyes)

end NearCubicWires.RepairOrdinary.PCPTransport
