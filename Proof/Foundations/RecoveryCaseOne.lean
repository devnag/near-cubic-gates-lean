import Proof.Foundations.RecoverySourceContracts
import Proof.Foundations.CaseOnePadding

/-! Immediate and enclosing recovery consumers of the corrected source.
One ordinary hierarchy and one selected PCP supply the canonical Case-1 table.
The later-cutoff-universal AmplifierWitness and legacy executable refuter are
not cast targets. Source construction and final language execution remain
separate from these proved semantic applications. -/
namespace NearCubicWires.RepairSource
open ExecutableInterfaces SourceInterfaces RecoveryPipeline OuterPCPRecovery
open RecoveryScheduleEnvelope ComponentwiseTransfer PhysicalRecovery CaseOnePadding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selectedAmplifier (factory : SourceAmplifierFactory) (d : ℕ) :
    OrdinaryScheduleAmplifier factory.stvExponent d :=
  Classical.choice (factory.forSchedule d)

/-- Canonical accepted table; worst-case hardness follows from the literal
absence of a small accepting oracle for this same PCP. -/
noncomputable def scheduledAmplifierCore
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {c d n : ℕ} (amplifier : ScheduleAmplifier c d)
    (pcp : ProjectionPCP machine timeBound) (input : BitInput n)
    (hq : 1 ≤ pcp.nativeWidth n)
    (complete : ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmall : ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
      circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) →
      ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness) :
    HardCore booleanCircuitFamily := by
  let canonical := Classical.choice (existsCanonicalAcceptingProof pcp input complete)
  let seed := proofFunction pcp canonical.proof
  have hard : WorstCaseHardAt seed (oracleSizeBound d (pcp.nativeWidth n)) := by
    intro circuit hsize
    by_contra hmatches
    have heval : circuit.eval = seed := by
      funext address
      exact not_ne_iff.mp (not_exists.mp hmatches address)
    exact noSmall circuit hsize
      (acceptsOracleCircuit_of_proof pcp input canonical.proof
        canonical.accepts circuit heval)
  let result := amplifier.output (pcp.nativeWidth n) seed
  refine { arity := result.arity
           function := result.function
           size := integerFloorRoot c (oracleSizeBound d (pcp.nativeWidth n))
           advantage := Real.rpow (oracleSizeBound d (pcp.nativeWidth n) : ℝ)
             (-(1 : ℝ) / c)
           hard := ?_ }
  intro candidate hcandidate
  obtain ⟨circuit, hsize, rfl⟩ := hcandidate
  exact amplifier.sound _ seed hq hard circuit hsize

theorem scheduledAmplifierCore_arity
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {c d n : ℕ} (amplifier : ScheduleAmplifier c d)
    (pcp : ProjectionPCP machine timeBound) (input : BitInput n)
    (hq : 1 ≤ pcp.nativeWidth n)
    (complete : ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmall : ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
      circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) →
      ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness) :
    (scheduledAmplifierCore amplifier pcp input hq complete noSmall).arity ≤
      amplifier.arityCoefficient * pcp.nativeWidth n := by
  apply amplifier.arityBound
  exact hq

/-- Preserve the actual canonical small-oracle branch. The Case-1 branch now
contains the core constructed from its schedule-specific amplifier. -/
inductive ScheduledOuterCase
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ} {c d : ℕ}
    (pcp : ProjectionPCP machine timeBound) (amplifier : ScheduleAmplifier c d)
    {n : ℕ} (input : BitInput n) where
  | caseOne :
      (core : HardCore booleanCircuitFamily) →
      core.size = integerFloorRoot c (oracleSizeBound d (pcp.nativeWidth n)) →
      core.advantage = Real.rpow (oracleSizeBound d (pcp.nativeWidth n) : ℝ)
        (-(1 : ℝ) / c) →
      core.arity ≤ amplifier.arityCoefficient * pcp.nativeWidth n →
      ScheduledOuterCase pcp amplifier input
  | caseTwo : CanonicalAcceptingOracle (sizeBound := oracleSizeBound d) pcp input →
      ScheduledOuterCase pcp amplifier input

theorem existsScheduledOuterCase
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ} {c d n : ℕ}
    (pcp : ProjectionPCP machine timeBound) (amplifier : ScheduleAmplifier c d)
    (input : BitInput n) (hq : 1 ≤ pcp.nativeWidth n)
    (complete : ∃ proof, ∀ randomness, pcp.accepts input proof randomness) :
    Nonempty (ScheduledOuterCase pcp amplifier input) := by
  classical
  by_cases hsmall : ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
      circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) ∧
        ∀ randomness, acceptsOracleCircuit pcp input circuit randomness
  · exact ⟨.caseTwo (Classical.choice (existsCanonicalAcceptingOracle pcp input hsmall))⟩
  · have noSmall : ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) →
        ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness := by
      intro circuit hsize accepts
      exact hsmall ⟨circuit, hsize, accepts⟩
    exact ⟨.caseOne (scheduledAmplifierCore amplifier pcp input hq complete noSmall)
      rfl rfl (scheduledAmplifierCore_arity amplifier pcp input hq complete noSmall)⟩

/-- Enclosing application: refuter conflict, same-language PCP completeness,
and canonical recovery split, with the amplifier selected only after d. -/
theorem ordinaryRefuterScheduledRecovery
    {T : ℕ → ℕ} (source : JointOrdinarySource T) (degrees : PCPDegrees)
    (outer : ChangedHierarchyOuterPCP source degrees)
    (machine : OrdinaryWeakMachine) (littleO : OrdinaryLittleO machine T)
    (oneSided : ∀ n x, machine.accepts n x →
      source.hierarchy.timedView.accepts n x = true)
    (factory : SourceAmplifierFactory) (d : ℕ) :
    ∃ onset, ∀ n, onset ≤ n → 1 ≤ outer.result.pcp.nativeWidth n →
      Nonempty (ScheduledOuterCase outer.result.pcp
        (selectedAmplifier factory d).toScheduleAmplifier (source.refuter.output machine n)) := by
  obtain ⟨onset, ready⟩ := actualRefuterPCPRecoveryJoin source degrees outer
    machine littleO oneSided
  refine ⟨onset, ?_⟩
  intro n hn hq
  exact existsScheduledOuterCase outer.result.pcp
    (selectedAmplifier factory d).toScheduleAmplifier
    (source.refuter.output machine n) hq (ready n hn).2

/-- The table is padded semantically by ignored variables, preserving both
hardness parameters. This is the existing physical consumer's actual core. -/
noncomputable def padAmplifierCore (core : HardCore booleanCircuitFamily)
    (target : ℕ) (hcore : core.arity ≤ target) : HardCore booleanCircuitFamily where
  arity := target
  function := padCore core.function hcore
  size := core.size
  advantage := core.advantage
  hard := averageHard_padCore (family := booleanCircuitFamily) (size := core.size)
    booleanCircuitFamily_restrictionClosed core.hard hcore

noncomputable def amplifierPhysicalConsumer
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily) (target : ℕ)
    (hcore : core.arity ≤ target) (symCap thrCap : ℕ)
    (hsym : 40 * (target + symCap + 2) ^ 4 ≤ core.size)
    (hthr : 50 * (target + thrCap + 2) ^ 4 ≤ core.size) :=
  commonPhysicalCoreOfBoolean normalization (padAmplifierCore core target hcore)
    symCap thrCap hsym hthr

/-- Exact selected source instance at the recovery proof-budget currency. -/
theorem selectedAmplifier_constructorBudget (factory : SourceAmplifierFactory)
    (d q proofBudget : ℕ) (hq : 1 ≤ q) (hproof : 2 ^ q ≤ proofBudget) :
    2 ^ ((selectedAmplifier factory d).constructionExponent * max 1 q) ≤
      proofBudget ^ (selectedAmplifier factory d).constructionExponent :=
  amplifier_construction_budget_at_consumer _ q proofBudget hq hproof

end NearCubicWires.RepairSource
