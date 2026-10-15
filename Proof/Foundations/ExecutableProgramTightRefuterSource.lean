import Proof.Foundations.ExecutableProgramTimedSource

/-!
# Certified-tight refuter source over an executable hierarchy program

This module combines two fidelity corrections: verifier time is bounded above
by a literal interpreter receipt, and the refuter's hierarchy language/time
pair is derived from one `ExecutableLanguageProgram`.
-/

namespace NearCubicWires.ExecutableProgramTightRefuterSource

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.SourceInterfaces

/-- Request-indexed resources for the exact verifier program.  The advertised
semantic charge dominates both resources used by the literal halting receipt. -/
structure ReceiptBackedTightVerifierBudget
    (machine : ExecutableWeakNondeterministicMachine) where
  fuel : WeakVerifierRequest → ℕ
  registerBits : WeakVerifierRequest → ℕ
  advertisedSteps : WeakVerifierRequest → ℕ
  fuelPositive : ∀ request, 0 < fuel request
  registerBitsPositive : ∀ request, 0 < registerBits request
  fuel_le_advertisedSteps : ∀ request, fuel request ≤ advertisedSteps request
  registerBits_le_advertisedSteps : ∀ request,
    registerBits request ≤ advertisedSteps request
  initialBitsFit : ∀ request,
    natBitLength (max request.length request.code) ≤ registerBits request
  halts : ∀ request,
    runNPOracleProgram machine.verifier.program (registerBits request)
        (fuel request)
        (initialNPOracleState request.length request.code) =
      some (machine.verifier.execute request)

structure ReceiptBackedTightWeakMachine where
  legacy : ExecutableWeakNondeterministicMachine
  receipt : ReceiptBackedTightVerifierBudget legacy

def ReceiptBackedTightWeakMachine.witnessBits
    (machine : ReceiptBackedTightWeakMachine) (n : ℕ) : ℕ :=
  machine.legacy.witnessBits n

def ReceiptBackedTightWeakMachine.verifierRequest
    (machine : ReceiptBackedTightWeakMachine) {n : ℕ}
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    WeakVerifierRequest :=
  machine.legacy.verifierRequest input witness

def ReceiptBackedTightWeakMachine.execute
    (machine : ReceiptBackedTightWeakMachine)
    (request : WeakVerifierRequest) : ℕ :=
  (runNPOracleProgram machine.legacy.verifier.program
      (machine.receipt.registerBits request) (machine.receipt.fuel request)
      (initialNPOracleState request.length request.code)).getD 0

theorem ReceiptBackedTightWeakMachine.execute_eq_legacy
    (machine : ReceiptBackedTightWeakMachine)
    (request : WeakVerifierRequest) :
    machine.execute request = machine.legacy.verifier.execute request := by
  simp [ReceiptBackedTightWeakMachine.execute, machine.receipt.halts request]

def ReceiptBackedTightWeakMachine.run
    (machine : ReceiptBackedTightWeakMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) : Bool :=
  machine.execute (machine.verifierRequest input witness) != 0

def ReceiptBackedTightWeakMachine.toSemantic
    (machine : ReceiptBackedTightWeakMachine) : WeakNondeterministicMachine where
  witnessBits := machine.witnessBits
  run := machine.run
  steps := fun _n input witness =>
    machine.receipt.advertisedSteps (machine.verifierRequest input witness)

theorem ReceiptBackedTightWeakMachine.run_eq_legacy
    (machine : ReceiptBackedTightWeakMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    machine.run n input witness = machine.legacy.run n input witness := by
  simp only [ReceiptBackedTightWeakMachine.run,
    ExecutableWeakNondeterministicMachine.run]
  rw [machine.execute_eq_legacy]
  rfl

theorem ReceiptBackedTightWeakMachine.accepts_iff_legacy
    (machine : ReceiptBackedTightWeakMachine) {n : ℕ}
    (input : BitInput n) :
    machine.toSemantic.accepts input ↔ machine.legacy.toSemantic.accepts input := by
  constructor
  · rintro ⟨witness, hwitness⟩
    refine ⟨witness, ?_⟩
    change machine.run n input witness = true at hwitness
    change machine.legacy.run n input witness = true
    rw [← machine.run_eq_legacy]
    exact hwitness
  · rintro ⟨witness, hwitness⟩
    refine ⟨witness, ?_⟩
    change machine.legacy.run n input witness = true at hwitness
    change machine.run n input witness = true
    rw [machine.run_eq_legacy]
    exact hwitness

/-- Coarse legacy programs embed without changing their semantics.  This is
used only to derive the compatibility projection; genuinely tight consumers
use an independently constructed receipt. -/
def ReceiptBackedTightWeakMachine.ofLegacy
    (machine : ExecutableWeakNondeterministicMachine) :
    ReceiptBackedTightWeakMachine where
  legacy := machine
  receipt := {
    fuel := machine.verifier.budget
    registerBits := machine.verifier.budget
    advertisedSteps := machine.verifier.budget
    fuelPositive := by
      intro request
      exact machine.verifier.budget_pos request
    registerBitsPositive := by
      intro request
      exact machine.verifier.budget_pos request
    fuel_le_advertisedSteps := fun _ => le_rfl
    registerBits_le_advertisedSteps := fun _ => le_rfl
    initialBitsFit := machine.verifier.initialBitsFit
    halts := machine.verifier.run_eq_execute }

@[simp] theorem ReceiptBackedTightWeakMachine.ofLegacy_witnessBits
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) :
    (ReceiptBackedTightWeakMachine.ofLegacy machine).witnessBits n =
      machine.witnessBits n :=
  rfl

@[simp] theorem ReceiptBackedTightWeakMachine.ofLegacy_steps
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    (ReceiptBackedTightWeakMachine.ofLegacy machine).toSemantic.steps
        n input witness = machine.toSemantic.steps n input witness :=
  rfl

/-- Faithful replacement for the tight source prototype: both the hierarchy
and each tested weak-machine runtime have executable provenance. -/
structure CertifiedTightExecutableProgramRefuterSource (bound : ℕ → ℕ) where
  hierarchyProgram : ExecutableLanguageProgram
  hierarchySteps : ∀ n input,
    programSteps hierarchyProgram n input ≤ bound n
  refuter : ExecutableSATOracleRefuter hierarchyProgram.language bound
  soundTight : ∀ machine : ReceiptBackedTightWeakMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine.legacy n) ↔
        hierarchyProgram.language n
          (refuter.output machine.legacy n) = false)

theorem CertifiedTightExecutableProgramRefuterSource.soundLegacy
    {bound : ℕ → ℕ}
    (source : CertifiedTightExecutableProgramRefuterSource bound)
    (machine : ExecutableWeakNondeterministicMachine)
    (hruntime : RunsInLittleO machine.toSemantic bound)
    (hwitness : ∀ n, machine.witnessBits n ≤ n / 10) :
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (source.refuter.output machine n) ↔
        source.hierarchyProgram.language n
          (source.refuter.output machine n) = false) := by
  let tight := ReceiptBackedTightWeakMachine.ofLegacy machine
  have htightRuntime : RunsInLittleO tight.toSemantic bound := by
    intro multiplier hmultiplier
    rcases hruntime multiplier hmultiplier with ⟨onset, hruntime⟩
    refine ⟨onset, ?_⟩
    intro n hn input witness
    simpa [tight, ReceiptBackedTightWeakMachine.toSemantic,
      ReceiptBackedTightWeakMachine.verifierRequest,
      ReceiptBackedTightWeakMachine.ofLegacy,
      ExecutableWeakNondeterministicMachine.toSemantic,
      ExecutableWeakNondeterministicMachine.verifierRequest,
      ExecutableWeakNondeterministicMachine.verifierBudget,
      QuotientNatProgram.budget, WeakVerifierRequest.measure] using
        hruntime n hn input witness
  have htightWitness : ∀ n, tight.witnessBits n ≤ n / 10 := by
    simpa [tight] using hwitness
  rcases source.soundTight tight htightRuntime htightWitness with
    ⟨onset, hsound⟩
  refine ⟨onset, ?_⟩
  intro n hn
  have hpoint := hsound n hn
  change
    (tight.toSemantic.accepts (source.refuter.output machine n) ↔
      source.hierarchyProgram.language n
        (source.refuter.output machine n) = false) at hpoint
  exact (tight.accepts_iff_legacy
    (source.refuter.output machine n)).symm.trans hpoint

/-- Compatibility projection to the honest program-backed non-tight source. -/
def CertifiedTightExecutableProgramRefuterSource.toProgramSource
    {bound : ℕ → ℕ}
    (source : CertifiedTightExecutableProgramRefuterSource bound) :
    ExecutableProgramRefuterSource bound where
  hierarchyProgram := source.hierarchyProgram
  hierarchySteps := source.hierarchySteps
  refuter := source.refuter
  sound := source.soundLegacy

/-- Final compatibility projection for the existing recovery cone.  The
legacy `TimedDecisionMachine` is still definitionally program-derived. -/
def CertifiedTightExecutableProgramRefuterSource.toLegacy
    {bound : ℕ → ℕ}
    (source : CertifiedTightExecutableProgramRefuterSource bound) :
    ExecutableRefuterSource bound :=
  source.toProgramSource.toLegacy

def CertifiedTightExecutableProgramRefuterContract : Prop :=
  ∀ (bound : ℕ → ℕ), RefuterClockAdmissible bound →
    Nonempty (CertifiedTightExecutableProgramRefuterSource bound)

/-- Exact corrected type of the published refuter/XOR field. -/
def CertifiedTightExecutableProgramRefuterAndXorContract : Prop :=
  CertifiedTightExecutableProgramRefuterContract ∧ XorContract

theorem certifiedTightProgramRefuterContract_implies_programContract
    (contract : CertifiedTightExecutableProgramRefuterContract) :
    ExecutableProgramRefuterContract := by
  intro bound admissible
  rcases contract bound admissible with ⟨source⟩
  exact ⟨source.toProgramSource⟩

theorem certifiedTightProgramRefuterContract_implies_legacy
    (contract : CertifiedTightExecutableProgramRefuterContract) :
    ExecutableRefuterContract := by
  intro bound admissible
  rcases contract bound admissible with ⟨source⟩
  exact ⟨source.toLegacy⟩

theorem certifiedTightProgramRefuterAndXor_implies_legacy
    (contract : CertifiedTightExecutableProgramRefuterAndXorContract) :
    ExecutableRefuterAndXorContract :=
  ⟨certifiedTightProgramRefuterContract_implies_legacy contract.1,
    contract.2⟩

end NearCubicWires.ExecutableProgramTightRefuterSource
