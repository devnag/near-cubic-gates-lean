import Proof.Circuits.BoundedOracleStructuralFormulaAtomSchedule
import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.MachineModel.CircuitInputFormulaPrefixSATProgram
import Proof.MachineModel.TaggedToBalancedPreservingProgram

/-!
# Bounded-oracle structural formula suffix

This is the sole post-emitter path.  The emitter's exact heterogeneous atom
schedule is consumed by the shared balanced clause fold and raw-clause
prefix-SAT reducer; no circuit code, formula callback, or alternate CNF
builder is introduced here.
-/

namespace NearCubicWires.BoundedOracleStructuralFormulaPrefixSATProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputFormulaPrefixSATProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedToBalancedPreservingProgram
open NearCubicWires.VerifiedLinker

/-- Fixed suffix shared by every published projection PCP. -/
abbrev boundedOracleStructuralFormulaPrefixSATProgram : NPOracleProgram :=
  circuitInputFormulaPrefixSATProgram

def boundedOracleStructuralFormulaPrefixInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList
      (boundedOracleStructuralFormulaAtoms pcp input bound))
    (encodeUnary count)

def boundedOracleStructuralFormulaPrefixFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count : ℕ) : ℕ :=
  circuitInputFormulaPrefixSATFuel
    (boundedOracleVerifierCircuit pcp input bound) count

def boundedOracleStructuralFormulaPrefixMaximumBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count inputLength : ℕ) : ℕ :=
  circuitInputFormulaPrefixSATMaximumBits inputLength
    (boundedOracleVerifierCircuit pcp input bound) count

theorem boundedOracleStructuralFormulaPrefixSATProgram_containsSAT :
    containsSAT boundedOracleStructuralFormulaPrefixSATProgram = true :=
  circuitInputFormulaPrefixSATProgram_containsSAT

/-- Exact suffix refinement from the canonical structural atom target. -/
theorem run_boundedOracleStructuralFormulaPrefixSATProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count inputLength : ℕ) :
    runNPOracleProgram boundedOracleStructuralFormulaPrefixSATProgram
        (boundedOracleStructuralFormulaPrefixMaximumBits
          pcp input bound count inputLength)
        (boundedOracleStructuralFormulaPrefixFuel
          pcp input bound count)
        (initialNPOracleState inputLength
          (boundedOracleStructuralFormulaPrefixInput
            pcp input bound count)) =
      some
        (prefixSATOutput count <|
          boundedOracleRecoveryFormula pcp input bound) := by
  simpa only [boundedOracleStructuralFormulaPrefixSATProgram,
    boundedOracleStructuralFormulaPrefixMaximumBits,
    boundedOracleStructuralFormulaPrefixFuel,
    boundedOracleStructuralFormulaPrefixInput,
    countedCircuitInputFormulaBalancedFoldInput,
    boundedOracleStructuralFormulaAtoms_eq,
    boundedOracleRecoveryFormula] using
      run_circuitInputFormulaPrefixSATProgram inputLength
        (boundedOracleVerifierCircuit pcp input bound) count

/-- On a legal accepting oracle, the same executable suffix returns the exact
canonical description coordinate used by C.12 recovery. -/
theorem run_boundedOracleStructuralFormulaPrefixSATProgram_eq_canonical
    {machine : TimedDecisionMachine}
    {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (canonical :
      CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input)
    (target :
      Fin (descriptionWidth (pcp.nativeWidth n)
        (sizeBound (pcp.nativeWidth n))))
    (inputLength : ℕ) :
    runNPOracleProgram boundedOracleStructuralFormulaPrefixSATProgram
        (boundedOracleStructuralFormulaPrefixMaximumBits pcp input
          (sizeBound (pcp.nativeWidth n)) (target.val + 1) inputLength)
        (boundedOracleStructuralFormulaPrefixFuel pcp input
          (sizeBound (pcp.nativeWidth n)) (target.val + 1))
        (initialNPOracleState inputLength
          (boundedOracleStructuralFormulaPrefixInput pcp input
            (sizeBound (pcp.nativeWidth n)) (target.val + 1))) =
      some
        (canonicalDescriptionInput canonical.circuit
          canonical.sizeBounded target).toNat := by
  rw [run_boundedOracleStructuralFormulaPrefixSATProgram,
    prefixSATOutput_boundedOracle_eq_canonical
      pcp input canonical target]

/-! ## Direct tagged-emitter suffix -/

/-- The exact fixed program linked immediately after the structural emitter. -/
def boundedOracleStructuralTaggedPrefixSATProgram : NPOracleProgram :=
  linkPrograms taggedToBalancedPreservingProgram
    boundedOracleStructuralFormulaPrefixSATProgram

def boundedOracleStructuralTaggedPrefixInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count : ℕ) : ℕ :=
  taggedToBalancedPreservingInput
    (boundedOracleStructuralFormulaAtoms pcp input bound)
    (encodeUnary count)

def boundedOracleStructuralTaggedPrefixFuel
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count : ℕ) : ℕ :=
  linkFuel boundedOracleStructuralFormulaPrefixSATProgram
    (taggedToBalancedPreservingFuel
      (boundedOracleStructuralFormulaAtoms pcp input bound))
    (boundedOracleStructuralFormulaPrefixFuel pcp input bound count)

def boundedOracleStructuralTaggedPrefixMaximumBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count inputLength : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (taggedToBalancedPreservingMaximumBits inputLength
        (boundedOracleStructuralFormulaAtoms pcp input bound)
        (encodeUnary count))
      (boundedOracleStructuralFormulaPrefixMaximumBits pcp input
        bound count inputLength)

theorem boundedOracleStructuralTaggedPrefixSATProgram_containsSAT :
    containsSAT boundedOracleStructuralTaggedPrefixSATProgram = true := by
  rw [boundedOracleStructuralTaggedPrefixSATProgram,
    containsSAT_linkPrograms,
    boundedOracleStructuralFormulaPrefixSATProgram_containsSAT]
  exact Bool.or_true _

/-- Direct exact refinement from the private tagged emitter stream through
canonical balancing, all formula clauses, and zero-first prefix SAT. -/
theorem run_boundedOracleStructuralTaggedPrefixSATProgram
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (bound count inputLength : ℕ) :
    runNPOracleProgram boundedOracleStructuralTaggedPrefixSATProgram
        (boundedOracleStructuralTaggedPrefixMaximumBits
          pcp input bound count inputLength)
        (boundedOracleStructuralTaggedPrefixFuel pcp input bound count)
        (initialNPOracleState inputLength
          (boundedOracleStructuralTaggedPrefixInput
            pcp input bound count)) =
      some
        (prefixSATOutput count <|
          boundedOracleRecoveryFormula pcp input bound) := by
  let atoms := boundedOracleStructuralFormulaAtoms pcp input bound
  let maximumBits :=
    boundedOracleStructuralTaggedPrefixMaximumBits
      pcp input bound count inputLength
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hfirstBits :
      taggedToBalancedPreservingMaximumBits inputLength atoms
          (encodeUnary count) ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondBits :
      boundedOracleStructuralFormulaPrefixMaximumBits pcp input
          bound count inputLength ≤
        maximumBits := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  apply run_linkPrograms hpositive hlengthBits
  · exact run_bits_mono
      (run_taggedToBalancedPreservingProgram inputLength atoms
        (encodeUnary count))
      hfirstBits
  · have hrun :=
      run_bits_mono
        (run_boundedOracleStructuralFormulaPrefixSATProgram
          pcp input bound count inputLength)
        hsecondBits
    simpa only [atoms, boundedOracleStructuralFormulaPrefixInput,
      taggedToBalancedPreservingOutput,
      boundedOracleStructuralFormulaAtoms_eq,
      countedCircuitInputFormulaBalancedFoldInput] using hrun

end NearCubicWires.BoundedOracleStructuralFormulaPrefixSATProgram
