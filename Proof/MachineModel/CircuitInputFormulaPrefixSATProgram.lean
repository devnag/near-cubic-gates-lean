import Proof.MachineModel.BoundedOracleRecoveryProgram
import Proof.Circuits.CircuitInputClauseBalancedCall

/-!
# Executable circuit-input CNF to prefix-SAT recovery

This module links the sole complete circuit-input clause fold directly to the
raw-clause prefix-SAT suffix.  Its public input is a balanced list of clause
atoms paired with a unary prefix count; no formula code, SAT answer, or host
clause generator crosses the machine boundary.
-/

namespace NearCubicWires.CircuitInputFormulaPrefixSATProgram

open NearCubicWires
open NearCubicWires.BoundedOracleRecoveryProgram
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputClauseBalancedCall
open NearCubicWires.CircuitInputCNF
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-- Complete fixed program from heterogeneous circuit-input clause atoms to
the final bit of a zero-first SAT prefix. -/
def circuitInputFormulaPrefixSATProgram : NPOracleProgram :=
  linkPrograms countedCircuitInputFormulaBalancedFoldProgram
    rawClausePrefixSATProgram

def circuitInputFormulaPrefixSATFuel {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) : ℕ :=
  linkFuel rawClausePrefixSATProgram
    (countedCircuitInputFormulaBalancedFoldFuel circuit)
    (rawClausePrefixSATFuel count (circuitInputFormula circuit))

def circuitInputFormulaPrefixSATMaximumBits {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) (count : ℕ) : ℕ :=
  max
    (countedCircuitInputFormulaBalancedFoldBits inputLength circuit count)
    (rawClausePrefixSATMaximumBits inputLength count
      (circuitInputFormula circuit))

theorem circuitInputFormulaPrefixSATProgram_containsSAT :
    containsSAT circuitInputFormulaPrefixSATProgram = true := by
  rw [circuitInputFormulaPrefixSATProgram, containsSAT_linkPrograms,
    rawClausePrefixSATProgram_containsSAT]
  exact Bool.or_true _

/-- Exact end-to-end refinement from every circuit-input formula clause to
the zero-first prefix-SAT result. -/
theorem run_circuitInputFormulaPrefixSATProgram {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) (count : ℕ) :
    runNPOracleProgram circuitInputFormulaPrefixSATProgram
        (circuitInputFormulaPrefixSATMaximumBits
          inputLength circuit count)
        (circuitInputFormulaPrefixSATFuel circuit count)
        (initialNPOracleState inputLength
          (countedCircuitInputFormulaBalancedFoldInput circuit count)) =
      some (prefixSATOutput count (circuitInputFormula circuit)) := by
  let maximumBits :=
    circuitInputFormulaPrefixSATMaximumBits inputLength circuit count
  have hfirstBits :
      countedCircuitInputFormulaBalancedFoldBits inputLength circuit count ≤
        maximumBits := by
    exact Nat.le_max_left _ _
  have hsecondBits :
      rawClausePrefixSATMaximumBits inputLength count
          (circuitInputFormula circuit) ≤ maximumBits := by
    exact Nat.le_max_right _ _
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    have :
        natBitLength inputLength ≤
          rawClausePrefixSATMaximumBits inputLength count
            (circuitInputFormula circuit) := by
      unfold rawClausePrefixSATMaximumBits
      exact Nat.le_max_left _ _
    exact this.trans hsecondBits
  have hpositive : 1 ≤ maximumBits := by
    have hprefixPositive :
        1 ≤ prefixSATMaximumBits count (circuitInputFormula circuit) := by
      unfold prefixSATMaximumBits natBitLength
      omega
    have hprefixBits :
        prefixSATMaximumBits count (circuitInputFormula circuit) ≤
          cnfPrefixSATMaximumBits inputLength count
            (circuitInputFormula circuit) := by
      unfold cnfPrefixSATMaximumBits
      exact
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    have hcnfBits :
        cnfPrefixSATMaximumBits inputLength count
            (circuitInputFormula circuit) ≤
          rawClausePrefixSATMaximumBits inputLength count
            (circuitInputFormula circuit) := by
      unfold rawClausePrefixSATMaximumBits
      exact
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact hprefixPositive.trans
      (hprefixBits.trans (hcnfBits.trans hsecondBits))
  apply run_linkPrograms hpositive hlengthBits
  · apply run_bits_mono
      (run_countedCircuitInputFormulaBalancedFoldProgram
        inputLength circuit count)
    exact hfirstBits
  · apply run_bits_mono
      (run_rawClausePrefixSATProgram inputLength count
        (circuitInputFormula circuit)
        (circuitInputFormula_threeLiteral circuit))
    exact hsecondBits

end NearCubicWires.CircuitInputFormulaPrefixSATProgram
