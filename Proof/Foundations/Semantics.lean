import Mathlib
import Proof.Foundations.BalancedCNFCodec
import StatementSupport

/-!
# Concrete semantic vocabulary for the headline statements

This file fixes the Boolean, circuit, wire, agreement, and complexity objects
that occur in the paper's statements, in particular Theorem 2.5.  In particular, a wire count is computed
from retained bottom supports and retained top incidences; it is not an
uninterpreted resource predicate.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires

/-- The support-first bounded-integer representation imported from MTT/CTW. -/
structure NormalizedThresholdGate (n : ℕ) where
  weight : Fin n → ℤ
  threshold : ℤ

def NormalizedThresholdGate.eval {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) : Bool :=
  decide (gate.threshold ≤ ∑ i, gate.weight i * if input i then 1 else 0)

def NormalizedThresholdGate.strictEval {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n) : Bool :=
  decide (gate.threshold < ∑ i, gate.weight i * if input i then 1 else 0)

def NormalizedThresholdGate.parametersBoundedBy {n : ℕ}
    (gate : NormalizedThresholdGate n) (bound : ℕ) : Prop :=
  (∀ i, Int.natAbs (gate.weight i) ≤ bound) ∧
    Int.natAbs gate.threshold ≤ bound

structure ExactThresholdGate (n : ℕ) where
  weight : Fin n → ℤ
  target : ℤ

def ExactThresholdGate.eval {n : ℕ} (gate : ExactThresholdGate n)
    (input : BitInput n) : Bool :=
  decide ((∑ i, gate.weight i * if input i then 1 else 0) = gate.target)

def intBitLength (value : ℤ) : ℕ := Nat.log 2 value.natAbs + 1

def NormalizedThresholdGate.encodingBits {n : ℕ}
    (gate : NormalizedThresholdGate n) : ℕ :=
  intBitLength gate.threshold + ∑ i, intBitLength (gate.weight i)

def ExactThresholdGate.encodingBits {n : ℕ}
    (gate : ExactThresholdGate n) : ℕ :=
  intBitLength gate.target + ∑ i, intBitLength (gate.weight i)

/-- A deterministic decomposition result.  The `List` preserves occurrences:
duplicate exact gates may not be silently quotient-ed away. -/
structure ExactDecomposition {n : ℕ} (gate : NormalizedThresholdGate n) where
  children : List (ExactThresholdGate n)
  equivalent : ∀ input,
    gate.strictEval input = children.any (fun child => child.eval input)
  disjoint : ∀ input,
    (children.filter fun child => child.eval input).length ≤ 1

def SymmetricThresholdCircuit.wireCount {n : ℕ}
    (circuit : SymmetricThresholdCircuit n) : ℕ :=
  ∑ i, ((circuit.bottom i).support.card + 1)

noncomputable def ThresholdThresholdCircuit.wireCount {n : ℕ}
    (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i with circuit.topWeight i ≠ 0,
    ((circuit.bottom i).support.card + 1)

/-- Uniform agreement on the Boolean cube. -/
noncomputable def agreement {n : ℕ} (left right : BoolFunction n) : ℝ :=
  ((Finset.univ.filter fun input => left input = right input).card : ℝ) /
    (Fintype.card (BitInput n) : ℝ)

noncomputable def wireScale (coefficient : ℝ) (logExponent n : ℕ) : ℝ :=
  coefficient * (n : ℝ) ^ 3 / (logScale n : ℝ) ^ logExponent

noncomputable def inversePolynomialAdvantage (n : ℕ) (exponent : ℝ) : ℝ :=
  Real.rpow (n : ℝ) (-exponent)

/-! ## A small fixed machine model for `E^NP`

The NP oracle is satisfiability of a canonically decoded finite CNF.  The
register-machine interpreter charges one unit per instruction, including an
oracle query.  Consequently `ENPCertificate` cannot be inhabited merely by
storing the target language in an arbitrary evaluator: it must exhibit one
finite program that returns the right bit within the displayed fuel bound.
-/

def encodeBitInput {n : ℕ} (input : BitInput n) : ℕ :=
  ∑ i, if input i then 2 ^ i.val else 0

/-- The machine's little-endian input code is exactly `Nat.ofBits`.  Keeping
this identity beside the encoder prevents executable adapters from carrying
their own bit-order convention. -/
theorem encodeBitInput_eq_ofBits {n : ℕ} (input : BitInput n) :
    encodeBitInput input = Nat.ofBits input := by
  induction n with
  | zero =>
      simp [encodeBitInput]
  | succ n inductionHypothesis =>
      calc
        encodeBitInput input =
            (if input 0 then 1 else 0) +
              2 * encodeBitInput (fun index : Fin n => input index.succ) := by
          unfold encodeBitInput
          rw [Fin.sum_univ_succ, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro index _
          split
          · change 2 ^ (index.val + 1) = 2 * 2 ^ index.val
            rw [pow_succ]
            omega
          · simp
        _ =
            (if input 0 then 1 else 0) +
              2 * Nat.ofBits (fun index : Fin n => input index.succ) := by
          rw [inductionHypothesis]
        _ = Nat.ofBits input := by
          rw [Nat.ofBits_succ]
          have htail :
              (fun index : Fin n => input index.succ) =
                input ∘ Fin.succ := rfl
          rw [htail]
          cases input 0 <;> simp [Nat.mul_comm, Nat.add_comm]

theorem encodeBitInput_testBit {value width : ℕ}
    (hvalue : value < 2 ^ width) :
    encodeBitInput (fun bit : Fin width => value.testBit bit.val) = value := by
  rw [encodeBitInput_eq_ofBits, Nat.ofBits_testBit, Nat.mod_eq_of_lt hvalue]

structure ENPCertificate (language : Language) where
  program : NPOracleProgram
  exponent : ℕ
  exponentPositive : 0 < exponent
  onset : ℕ
  computes : ∀ n, onset ≤ n → ∀ input,
    runNPOracleProgram program (2 ^ (exponent * n)) (2 ^ (exponent * n))
      (initialNPOracleState n (encodeBitInput input)) =
        some (language n input).toNat

def InENP (language : Language) : Prop := Nonempty (ENPCertificate language)

end NearCubicWires
