import Proof.Foundations.OuterPCPRecovery

/-!
# Restricting exact-width outer oracles to the native PCP face

Exact-width padding presents the outer proof as a circuit on the common width,
while the imported executable substitution consumes a circuit on its native
width.  The padded verifier queries only the zero-suffix face.  This module
proves that restricting a padded circuit to that face preserves every verifier
row, so both views use one oracle rather than parallel semantic witnesses.
-/

namespace NearCubicWires.PaddedOracleRestriction

open NearCubicWires
open NearCubicWires.CaseOnePadding
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

def zeroPadding {native padded : ℕ} : BitInput (padded - native) :=
  fun _ => false

def restrictPaddedOracle {native padded : ℕ}
    (circuit : BooleanCircuit padded) (hwidth : native ≤ padded) :
    BooleanCircuit native :=
  restrictBooleanCircuit circuit hwidth zeroPadding

private theorem splitInput_eq_joinBits
    {native padded : ℕ} (hwidth : native ≤ padded)
    (input : BitInput native) :
    (fun index =>
        Sum.elim input (zeroPadding (native := native) (padded := padded))
          ((finSplitEquiv hwidth).symm index)) =
      joinBits hwidth input zeroPadding := by
  funext index
  obtain ⟨index, rfl⟩ := (finSplitEquiv hwidth).surjective index
  cases index with
  | inl index =>
      simp [finSplitEquiv, joinBits]
  | inr index =>
      simp [finSplitEquiv, joinBits, zeroPadding]

@[simp] theorem restrictPaddedOracle_eval
    {native padded : ℕ} (circuit : BooleanCircuit padded)
    (hwidth : native ≤ padded) (input : BitInput native) :
    (restrictPaddedOracle circuit hwidth).eval input =
      circuit.eval (joinBits hwidth input zeroPadding) := by
  rw [restrictPaddedOracle, restrictBooleanCircuit_eval]
  rw [splitInput_eq_joinBits]

theorem projectedInput_padProjectionPCP
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (randomness : BitInput (paddedWidth n))
    (query : Fin (pcp.queryCount n)) :
    projectedInput (padProjectionPCP pcp paddedWidth hwidth)
        input randomness query =
      joinBits (hwidth n)
        (projectedInput pcp input (prefixBits (hwidth n) randomness) query)
        zeroPadding := by
  funext bit
  by_cases hbit : bit.val < pcp.nativeWidth n
  · simp [projectedInput, padProjectionPCP, joinBits, hbit,
      liftProjectedRandomBit_eval]
  · simp [projectedInput, padProjectionPCP, joinBits, zeroPadding, hbit,
      ProjectedRandomBit.eval]

theorem acceptsOracleCircuit_restrictPaddedOracle
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (circuit : BooleanCircuit (paddedWidth n))
    (randomness : BitInput (paddedWidth n)) :
    acceptsOracleCircuit pcp input
        (restrictPaddedOracle circuit (hwidth n))
        (prefixBits (hwidth n) randomness) =
      acceptsOracleCircuit (padProjectionPCP pcp paddedWidth hwidth)
        input circuit randomness := by
  unfold acceptsOracleCircuit
  rw [padProjectionPCP_decision]
  congr 1
  funext query
  rw [restrictPaddedOracle_eval]
  rw [projectedInput_padProjectionPCP]
  rfl

theorem restrictPaddedOracle_accepts
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n : ℕ} (input : BitInput n)
    (circuit : BooleanCircuit (paddedWidth n))
    (accepts : ∀ randomness,
      acceptsOracleCircuit (padProjectionPCP pcp paddedWidth hwidth)
        input circuit randomness) :
    ∀ randomness,
      acceptsOracleCircuit pcp input
        (restrictPaddedOracle circuit (hwidth n)) randomness := by
  intro randomness
  let paddedRandomness :=
    joinBits (hwidth n) randomness
      (zeroPadding (native := pcp.nativeWidth n)
        (padded := paddedWidth n))
  rw [← prefixBits_joinBits (hwidth n) randomness
    (zeroPadding (native := pcp.nativeWidth n)
      (padded := paddedWidth n))]
  rw [acceptsOracleCircuit_restrictPaddedOracle]
  exact accepts paddedRandomness

@[simp] theorem restrictPaddedOracle_size
    {native padded : ℕ} (circuit : BooleanCircuit padded)
    (hwidth : native ≤ padded) :
    (restrictPaddedOracle circuit hwidth).size = circuit.size := by
  simp [restrictPaddedOracle]

end NearCubicWires.PaddedOracleRestriction
