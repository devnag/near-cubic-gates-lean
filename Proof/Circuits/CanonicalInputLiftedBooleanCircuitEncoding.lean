import Proof.Circuits.InputLiftedBooleanCircuit

namespace NearCubicWires.CanonicalInputLiftedBooleanCircuitEncoding

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InputLiftedBooleanCircuit

@[simp] theorem encodeBooleanNode_liftBooleanNodeInputs
    {native padded : ℕ} (hinput : native ≤ padded)
    (node : BooleanNode native) :
    encodeBooleanNode (liftBooleanNodeInputs hinput node) =
      encodeBooleanNode node := by
  cases node <;> rfl

/-- Input-axis lifting is representation-transparent at the canonical circuit
codec. -/
@[simp] theorem encodeBooleanCircuit_liftBooleanCircuitInputs
    {native padded : ℕ} (circuit : BooleanCircuit native)
    (hinput : native ≤ padded) :
    encodeBooleanCircuit (liftBooleanCircuitInputs circuit hinput) =
      encodeBooleanCircuit circuit := by
  unfold encodeBooleanCircuit liftBooleanCircuitInputs
  have hnodes :
      (circuit.nodes.map (liftBooleanNodeInputs hinput)).map
          encodeBooleanNode =
        circuit.nodes.map encodeBooleanNode := by
    induction circuit.nodes with
    | nil => rfl
    | cons node nodes inductionHypothesis =>
        simp only [List.map_cons, inductionHypothesis]
        rw [encodeBooleanNode_liftBooleanNodeInputs]
  rw [hnodes]

end NearCubicWires.CanonicalInputLiftedBooleanCircuitEncoding
