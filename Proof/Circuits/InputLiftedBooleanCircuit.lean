import Proof.Foundations.PCPPClausePadding

namespace NearCubicWires
namespace InputLiftedBooleanCircuit

open NearCubicWires
open NearCubicWires.ProjectionPCPPadding

/-- Prefix embedding of native coordinates into a padded input domain. -/
def inputPrefixEmbedding {native padded : ℕ} (hinput : native ≤ padded) :
    Fin native ↪ Fin padded where
  toFun index := Fin.castLE hinput index
  inj' := by
    intro left right hequal
    apply Fin.ext
    exact congrArg (fun index : Fin padded => index.val) hequal

@[simp] theorem inputPrefixEmbedding_apply
    {native padded : ℕ} (hinput : native ≤ padded) (index : Fin native) :
    inputPrefixEmbedding hinput index = Fin.castLE hinput index :=
  rfl

@[simp] theorem inputPrefixEmbedding_val
    {native padded : ℕ} (hinput : native ≤ padded) (index : Fin native) :
    (inputPrefixEmbedding hinput index).val = index.val :=
  rfl

def liftBooleanNodeInputs {native padded : ℕ} (hinput : native ≤ padded) :
    BooleanNode native → BooleanNode padded
  | .const value => .const value
  | .input index => .input (inputPrefixEmbedding hinput index)
  | .not child => .not child
  | .and left right => .and left right
  | .or left right => .or left right

theorem liftBooleanNodeInputs_wellFormed
    {native padded index : ℕ} (hinput : native ≤ padded)
    (node : BooleanNode native) (hnode : node.WellFormedAt index) :
    (liftBooleanNodeInputs hinput node).WellFormedAt index := by
  cases node <;> exact hnode

@[simp] theorem liftBooleanNodeInputs_eval
    {native padded : ℕ} (hinput : native ≤ padded)
    (node : BooleanNode native) (input : BitInput padded)
    (prior : Array Bool) :
    (liftBooleanNodeInputs hinput node).eval input prior =
      node.eval (prefixBits hinput input) prior := by
  cases node <;> rfl

/-- The native circuit evaluated on the prefix of a larger input cube. -/
def liftBooleanCircuitInputs {native padded : ℕ}
    (circuit : BooleanCircuit native) (hinput : native ≤ padded) :
    BooleanCircuit padded where
  nodes := circuit.nodes.map (liftBooleanNodeInputs hinput)
  output :=
    ⟨circuit.output.val, by
      simpa only [List.length_map] using circuit.output.isLt⟩
  wellFormed := by
    intro index
    let sourceIndex : Fin circuit.nodes.length :=
      ⟨index.val, by simpa using index.isLt⟩
    have hsource := circuit.wellFormed sourceIndex
    change
      ((circuit.nodes.map (liftBooleanNodeInputs hinput)).get index)
          |>.WellFormedAt index.val
    simp only [List.get_eq_getElem, List.getElem_map]
    exact liftBooleanNodeInputs_wellFormed hinput
      (circuit.nodes.get sourceIndex) hsource

private theorem foldl_liftBooleanNodeInputs
    {native padded : ℕ} (hinput : native ≤ padded)
    (input : BitInput padded) (nodes : List (BooleanNode native))
    (prior : Array Bool) :
    (nodes.map (liftBooleanNodeInputs hinput)).foldl
        (fun values node => values.push (node.eval input values)) prior =
      nodes.foldl
        (fun values node =>
          values.push (node.eval (prefixBits hinput input) values)) prior := by
  induction nodes generalizing prior with
  | nil => rfl
  | cons node nodes inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [liftBooleanNodeInputs_eval]
      exact inductionHypothesis _

@[simp] theorem liftBooleanCircuitInputs_values
    {native padded : ℕ} (circuit : BooleanCircuit native)
    (hinput : native ≤ padded) (input : BitInput padded) :
    (liftBooleanCircuitInputs circuit hinput).values input =
      circuit.values (prefixBits hinput input) := by
  unfold BooleanCircuit.values liftBooleanCircuitInputs
  exact foldl_liftBooleanNodeInputs hinput input circuit.nodes #[]

@[simp] theorem liftBooleanCircuitInputs_eval
    {native padded : ℕ} (circuit : BooleanCircuit native)
    (hinput : native ≤ padded) (input : BitInput padded) :
    (liftBooleanCircuitInputs circuit hinput).eval input =
      circuit.eval (prefixBits hinput input) := by
  unfold BooleanCircuit.eval
  rw [liftBooleanCircuitInputs_values]
  rfl

@[simp] theorem liftBooleanCircuitInputs_size
    {native padded : ℕ} (circuit : BooleanCircuit native)
    (hinput : native ≤ padded) :
    (liftBooleanCircuitInputs circuit hinput).size = circuit.size := by
  simp [BooleanCircuit.size, liftBooleanCircuitInputs]

end InputLiftedBooleanCircuit
end NearCubicWires
