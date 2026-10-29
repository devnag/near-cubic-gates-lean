import SourceAdapters.Proximity.PredicateCircuit
import SourceAdapters.Proximity.ClauseBlocks

/-!
Q02, `app:sources`, "Uniform three-query PCPP and code interfaces": one common block length depends only on q, never on the
circuit, old coins or predicate. Every resulting clause has exactly three
literals; padding has a dedicated dummy coordinate after all gate variables.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.TseitinCNF NearCubicWires.CircuitInputCNF

theorem node_block_length {q : ℕ} (index : ℕ) (node : BooleanNode q) :
    (circuitInputNodeClauses index node).length ≤ 3 := by
  cases node with
  | const b => cases b <;> simp [circuitInputNodeClauses]
  | input i => simp [circuitInputNodeClauses]
  | not child => simp [circuitInputNodeClauses]
  | and left right => simp [circuitInputNodeClauses]
  | or left right => simp [circuitInputNodeClauses]

theorem nodes_block_length {q : ℕ} (nodes : List (BooleanNode q)) (start : ℕ) :
    (circuitInputNodesClausesFrom start nodes).length ≤ 3 * nodes.length := by
  induction nodes generalizing start with
  | nil => simp [circuitInputNodesClausesFrom]
  | cons node rest ih =>
      have hn := node_block_length start node
      have hr := ih (start + 1)
      simp only [circuitInputNodesClausesFrom, List.length_append, List.length_cons]
      omega

theorem circuit_block_length {q : ℕ} (C : BooleanCircuit q) :
    (circuitInputFormula C).length ≤ q + 3 * C.size + 1 := by
  have h := nodes_block_length C.nodes 0
  simp only [circuitInputFormula, List.length_append, circuitInputTautologies_length,
    List.length_cons, List.length_nil, BooleanCircuit.size]
  omega

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": the decision circuit bound is uniform over every predicate on q bits. -/
def predicateNodeBound (q : ℕ) : ℕ := (3 * q + 2) * 2 ^ q + 1

def predicateClauseBound (q : ℕ) : ℕ := q + 3 * predicateNodeBound q + 1

def predicateBlockBits (q : ℕ) : ℕ := Nat.clog 2 (predicateClauseBound q)

def predicateBlockSize (q : ℕ) : ℕ := 2 ^ predicateBlockBits q

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a common binary-sized block with a fresh dummy coordinate. -/
def predicateBlock {q : ℕ} (predicate : BitInput q → Bool) : EncodedCNF :=
  padClauseBlock (predicateBlockSize q) (q + (predicateCircuit predicate).size)
    (circuitInputFormula (predicateCircuit predicate))

theorem predicateBlock_length {q : ℕ} (predicate : BitInput q → Bool) :
    (predicateBlock predicate).length = predicateBlockSize q := by
  apply padClauseBlock_length
  calc
    (circuitInputFormula (predicateCircuit predicate)).length ≤
        q + 3 * (predicateCircuit predicate).size + 1 := circuit_block_length _
    _ ≤ predicateClauseBound q := by
      have h := predicateCircuit_size predicate
      dsimp [predicateClauseBound, predicateNodeBound]
      omega
    _ ≤ predicateBlockSize q := binaryBlockSize_ge _

theorem predicateBlock_three {q : ℕ} (predicate : BitInput q → Bool) :
    ∀ clause ∈ predicateBlock predicate, clause.length = 3 :=
  padClauseBlock_three _ _ _ (circuit_block_three _)

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": exact consistency semantics for every answer tuple. -/
theorem predicateBlock_iff {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q) :
    predicate input = true ↔
      ∃ assignment : ℕ → Bool, recoveredCircuitInput assignment = input ∧
        formulaEval assignment (predicateBlock predicate) = true := by
  rw [← predicateCircuit_eval predicate input]
  exact padded_circuit_iff _ _ _ _

/-- `app:sources`, "Uniform three-query PCPP and code interfaces": a rejected answer tuple forces a false padded clause. -/
theorem predicateBlock_rejects {q : ℕ} (predicate : BitInput q → Bool) (input : BitInput q)
    (hreject : predicate input = false) (assignment : ℕ → Bool)
    (hinput : recoveredCircuitInput assignment = input) :
    ∃ clause ∈ predicateBlock predicate, clauseEval assignment clause = false := by
  obtain ⟨clause, hmem, hfalse⟩ := circuit_block_rejects (predicateCircuit predicate) input
    (by simpa only [predicateCircuit_eval] using hreject) assignment hinput
  refine ⟨clause, List.mem_append_left _ hmem, hfalse⟩

end NearCubicGates.Adapters.Proximity
