import Proof.Foundations.BooleanDAGBuilder

/-!
# Semantics-preserving Boolean DAG size padding

The pointwise-PCPP source expects a circuit whose DAG size is at least its
input arity.  Appending unreachable constants is the canonical way to meet
that syntactic precondition: old node addresses and the distinguished output
are unchanged, and the exact size increase remains visible.
-/

namespace NearCubicWires

def BooleanCircuit.toBuilder {n : ℕ} (circuit : BooleanCircuit n) :
    BooleanDAGBuilder n where
  nodes := circuit.nodes
  wellFormed := circuit.wellFormed

def BooleanDAGBuilder.appendFalse {n : ℕ}
    (builder : BooleanDAGBuilder n) : ℕ → BooleanDAGBuilder n
  | 0 => builder
  | count + 1 =>
      (builder.appendNode (.const false) trivial).appendFalse count

@[simp] theorem BooleanDAGBuilder.appendFalse_nodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (count : ℕ) :
    (builder.appendFalse count).nodes =
      builder.nodes ++ List.replicate count (.const false) := by
  induction count generalizing builder with
  | zero =>
      simp [BooleanDAGBuilder.appendFalse]
  | succ count ih =>
      simp [BooleanDAGBuilder.appendFalse, ih,
        List.append_assoc]
      rfl

def BooleanDAGBuilder.appendFalseExtension {n : ℕ}
    (builder : BooleanDAGBuilder n) (count : ℕ) :
    BooleanDAGExtension builder (builder.appendFalse count) where
  suffix := List.replicate count (.const false)
  nodes_eq := builder.appendFalse_nodes count

/-- Append exactly `count` unreachable constant nodes. -/
def BooleanCircuit.padSize {n : ℕ} (circuit : BooleanCircuit n)
    (count : ℕ) : BooleanCircuit n :=
  let prior := circuit.toBuilder
  let extension := prior.appendFalseExtension count
  (prior.appendFalse count).finish (extension.lift circuit.output)

@[simp] theorem BooleanCircuit.padSize_size {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) :
    (circuit.padSize count).size = circuit.size + count := by
  change (circuit.toBuilder.appendFalse count).nodes.length =
    circuit.nodes.length + count
  rw [BooleanDAGBuilder.appendFalse_nodes]
  simp [BooleanCircuit.toBuilder]

@[simp] theorem BooleanCircuit.padSize_eval {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) (input : BitInput n) :
    (circuit.padSize count).eval input = circuit.eval input := by
  let prior := circuit.toBuilder
  let extension := prior.appendFalseExtension count
  have hwire :=
    extension.wireValue_lift input circuit.output
  exact congrArg (fun value : Option Bool => value.getD false) hwire

/-- Minimal syntactic padding for the PCPP side condition. -/
def BooleanCircuit.padToArity {n : ℕ}
    (circuit : BooleanCircuit n) : BooleanCircuit n :=
  circuit.padSize (n - circuit.size)

theorem BooleanCircuit.arity_le_padToArity_size {n : ℕ}
    (circuit : BooleanCircuit n) :
    n ≤ circuit.padToArity.size := by
  simp [BooleanCircuit.padToArity]
  omega

theorem BooleanCircuit.padToArity_size_le {n : ℕ}
    (circuit : BooleanCircuit n) :
    circuit.padToArity.size ≤ circuit.size + n := by
  simp [BooleanCircuit.padToArity]

@[simp] theorem BooleanCircuit.padToArity_eval {n : ℕ}
    (circuit : BooleanCircuit n) (input : BitInput n) :
    circuit.padToArity.eval input = circuit.eval input := by
  simp [BooleanCircuit.padToArity]

end NearCubicWires
