import Proof.Foundations.Semantics

/-!
# Verified construction API for Boolean DAGs

`BooleanCircuit` stores a topologically ordered node list.  This module is the
only append API used by arithmetic and threshold compilers: every newly added
node may reference only the existing prefix, and the preservation/newest-value
lemmas make sharing explicit.
-/

namespace NearCubicWires

structure BooleanDAGBuilder (n : ℕ) where
  nodes : List (BooleanNode n)
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val

def BooleanDAGBuilder.empty (n : ℕ) : BooleanDAGBuilder n where
  nodes := []
  wellFormed := by intro index; exact Fin.elim0 index

def BooleanDAGBuilder.values {n : ℕ} (builder : BooleanDAGBuilder n)
    (input : BitInput n) : Array Bool :=
  builder.nodes.foldl
    (fun prior node => prior.push (node.eval input prior)) #[]

@[simp] theorem BooleanDAGBuilder.values_size {n : ℕ}
    (builder : BooleanDAGBuilder n) (input : BitInput n) :
    (builder.values input).size = builder.nodes.length := by
  have foldSize :
      ∀ (nodes : List (BooleanNode n)) (prior : Array Bool),
        (nodes.foldl
          (fun values node => values.push (node.eval input values))
          prior).size = prior.size + nodes.length := by
    intro nodes
    induction nodes with
    | nil =>
        intro prior
        simp
    | cons node tail inductionHypothesis =>
        intro prior
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        simp only [Array.size_push, List.length_cons]
        omega
  simpa [BooleanDAGBuilder.values] using foldSize builder.nodes #[]

def BooleanDAGBuilder.appendNode {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    BooleanDAGBuilder n where
  nodes := builder.nodes ++ [node]
  wellFormed := by
    intro index
    by_cases hold : index.val < builder.nodes.length
    · rw [List.get_eq_getElem, List.getElem_append_left hold]
      exact builder.wellFormed ⟨index.val, hold⟩
    · have hindex : index.val = builder.nodes.length := by
        have hlt := index.isLt
        simp only [List.length_append, List.length_singleton] at hlt
        omega
      rw [List.get_eq_getElem,
        List.getElem_concat_length hindex index.isLt, hindex]
      exact hnode

@[simp] theorem BooleanDAGBuilder.appendNode_nodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).nodes = builder.nodes ++ [node] :=
  rfl

@[simp] theorem BooleanDAGBuilder.appendNode_length {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).nodes.length =
      builder.nodes.length + 1 := by
  simp

theorem BooleanDAGBuilder.appendNode_values {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (input : BitInput n) :
    (builder.appendNode node hnode).values input =
      (builder.values input).push (node.eval input (builder.values input)) := by
  simp [BooleanDAGBuilder.values, BooleanDAGBuilder.appendNode,
    List.foldl_append]

def BooleanDAGBuilder.newest {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    Fin (builder.appendNode node hnode).nodes.length :=
  ⟨builder.nodes.length, by simp⟩

def BooleanDAGBuilder.liftRef {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (reference : Fin builder.nodes.length) :
    Fin (builder.appendNode node hnode).nodes.length :=
  ⟨reference.val, by simp [Nat.lt_succ_of_lt reference.isLt]⟩

@[simp] theorem BooleanDAGBuilder.liftRef_val {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (reference : Fin builder.nodes.length) :
    (builder.liftRef node hnode reference).val = reference.val :=
  rfl

theorem BooleanDAGBuilder.appendNode_preserves {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (input : BitInput n) (reference : Fin builder.nodes.length) :
    getElem? ((builder.appendNode node hnode).values input)
        (builder.liftRef node hnode reference).val =
      getElem? (builder.values input) reference.val := by
  rw [builder.appendNode_values node hnode input]
  rw [Array.getElem?_eq_getElem (by
    simp [BooleanDAGBuilder.liftRef])]
  rw [Array.getElem?_eq_getElem (by
    simp)]
  have href : reference.val < (builder.values input).size := by
    simp
  exact congrArg some (Array.getElem_push_lt href)

theorem BooleanDAGBuilder.appendNode_newest {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (input : BitInput n) :
    getElem? ((builder.appendNode node hnode).values input)
        (builder.newest node hnode).val =
      some (node.eval input (builder.values input)) := by
  rw [builder.appendNode_values node hnode input]
  rw [Array.getElem?_eq_getElem (by
    simp [BooleanDAGBuilder.newest])]
  simpa [BooleanDAGBuilder.newest, builder.values_size input] using
    congrArg some
      (Array.getElem_push_eq
        (xs := builder.values input)
        (x := node.eval input (builder.values input)))

structure BooleanDAGAppendResult {n : ℕ}
    (prior : BooleanDAGBuilder n) where
  builder : BooleanDAGBuilder n
  output : Fin builder.nodes.length
  lift : Fin prior.nodes.length → Fin builder.nodes.length
  outputIndex : output.val = prior.nodes.length
  liftIndex : ∀ reference, (lift reference).val = reference.val
  nodes : builder.nodes = prior.nodes ++ [builder.nodes.get output]

def BooleanDAGBuilder.append {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    BooleanDAGAppendResult builder where
  builder := builder.appendNode node hnode
  output := builder.newest node hnode
  lift := builder.liftRef node hnode
  outputIndex := rfl
  liftIndex := fun _ => rfl
  nodes := by simp [BooleanDAGBuilder.newest]

def BooleanDAGBuilder.appendConst {n : ℕ}
    (builder : BooleanDAGBuilder n) (value : Bool) :
    BooleanDAGAppendResult builder :=
  builder.append (.const value) trivial

def BooleanDAGBuilder.appendInput {n : ℕ}
    (builder : BooleanDAGBuilder n) (index : Fin n) :
    BooleanDAGAppendResult builder :=
  builder.append (.input index) trivial

def BooleanDAGBuilder.appendNot {n : ℕ}
    (builder : BooleanDAGBuilder n) (child : Fin builder.nodes.length) :
    BooleanDAGAppendResult builder :=
  builder.append (.not child.val) child.isLt

def BooleanDAGBuilder.appendAnd {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    BooleanDAGAppendResult builder :=
  builder.append (.and left.val right.val) ⟨left.isLt, right.isLt⟩

def BooleanDAGBuilder.appendOr {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    BooleanDAGAppendResult builder :=
  builder.append (.or left.val right.val) ⟨left.isLt, right.isLt⟩

/-! ## Compositional multi-node extensions -/

/-- `final` extends `prior` by one contiguous topological suffix.  Recording the
suffix, rather than an arbitrary embedding, makes index preservation canonical
and prevents arithmetic compilers from silently renumbering existing wires. -/
structure BooleanDAGExtension {n : ℕ}
    (prior final : BooleanDAGBuilder n) where
  suffix : List (BooleanNode n)
  nodes_eq : final.nodes = prior.nodes ++ suffix

namespace BooleanDAGExtension

def refl {n : ℕ} (builder : BooleanDAGBuilder n) :
    BooleanDAGExtension builder builder where
  suffix := []
  nodes_eq := by simp

def single {n : ℕ} (builder : BooleanDAGBuilder n)
    (node : BooleanNode n) (hnode : node.WellFormedAt builder.nodes.length) :
    BooleanDAGExtension builder (builder.appendNode node hnode) where
  suffix := [node]
  nodes_eq := rfl

def trans {n : ℕ} {first middle final : BooleanDAGBuilder n}
    (left : BooleanDAGExtension first middle)
    (right : BooleanDAGExtension middle final) :
    BooleanDAGExtension first final where
  suffix := left.suffix ++ right.suffix
  nodes_eq := by
    rw [right.nodes_eq, left.nodes_eq, List.append_assoc]

theorem length_eq {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final) :
    final.nodes.length =
      prior.nodes.length + extension.suffix.length := by
  rw [extension.nodes_eq, List.length_append]

theorem length_le {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final) :
    prior.nodes.length ≤ final.nodes.length := by
  rw [extension.length_eq]
  omega

/-- Existing wire addresses are unchanged by extension. -/
def lift {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (reference : Fin prior.nodes.length) : Fin final.nodes.length :=
  ⟨reference.val, Nat.lt_of_lt_of_le reference.isLt extension.length_le⟩

@[simp] theorem lift_val {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (reference : Fin prior.nodes.length) :
    (extension.lift reference).val = reference.val :=
  rfl

private theorem foldl_push_preserves {n : ℕ} (input : BitInput n)
    (suffix : List (BooleanNode n)) (prior : Array Bool)
    (index : ℕ) (hindex : index < prior.size) :
    getElem?
        (suffix.foldl
          (fun values node => values.push (node.eval input values))
          prior)
        index =
      getElem? prior index := by
  induction suffix generalizing prior with
  | nil => rfl
  | cons node tail inductionHypothesis =>
      rw [List.foldl_cons]
      rw [inductionHypothesis
        (prior := prior.push (node.eval input prior))
        (hindex := by simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem (by
        simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem hindex]
      exact congrArg some (Array.getElem_push_lt hindex)

/-- Extending a DAG preserves the value on every lifted old wire. -/
theorem wireValue_lift {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (input : BitInput n) (reference : Fin prior.nodes.length) :
    getElem? (final.values input) (extension.lift reference).val =
      getElem? (prior.values input) reference.val := by
  change getElem? (final.values input) reference.val =
    getElem? (prior.values input) reference.val
  rw [BooleanDAGBuilder.values, extension.nodes_eq, List.foldl_append]
  exact foldl_push_preserves input extension.suffix (prior.values input)
    reference.val (by simp)

end BooleanDAGExtension

/-- The result of compiling `k` output wires while extending a shared DAG. -/
structure BooleanDAGBuildResult {n : ℕ}
    (prior : BooleanDAGBuilder n) (k : ℕ) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  output : Fin k → Fin final.nodes.length

namespace BooleanDAGBuildResult

def addedNodes {n k : ℕ} {prior : BooleanDAGBuilder n}
    (result : BooleanDAGBuildResult prior k) : ℕ :=
  result.extension.suffix.length

theorem final_length {n k : ℕ} {prior : BooleanDAGBuilder n}
    (result : BooleanDAGBuildResult prior k) :
    result.final.nodes.length =
      prior.nodes.length + result.addedNodes :=
  result.extension.length_eq

end BooleanDAGBuildResult

def BooleanNode.edgeCount {n : ℕ} : BooleanNode n → ℕ
  | .const _ | .input _ => 0
  | .not _ => 1
  | .and _ _ | .or _ _ => 2

def BooleanDAGBuilder.edgeCount {n : ℕ}
    (builder : BooleanDAGBuilder n) : ℕ :=
  (builder.nodes.map BooleanNode.edgeCount).sum

@[simp] theorem BooleanDAGBuilder.appendNode_edgeCount {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).edgeCount =
      builder.edgeCount + node.edgeCount := by
  simp [BooleanDAGBuilder.edgeCount]

def BooleanDAGBuilder.finish {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (output : Fin builder.nodes.length) : BooleanCircuit n where
  nodes := builder.nodes
  output := output
  wellFormed := builder.wellFormed

@[simp] theorem BooleanDAGBuilder.finish_size {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (output : Fin builder.nodes.length) :
    (builder.finish output).size = builder.nodes.length :=
  rfl

@[simp] theorem BooleanDAGBuilder.finish_eval {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (output : Fin builder.nodes.length) (input : BitInput n) :
    (builder.finish output).eval input =
      (builder.values input)[output.val]?.getD false :=
  rfl

end NearCubicWires
