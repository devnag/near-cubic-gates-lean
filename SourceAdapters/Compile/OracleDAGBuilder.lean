import NineInputs

/-!
proof of `thm:short-pcp-ours`, Step 4: compile the bounded verifier using a shared DAG, with each
proof read an oracle gate on its actual earlier address wires. This module
provides the checked append API; it asserts no computation compiler/runtime.
The builder uses the literal MW20 oracle nodes.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.Bindings.MW20
set_option autoImplicit false

structure OracleDAGBuilder (n arity : ℕ) where
  nodes : List (OracleNode n arity)
  wellFormed :
    ∀ index : Fin nodes.length,
      (nodes.get index).WellFormedAt index.val

def OracleDAGBuilder.empty (n arity : ℕ) : OracleDAGBuilder n arity where
  nodes := []
  wellFormed := by intro index; exact Fin.elim0 index

def OracleDAGBuilder.values {n arity : ℕ} (builder : OracleDAGBuilder n arity)
    (O : BitInput arity → Bool) (input : BitInput n) : Array Bool :=
  builder.nodes.foldl
    (fun prior node => prior.push (node.eval O input prior)) #[]

@[simp] theorem OracleDAGBuilder.values_size {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (O : BitInput arity → Bool) (input : BitInput n) :
    (builder.values O input).size = builder.nodes.length := by
  have foldSize :
      ∀ (nodes : List (OracleNode n arity)) (prior : Array Bool),
        (nodes.foldl
          (fun values node => values.push (node.eval O input values))
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
  simpa [OracleDAGBuilder.values] using foldSize builder.nodes #[]

def OracleDAGBuilder.appendNode {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    OracleDAGBuilder n arity where
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

@[simp] theorem OracleDAGBuilder.appendNode_nodes {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).nodes = builder.nodes ++ [node] :=
  rfl

@[simp] theorem OracleDAGBuilder.appendNode_length {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).nodes.length =
      builder.nodes.length + 1 := by
  simp

theorem OracleDAGBuilder.appendNode_values {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length)
    (O : BitInput arity → Bool) (input : BitInput n) :
    (builder.appendNode node hnode).values O input =
      (builder.values O input).push (node.eval O input (builder.values O input)) := by
  simp [OracleDAGBuilder.values, OracleDAGBuilder.appendNode,
    List.foldl_append]

def OracleDAGBuilder.newest {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    Fin (builder.appendNode node hnode).nodes.length :=
  ⟨builder.nodes.length, by simp⟩

def OracleDAGBuilder.liftRef {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length)
    (reference : Fin builder.nodes.length) :
    Fin (builder.appendNode node hnode).nodes.length :=
  ⟨reference.val, by simp [Nat.lt_succ_of_lt reference.isLt]⟩

@[simp] theorem OracleDAGBuilder.liftRef_val {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length)
    (reference : Fin builder.nodes.length) :
    (builder.liftRef node hnode reference).val = reference.val :=
  rfl

theorem OracleDAGBuilder.appendNode_preserves {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length)
    (O : BitInput arity → Bool) (input : BitInput n) (reference : Fin builder.nodes.length) :
    getElem? ((builder.appendNode node hnode).values O input)
        (builder.liftRef node hnode reference).val =
      getElem? (builder.values O input) reference.val := by
  rw [builder.appendNode_values node hnode O input]
  rw [Array.getElem?_eq_getElem (by
    simp [OracleDAGBuilder.liftRef])]
  rw [Array.getElem?_eq_getElem (by
    simp)]
  have href : reference.val < (builder.values O input).size := by
    simp
  exact congrArg some (Array.getElem_push_lt href)

theorem OracleDAGBuilder.appendNode_newest {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length)
    (O : BitInput arity → Bool) (input : BitInput n) :
    getElem? ((builder.appendNode node hnode).values O input)
        (builder.newest node hnode).val =
      some (node.eval O input (builder.values O input)) := by
  rw [builder.appendNode_values node hnode O input]
  rw [Array.getElem?_eq_getElem (by
    simp [OracleDAGBuilder.newest])]
  simpa [OracleDAGBuilder.newest, builder.values_size O input] using
    congrArg some
      (Array.getElem_push_eq
        (xs := builder.values O input)
        (x := node.eval O input (builder.values O input)))

structure OracleDAGAppendResult {n arity : ℕ}
    (prior : OracleDAGBuilder n arity) where
  builder : OracleDAGBuilder n arity
  output : Fin builder.nodes.length
  lift : Fin prior.nodes.length → Fin builder.nodes.length
  outputIndex : output.val = prior.nodes.length
  liftIndex : ∀ reference, (lift reference).val = reference.val
  nodes : builder.nodes = prior.nodes ++ [builder.nodes.get output]

def OracleDAGBuilder.append {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    OracleDAGAppendResult builder where
  builder := builder.appendNode node hnode
  output := builder.newest node hnode
  lift := builder.liftRef node hnode
  outputIndex := rfl
  liftIndex := fun _ => rfl
  nodes := by simp [OracleDAGBuilder.newest]

def OracleDAGBuilder.appendConst {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (value : Bool) :
    OracleDAGAppendResult builder :=
  builder.append (.const value) trivial

def OracleDAGBuilder.appendInput {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (index : Fin n) :
    OracleDAGAppendResult builder :=
  builder.append (.input index) trivial

def OracleDAGBuilder.appendNot {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (child : Fin builder.nodes.length) :
    OracleDAGAppendResult builder :=
  builder.append (.not child.val) child.isLt

def OracleDAGBuilder.appendAnd {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (left right : Fin builder.nodes.length) :
    OracleDAGAppendResult builder :=
  builder.append (.and left.val right.val) ⟨left.isLt, right.isLt⟩

def OracleDAGBuilder.appendOr {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (left right : Fin builder.nodes.length) :
    OracleDAGAppendResult builder :=
  builder.append (.or left.val right.val) ⟨left.isLt, right.isLt⟩

/-- proof of `thm:short-pcp-ours`, Step 4: all oracle argument wires belong to the existing DAG. -/
def OracleDAGBuilder.appendOracle {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (args : Fin arity → Fin builder.nodes.length) :
    OracleDAGAppendResult builder :=
  builder.append (.oracle (fun j => (args j).val)) (fun j => (args j).isLt)

/-! ## Compositional multi-node extensions -/

/-- `final` extends `prior` by one contiguous topological suffix.  Recording the
suffix, rather than an arbitrary embedding, makes index preservation canonical
and prevents arithmetic compilers from silently renumbering existing wires. -/
structure OracleDAGExtension {n arity : ℕ}
    (prior final : OracleDAGBuilder n arity) where
  suffix : List (OracleNode n arity)
  nodes_eq : final.nodes = prior.nodes ++ suffix

namespace OracleDAGExtension

def refl {n arity : ℕ} (builder : OracleDAGBuilder n arity) :
    OracleDAGExtension builder builder where
  suffix := []
  nodes_eq := by simp

def single {n arity : ℕ} (builder : OracleDAGBuilder n arity)
    (node : OracleNode n arity) (hnode : node.WellFormedAt builder.nodes.length) :
    OracleDAGExtension builder (builder.appendNode node hnode) where
  suffix := [node]
  nodes_eq := rfl

def trans {n arity : ℕ} {first middle final : OracleDAGBuilder n arity}
    (left : OracleDAGExtension first middle)
    (right : OracleDAGExtension middle final) :
    OracleDAGExtension first final where
  suffix := left.suffix ++ right.suffix
  nodes_eq := by
    rw [right.nodes_eq, left.nodes_eq, List.append_assoc]

theorem length_eq {n arity : ℕ} {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final) :
    final.nodes.length =
      prior.nodes.length + extension.suffix.length := by
  rw [extension.nodes_eq, List.length_append]

theorem length_le {n arity : ℕ} {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final) :
    prior.nodes.length ≤ final.nodes.length := by
  rw [extension.length_eq]
  omega

/-- Existing wire addresses are unchanged by extension. -/
def lift {n arity : ℕ} {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final)
    (reference : Fin prior.nodes.length) : Fin final.nodes.length :=
  ⟨reference.val, Nat.lt_of_lt_of_le reference.isLt extension.length_le⟩

@[simp] theorem lift_val {n arity : ℕ} {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final)
    (reference : Fin prior.nodes.length) :
    (extension.lift reference).val = reference.val :=
  rfl

private theorem foldl_push_preserves {n arity : ℕ} (O : BitInput arity → Bool) (input : BitInput n)
    (suffix : List (OracleNode n arity)) (prior : Array Bool)
    (index : ℕ) (hindex : index < prior.size) :
    getElem?
        (suffix.foldl
          (fun values node => values.push (node.eval O input values))
          prior)
        index =
      getElem? prior index := by
  induction suffix generalizing prior with
  | nil => rfl
  | cons node tail inductionHypothesis =>
      rw [List.foldl_cons]
      rw [inductionHypothesis
        (prior := prior.push (node.eval O input prior))
        (hindex := by simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem (by
        simpa using Nat.lt_succ_of_lt hindex)]
      rw [Array.getElem?_eq_getElem hindex]
      exact congrArg some (Array.getElem_push_lt hindex)

/-- Extending a DAG preserves the value on every lifted old wire. -/
theorem wireValue_lift {n arity : ℕ} {prior final : OracleDAGBuilder n arity}
    (extension : OracleDAGExtension prior final)
    (O : BitInput arity → Bool) (input : BitInput n) (reference : Fin prior.nodes.length) :
    getElem? (final.values O input) (extension.lift reference).val =
      getElem? (prior.values O input) reference.val := by
  change getElem? (final.values O input) reference.val =
    getElem? (prior.values O input) reference.val
  rw [OracleDAGBuilder.values, extension.nodes_eq, List.foldl_append]
  exact foldl_push_preserves O input extension.suffix (prior.values O input)
    reference.val (by simp)

end OracleDAGExtension

/-- The result of compiling `k` output wires while extending a shared DAG. -/
structure OracleDAGBuildResult {n arity : ℕ}
    (prior : OracleDAGBuilder n arity) (k : ℕ) where
  final : OracleDAGBuilder n arity
  extension : OracleDAGExtension prior final
  output : Fin k → Fin final.nodes.length

namespace OracleDAGBuildResult

def addedNodes {n arity k : ℕ} {prior : OracleDAGBuilder n arity}
    (result : OracleDAGBuildResult prior k) : ℕ :=
  result.extension.suffix.length

theorem final_length {n arity k : ℕ} {prior : OracleDAGBuilder n arity}
    (result : OracleDAGBuildResult prior k) :
    result.final.nodes.length =
      prior.nodes.length + result.addedNodes :=
  result.extension.length_eq

end OracleDAGBuildResult

def oracleNodeEdgeCount {n arity : ℕ} : OracleNode n arity → ℕ
  | .const _ | .input _ => 0
  | .not _ => 1
  | .and _ _ | .or _ _ => 2
  | .oracle _ => arity

def OracleDAGBuilder.edgeCount {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) : ℕ :=
  (builder.nodes.map oracleNodeEdgeCount).sum

@[simp] theorem OracleDAGBuilder.appendNode_edgeCount {n arity : ℕ}
    (builder : OracleDAGBuilder n arity) (node : OracleNode n arity)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (builder.appendNode node hnode).edgeCount =
      builder.edgeCount + oracleNodeEdgeCount node := by
  simp [OracleDAGBuilder.edgeCount]

def OracleDAGBuilder.finish {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (output : Fin builder.nodes.length) : OracleCircuit n arity where
  nodes := builder.nodes
  output := output
  wellFormed := builder.wellFormed

@[simp] theorem OracleDAGBuilder.finish_size {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (output : Fin builder.nodes.length) :
    (builder.finish output).size = builder.nodes.length :=
  rfl

@[simp] theorem OracleDAGBuilder.finish_eval {n arity : ℕ}
    (builder : OracleDAGBuilder n arity)
    (output : Fin builder.nodes.length) (O : BitInput arity → Bool) (input : BitInput n) :
    (builder.finish output).eval O input =
      (builder.values O input)[output.val]?.getD false :=
  rfl

end NearCubicGates.Adapters.Compile
