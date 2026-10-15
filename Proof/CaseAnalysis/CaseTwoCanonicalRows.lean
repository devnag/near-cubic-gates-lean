import Proof.CaseAnalysis.CaseTwoTraversalController

/-! The physical traversal reads the original canonical row codec. Bounds
come from its actual well-formed DAG, not a second decoder or choice. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_row_eq {n : ℕ} (bound : ℕ) (x : BooleanNode n) :
    boundedNodeDescriptionBits bound x=rowBits (boundedCircuitFieldLimit n bound) x:=by
  cases x <;> rfl

def canonicalTail {n : ℕ} (bound : ℕ) (c : BooleanCircuit n):=
  orderedNatBits (boundedCircuitFieldLimit n bound) 0++
    (List.replicate (bound-c.size) (boundedPaddingDescriptionBits n bound)).flatten

theorem canonical_word_eq {n : ℕ} (bound : ℕ) (c : BooleanCircuit n) :
    word (boundedCircuitFieldLimit n bound) c.nodes c.output.val (canonicalTail bound c)=
      canonicalBoundedCircuitDescription bound c:=by
  have he : (c.nodes.map (boundedNodeDescriptionBits bound)).flatten=
      c.nodes.flatMap (rowBits (boundedCircuitFieldLimit n bound)):=by
    induction c.nodes with
    | nil=>rfl
    | cons x xs ih=>
      simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,canonical_row_eq,ih]
  simp only [word,canonicalBoundedCircuitDescription,List.flatten_append,List.flatten_singleton,
    boundedOutputDescriptionBits,canonicalTail,he,List.append_assoc]

theorem canonical_node_values {n : ℕ} (bound index : ℕ) (x : BooleanNode n)
    (hi : index≤bound) (hw : x.WellFormedAt index) :
    PCPPRequestNodeSchema.fields x 1≤boundedCircuitFieldLimit n bound ∧
      PCPPRequestNodeSchema.fields x 2≤boundedCircuitFieldLimit n bound:=by
  cases x with
  | const b=>cases b <;> dsimp [PCPPRequestNodeSchema.fields,boundedCircuitFieldLimit] <;> omega
  | input i=>have ht:=i.isLt;dsimp [PCPPRequestNodeSchema.fields,boundedCircuitFieldLimit];omega
  | not j=>change j < index at hw;dsimp [PCPPRequestNodeSchema.fields,boundedCircuitFieldLimit];omega
  | and j k=>rcases hw with ⟨hj,hk⟩;dsimp [PCPPRequestNodeSchema.fields,boundedCircuitFieldLimit];omega
  | or j k=>rcases hw with ⟨hj,hk⟩;dsimp [PCPPRequestNodeSchema.fields,boundedCircuitFieldLimit];omega

theorem canonical_values {n bound : ℕ} (c : BooleanCircuit n) (hc : c.size≤bound) :
    ∀ x∈c.nodes,PCPPRequestNodeSchema.fields x 1≤boundedCircuitFieldLimit n bound ∧
      PCPPRequestNodeSchema.fields x 2≤boundedCircuitFieldLimit n bound:=by
  intro x hx
  obtain ⟨i,rfl⟩:=List.mem_iff_get.mp hx
  exact canonical_node_values bound i.val (c.nodes.get i)
    (by have ht:=i.isLt;change c.nodes.length≤bound at hc;omega) (c.wellFormed i)

theorem canonical_output {n bound : ℕ} (c : BooleanCircuit n) (hc : c.size≤bound) :
    c.output.val≤boundedCircuitFieldLimit n bound:=by
  have ht:=c.output.isLt
  change c.nodes.length≤bound at hc
  unfold boundedCircuitFieldLimit
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
