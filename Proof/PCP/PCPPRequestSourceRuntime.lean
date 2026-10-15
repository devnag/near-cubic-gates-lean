import Proof.PCP.PCPPRequestPipelineRuntime

/-! A circuit-size bound for the already executed, single PCPP source call.
The native descriptor is bounded using the actual DAG's well-formedness;
the canonical serializer and source constructor keep their original budgets. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestRuntime
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceParameter {n : ℕ} (c : BooleanCircuit n) := n+c.size+5
def sourceDegree (a : PointwisePCPPAlgorithm) := max 312 a.degree
def sourceCoefficient (a : PointwisePCPPAlgorithm) :=
  inputCoefficient*39^156+2*a.coefficient+3

theorem natural_width {M v : ℕ} (hv : v+1 ≤ M) :
    (natWord v).length ≤ 2*M+1 := by
  rw [DecompositionSource.natWord_length]
  have h := Nat.log_le_self 2 v
  unfold natBitLength
  omega

theorem native_width {n : ℕ} (c : BooleanCircuit n) (i : Fin c.nodes.length) :
    (PCPPRequestNodeSchema.native (c.nodes.get i)).length ≤
      6*sourceParameter c+3 := by
  have hf (j : Fin 3) : PCPPRequestNodeSchema.fields (c.nodes.get i) j+1 ≤
      sourceParameter c := by
    have h := PCPPRequestNodeSchema.field_bound _ i.val (c.wellFormed i) j
    have hi := i.isLt
    change PCPPRequestNodeSchema.fields (c.nodes.get i) j+1 ≤ n+c.nodes.length+5
    omega
  have h0 := natural_width (hf 0)
  have h1 := natural_width (hf 1)
  have h2 := natural_width (hf 2)
  dsimp only [PCPPRequestNodeSchema.native]
  simp only [List.length_append]
  omega

private theorem stream_length_le {n B : ℕ} (nodes : List (BooleanNode n))
    (h : ∀ node ∈ nodes, (PCPPRequestNodeSchema.native node).length ≤ B) :
    (nodes.flatMap PCPPRequestNodeSchema.native).length ≤ nodes.length*B := by
  induction nodes with
  | nil => simp only [List.flatMap_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons node nodes ih =>
    have hn := h node (by simp)
    have ht := ih (fun v hv => h v (by simp only [List.mem_cons]; exact Or.inr hv))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

theorem descriptor_parameter {n : ℕ} (c : BooleanCircuit n) :
    parameter c.nodes (natWord c.output.val) ≤ 39*(sourceParameter c)^2 := by
  let M := sourceParameter c
  have hM : 1 ≤ M := by dsimp [M,sourceParameter]; omega
  have hn : n+1 ≤ M := by dsimp [M,sourceParameter]; omega
  have hs : c.size+1 ≤ M := by dsimp [M,sourceParameter]; omega
  have ho : c.output.val+1 ≤ M := by
    have h := c.output.isLt
    dsimp [M,sourceParameter,BooleanCircuit.size]
    omega
  have hstream : (PCPPRequestNodeLoop.stream c.nodes).length ≤ c.size*(6*M+3) := by
    apply stream_length_le
    intro node hnode
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hnode
    rw [← hi]
    exact native_width c i
  have hn' := natural_width hn
  have hs' := natural_width hs
  have ho' := natural_width ho
  change parameter c.nodes (natWord c.output.val) ≤ 39*M^2
  unfold parameter PCPPRequestNodeGlobal.payload DecompositionInputCounts.word
  rw [frame_length]
  simp only [List.length_append]
  change n+ (2*((natWord n).length+(natWord c.size).length+
    ((PCPPRequestNodeLoop.stream c.nodes).length+(natWord c.output.val).length))+1)+1 ≤ 39*M^2
  nlinarith

theorem input_source_bound {n : ℕ} (c : BooleanCircuit n) :
    PCPPRequestInput.budget c ≤ inputCoefficient*39^156*(sourceParameter c)^312 := by
  calc
    _ ≤ inputCoefficient*(parameter c.nodes (natWord c.output.val))^156 := input_bound c
    _ ≤ inputCoefficient*(39*(sourceParameter c)^2)^156 := by
      exact Nat.mul_le_mul_left inputCoefficient (Nat.pow_le_pow_left (descriptor_parameter c) 156)
    _ = _ := by ring

private theorem add_source_bound (M e f I S b t : ℕ) (hM : 1 ≤ M)
    (hb : b ≤ I*M^e) (ht : t ≤ S*M^f) :
    b+2*t+3 ≤ (I+2*S+3)*M^(max e f) := by
  have he := Nat.pow_le_pow_right hM (show e ≤ max e f from Nat.le_max_left _ _)
  have hf := Nat.pow_le_pow_right hM (show f ≤ max e f from Nat.le_max_right _ _)
  have hi := hb.trans (Nat.mul_le_mul_left I he)
  have hs := ht.trans (Nat.mul_le_mul_left S hf)
  have hone : 1 ≤ M^(max e f) := Nat.one_le_pow _ _ hM
  nlinarith

theorem source_bound (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :
    PCPPRequestSource.budget a r ≤ sourceCoefficient a*(sourceParameter r.circuit)^(sourceDegree a) := by
  have hpos : 1 ≤ sourceParameter r.circuit := by unfold sourceParameter; omega
  have hbase : r.circuit.size+r.arity+1 ≤ sourceParameter r.circuit := by
    unfold sourceParameter
    omega
  have hsrc : PCPPRequestSource.sourceBudget a r ≤ a.coefficient*(sourceParameter r.circuit)^a.degree :=
    Nat.mul_le_mul_left a.coefficient (Nat.pow_le_pow_left hbase a.degree)
  exact add_source_bound (sourceParameter r.circuit) 312 a.degree (inputCoefficient*39^156)
    a.coefficient (PCPPRequestInput.budget r.circuit) (PCPPRequestSource.sourceBudget a r)
    hpos (input_source_bound r.circuit) hsrc

theorem sourceCoefficient_pos (a : PointwisePCPPAlgorithm) : 0 < sourceCoefficient a := by
  unfold sourceCoefficient
  omega

theorem cold_source_bound (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (PCPPRequestSource.machine a) (PCPPRequestSource.budget a request)
      (fun i => if i.val=0 then frame
        (PCPPRequestNodeGlobal.payload request.circuit.nodes (natWord request.circuit.output.val)) else [])=some r ∧
      r.final.tapes (PCPPRequestSource.outputSlot a)=pcppOutput request (a.output request) ∧
      r.final.heads (PCPPRequestSource.outputSlot a)=0 ∧
      r.steps ≤ sourceCoefficient a*(sourceParameter request.circuit)^(sourceDegree a) := by
  obtain ⟨r,hr,ho,hh,hs⟩ := PCPPRequestSource.cold_run a request
  exact ⟨r,hr,ho,hh,hs.trans (source_bound a request)⟩

end NearCubicWires.RepairOrdinary.PCPPRequestRuntime
