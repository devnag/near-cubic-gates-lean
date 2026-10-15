import Proof.PCP.PCPPRequestNodeListEntry
import Proof.PCP.PCPPRequestNodeBudget

/-! One original-input capacity suffices for every actual node body. The
existing cold header producer will physically construct exactly this value. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
open RepairRepresentation PCPPRequestNodeCold PCPPRequestNodeSchema
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacityCoefficient : ℕ := 5000000000000000001
def capacity (source : List Bool) : ℕ := capacityCoefficient*((frame source).length+1)^12

theorem native_length {n : ℕ} (node : BooleanNode n) :
    (native node).length=2*width node+3 := by
  simp only [native,List.length_append,DecompositionSource.natWord_length]
  unfold width
  ring

theorem member_width {n : ℕ} (node : BooleanNode n) (nodes : List (BooleanNode n))
    (hmem : node∈nodes) : width node ≤ (PCPPRequestNodeLoop.stream nodes).length := by
  induction nodes with
  | nil => simp at hmem
  | cons first rest ih =>
    simp only [List.mem_cons] at hmem
    rw [PCPPRequestNodeLoop.stream_cons,List.length_append,native_length]
    rcases hmem with h | h
    · subst first
      omega
    · have hr := ih h
      omega

theorem count_le_stream {n : ℕ} (nodes : List (BooleanNode n)) :
    nodes.length ≤ (PCPPRequestNodeLoop.stream nodes).length := by
  induction nodes with
  | nil => simp
  | cons first rest ih =>
    rw [PCPPRequestNodeLoop.stream_cons,List.length_append,native_length,List.length_cons]
    omega

theorem node_capacity {n : ℕ} (pre suffix : List Bool) (nodes : List (BooleanNode n)) :
    ∀ node∈nodes,PCPPRequestNodeCold.budget node+1 ≤
      capacity (pre++PCPPRequestNodeLoop.stream nodes++suffix) := by
  intro node hnode
  have hw := member_width node nodes hnode
  have hwidth : width node+1 ≤ (frame (pre++PCPPRequestNodeLoop.stream nodes++suffix)).length+1 := by
    rw [frame_length,List.length_append,List.length_append]
    omega
  have hp := Nat.pow_le_pow_left hwidth 12
  have hb := PCPPRequestNodeCold.budget_envelope node
  have h1 : 1 ≤ ((frame (pre++PCPPRequestNodeLoop.stream nodes++suffix)).length+1)^12 :=
    Nat.one_le_pow _ _ (by omega)
  unfold capacity capacityCoefficient
  omega

end NearCubicWires.RepairOrdinary.PCPPRequestNodeGlobal
