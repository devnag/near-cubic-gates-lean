import Proof.PCP.PCPPRequestSourceInput
import Proof.Circuits.DecompositionInputBudget

/-! The cold canonical node stream has one fixed polynomial cost in the
actual original descriptor length and arity. Its produced stream size is
charged by that same execution, avoiding another codec-size derivation. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestRuntime
open LocalBitMultitape RepairRepresentation PCPPRequestNodeGlobal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coldCoefficient : ℕ := PCPSerializerCapacity.coefficient 12 capacityCoefficient+8*capacityCoefficient+1000
def parameter {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :=
  n+(frame (payload nodes suffix)).length+1

theorem cold_bound {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    coldBudget nodes suffix ≤ coldCoefficient*(parameter nodes suffix)^13 := by
  let N := (frame (payload nodes suffix)).length
  let X := parameter nodes suffix
  have hX : 1 ≤ X := by dsimp [X,parameter]; omega
  have hN : N+1 ≤ X := by dsimp [N,X,parameter]; omega
  have hm : nodes.length ≤ N := by
    have h := count_le_stream nodes
    dsimp only [N,payload,DecompositionInputCounts.word]
    rw [frame_length]
    simp only [List.length_append]
    omega
  have hp := DecompositionResource.cold_budget 12 capacityCoefficient n nodes.length N
    (PCPPRequestNodeLoop.stream nodes++suffix) rfl hm
  have hpre : DecompositionColdPrepare.budget 12 capacityCoefficient n nodes.length
      (PCPPRequestNodeLoop.stream nodes++suffix) ≤
      (PCPSerializerCapacity.coefficient 12 capacityCoefficient+512)*X^13+4 := by
    have hnPow := Nat.pow_le_pow_left hN 13
    have hxPow : X^2 ≤ X^13 := Nat.pow_le_pow_right hX (by decide)
    change _ ≤ PCPSerializerCapacity.coefficient 12 capacityCoefficient*(N+1)^13+512*X^2+4 at hp
    have hc := Nat.mul_le_mul_left (PCPSerializerCapacity.coefficient 12 capacityCoefficient) hnPow
    have hd := Nat.mul_le_mul_left 512 hxPow
    nlinarith
  have hcap : capacity (payload nodes suffix) ≤ capacityCoefficient*X^12 := by
    exact Nat.mul_le_mul_left capacityCoefficient (Nat.pow_le_pow_left hN 12)
  have hmX : nodes.length ≤ X := by omega
  have hX12 : X^12 ≤ X^13 := Nat.pow_le_pow_right hX (by decide)
  have hX13 : X ≤ X^13 := by simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ 13 by decide)
  have hone : 1 ≤ X^13 := Nat.one_le_pow _ _ hX
  have hloop : PCPPRequestNodeList.budget (capacity (payload nodes suffix)) nodes.length ≤
      (8*capacityCoefficient+15)*X^13+8 := by
    unfold PCPPRequestNodeList.budget
    calc
      _ ≤ 2*(capacityCoefficient*X^12)+X*(6*(capacityCoefficient*X^12)+15)+8 := by gcongr
      _ = 2*capacityCoefficient*X^12+6*capacityCoefficient*X^13+15*X+8 := by ring
      _ ≤ (8*capacityCoefficient+15)*X^13+8 := by nlinarith
  change _ ≤ coldCoefficient*X^13
  unfold coldBudget PCPPRequestNodeGlobal.budget coldCoefficient
  nlinarith

theorem mass_le_cold {n : ℕ} (nodes : List (BooleanNode n)) (suffix : List Bool) :
    PCPSerializerMass.mass (PCPPRequestCircuitNodes.fields nodes) ≤ coldBudget nodes suffix := by
  obtain ⟨r,hr,_,hh,_,_,_,_,_,_,hs⟩ := cold_run nodes suffix
  have hp := (prefix_of_run coldMachine _ _ r hr).1
  have h : r.final.heads (outputSlot 12) ≤ r.steps := by
    simpa only [initialConfiguration,Nat.zero_add] using SelectiveReset.prefix_head hp (outputSlot 12)
  have he : (PCPPRequestNodeLoop.encoded nodes).length=
      PCPSerializerMass.mass (PCPPRequestCircuitNodes.fields nodes) := by
    exact PCPTraversal.stream_mass (PCPPRequestCircuitNodes.fields nodes)
  rw [hh] at h
  rw [he] at h
  exact h.trans hs

end NearCubicWires.RepairOrdinary.PCPPRequestRuntime
