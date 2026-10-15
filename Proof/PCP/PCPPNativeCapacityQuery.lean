import Proof.PCP.PCPPNativeCapacityNodes

/-! The original well-formed oracle's entire node/query requirements follow
from its measured dimensions and row bytes, with one common capacity bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacity
open SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem workspace {n r : ℕ} (projection : Fin n → ProjectedRandomBit r)
    (nodes : List (BooleanNode n)) (base index W C F : ℕ) (hW : 4 ≤ W)
    (hn : n ≤ W) (hr : r ≤ W) (hrow : (rowCache projection).length ≤ W)
    (hp : base+2*(index+nodes.length) ≤ W)
    (hwell : ∀ j : Fin nodes.length,(nodes.get j).WellFormedAt (index+j.val))
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) :
    PCPPNativeNodeLoop.workspace base index C F projection nodes := by
  induction nodes generalizing index with
  | nil => trivial
  | cons node nodes ih =>
    have hfirst := hwell ⟨0,by simp⟩
    simp only [List.get_eq_getElem,List.getElem_cons_zero,Nat.add_zero] at hfirst
    have hb := node_bounds projection node base index W C hW hn hr hrow (by simp only [List.length_cons] at hp; omega) hfirst hC
    have hl := linear W C hC
    refine ⟨hb.1,by omega,by simp only [List.length_cons] at hp; omega,?_⟩
    apply ih (index+1) (by simp only [List.length_cons] at hp; omega) _
    intro j
    have h := hwell ⟨j.val+1,by simp only [List.length_cons]; omega⟩
    simpa only [List.get_eq_getElem,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem query_budget {n : ℕ} (oracle : BooleanCircuit n) (base W C F : ℕ)
    (hn : n ≤ W) (hp : base+2*oracle.size ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) :
    PCPPNativeQueryStep.budget base C F oracle+1 ≤ 64*(W+1)*(F+1) := by
  have hs : oracle.size ≤ W := by omega
  have hout : oracle.output.val < oracle.size := oracle.output.isLt
  have ho : oracle.output.val ≤ W := by omega
  have hna := PCPPNativeNodeRead.field_budget n
  have hns := PCPPNativeNodeRead.field_budget oracle.size
  have hno := PCPPNativeNodeRead.field_budget oracle.output.val
  have hpa := Nat.pow_le_pow_left (show n+1 ≤ W+1 by omega) 2
  have hps := Nat.pow_le_pow_left (show oracle.size+1 ≤ W+1 by omega) 2
  have hpo := Nat.pow_le_pow_left (show oracle.output.val+1 ≤ W+1 by omega) 2
  have ht := reusable_address base oracle.output.val C (address base oracle.output.val W C (by omega) hC)
  have hl := linear W C hC
  have hmul : oracle.size*F ≤ W*F := Nat.mul_le_mul_right F hs
  unfold PCPPNativeQueryStep.budget PCPPNativeQuery.budget PCPPNativeQuery.parsedNodesBudget
    PCPPNativeQuery.headerNodesBudget PCPPNativeQueryHeader.budget PCPPNativeQueryTail.budget
  norm_num [PCPPNativeQueryTail.firstBits,PCPPNativeQueryTail.lastBits,natWord,natBitLength]
  nlinarith

theorem query_capacity {n r : ℕ} (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (base W C F G : ℕ)
    (hW : 4 ≤ W) (hn : n ≤ W) (hr : r ≤ W)
    (hrow : (rowCache projection).length ≤ W) (hp : base+2*oracle.size+1 ≤ W)
    (hC : 4096*(W+1)^2 ≤ C) (hF : 32*C ≤ F) (hG : 64*(W+1)*(F+1) ≤ G) :
    C+1 ≤ F ∧ F+1 ≤ G ∧ PCPPNativeQueryIteration.capacity base C F G oracle projection := by
  have hl := linear W C hC
  have hfg : F+1 ≤ 64*(W+1)*(F+1) := by nlinarith
  refine ⟨by omega,by omega,?_,?_,by omega,?_,?_⟩
  · apply workspace projection oracle.nodes base 0 W C F hW hn hr hrow
      (by change base+2*(0+oracle.size) ≤ W; omega) _ hC hF
    intro j
    simpa only [Nat.zero_add] using oracle.wellFormed j
  · apply address base oracle.output.val W C _ hC
    have ho := oracle.output.isLt
    change oracle.output.val < oracle.size at ho
    omega
  · exact le_trans (query_budget oracle base W C F hn (by omega) hC hF) hG
  · have hg : 4*W+4 ≤ 64*(W+1)*(F+1) := by nlinarith
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeCapacity
