import Proof.Circuits.DecompositionInputBudget
import Proof.Circuits.DecompositionNativeSemantics

/-! The whole executed nesting and cold preparation have one polynomial
bound. Each charge below comes from its actual checked machine receipt. -/
namespace NearCubicWires.RepairOrdinary.DecompositionResource
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem nesting_budget (E N : ℕ) (groups : List (List ℤ))
    (hE : 1 ≤ E) (hT : groups.flatten.length ≤ N) (hm : groups.length ≤ N)
    (ho : PCPTraversal.budget (PCPSerializerMass.mass
      (DecompositionCodeBounds.childFields groups)) ≤ E) :
    DecompositionNesting.budget E groups ≤ 128*E*(N+1) := by
  have hET := Nat.mul_le_mul_left E hT
  have hEm := Nat.mul_le_mul_left E hm
  have hEN : N ≤ E*N := by nlinarith
  unfold DecompositionNesting.budget DecompositionAtomStreamReady.budget
    DecompositionAtomCold.budget DecompositionChildOuter.budget
    DecompositionChildStreamReady.budget DecompositionGroupsCold.budget
  rw [DecompositionNesting.child_fields]
  simp only [DecompositionNesting.fieldGroups,List.length_map]
  nlinarith

def coefficient (D C : ℕ) := PCPSerializerCapacity.coefficient D C+128*C+1028

theorem global_budget (D C E a N : ℕ) (groups : List (List ℤ))
    (hN : (frame (DecompositionInputCounts.word a groups.length
      (DecompositionAtomLoop.stream groups.flatten))).length=N)
    (hE : E=C*(N+1)^D) (hC : 1 ≤ E)
    (hT : groups.flatten.length ≤ N) (hm : groups.length ≤ N)
    (ho : PCPTraversal.budget (PCPSerializerMass.mass
      (DecompositionCodeBounds.childFields groups)) ≤ E) :
    DecompositionGlobal.budget D C E a groups ≤ coefficient D C*(a+N+1)^(D+2) := by
  have hp := cold_budget D C a groups.length N (DecompositionAtomLoop.stream groups.flatten) hN hm
  have hn := nesting_budget E N groups hC hT hm ho
  have hbase : 1 ≤ a+N+1 := by omega
  have hexp : (N+1)^(D+1) ≤ (a+N+1)^(D+2) := by
    calc
      _ ≤ (a+N+1)^(D+1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ _ := Nat.pow_le_pow_right hbase (by omega)
  have hsquare : (a+N+1)^2 ≤ (a+N+1)^(D+2) := Nat.pow_le_pow_right hbase (by omega)
  have hone : 1 ≤ (a+N+1)^(D+2) := Nat.one_le_pow _ _ hbase
  have hen : 128*E*(N+1)=128*C*(N+1)^(D+1) := by rw [hE,pow_succ]; ring
  rw [hen] at hn
  have hpc := Nat.mul_le_mul_left (PCPSerializerCapacity.coefficient D C) hexp
  have hnc := Nat.mul_le_mul_left (128*C) hexp
  unfold DecompositionGlobal.budget coefficient
  nlinarith

end NearCubicWires.RepairOrdinary.DecompositionResource
