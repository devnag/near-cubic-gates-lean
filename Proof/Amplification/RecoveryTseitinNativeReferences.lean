import Proof.Amplification.RecoveryTseitinReferenceBound
import Proof.Amplification.RecoveryTseitinNodeEndpoint
import Proof.PCP.PCPPRequestNodeSchema

/-! Select the physically generated references demanded by each original
node clause. The unused operands never impose spurious zero-reference work. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open RecoveryTseitinReferences CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def referencePorts (k : Fin 6) : Fin 3→Fin 4 := if k=2 then ![0,1,3] else ![0,2,3]
theorem reference_ports_injective (k : Fin 6) : Function.Injective (referencePorts k) := by
  fin_cases k <;> decide
def nativeReferences {n : Nat} (index : Nat) (node : BooleanNode n) : Fin 3→Nat :=
  fun j=>counts n index (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)
    (referencePorts (kind node) j)

theorem native_used {n : Nat} (index : Nat) (node : BooleanNode n) (p : Plan)
    (hp : p∈plans (kind node)) : indices (nativeReferences index node) p=indices (references index node) p := by
  cases node with
  | const b=>cases b <;> simp [kind,plans] at hp <;> subst p <;> rfl
  | input i=>
    simp [kind,plans] at hp
    rcases hp with rfl|rfl <;> funext j <;> fin_cases j <;> rfl
  | not i=>
    simp [kind,plans] at hp
    rcases hp with rfl|rfl <;> funext j <;> fin_cases j <;> rfl
  | and i j=>
    simp [kind,plans] at hp
    rcases hp with rfl|rfl|rfl <;> funext k <;> fin_cases k <;> rfl
  | or i j=>
    simp [kind,plans] at hp
    rcases hp with rfl|rfl|rfl <;> funext k <;> fin_cases k <;> rfl

theorem native_original {n : Nat} (index : Nat) (node : BooleanNode n) :
    formula (nativeReferences index node) (plans (kind node))=circuitInputNodeClauses index node := by
  rw [←original_node index node]
  apply List.map_congr_left
  intro p hp
  unfold clause
  rw [native_used index node p hp]

theorem native_reference_fields {n : Nat} (index : Nat) (node : BooleanNode n) (j : Fin 3) :
    RecoveryTseitinReferences.fields n index (PCPPRequestNodeSchema.fields node 1)
      (PCPPRequestNodeSchema.fields node 2) (referencePorts (kind node) j)=
      ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (nativeReferences index node j))
        (RepairOrdinary.frame (nativeReferences index node j).bits) := rfl

end NearCubicWires.RepairSource.RecoveryTseitinNode
