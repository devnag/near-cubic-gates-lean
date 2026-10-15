import Proof.PCP.PCPPNativeNodeNotRetained
import Proof.PCP.PCPPNativeDescriptor

/-! Exact retained projection-row cache and the literal two-node output
of the already verified shared-DAG substitution. These identities dock
the executed branch callers to the typed oracle/node loop. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open RepairRepresentation SourceInterfaces RepairSource
open ProjectionNormalization PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowFields {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) :=
  List.ofFn fun i => (projectionCode (projection i)).bits
def rowCache {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) := FieldList.stream (rowFields projection)
def rowBefore {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) (i : Fin n) := (rowFields projection).take i.val
def rowAfter {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) (i : Fin n) :=
  FieldList.stream ((rowFields projection).drop (i.val+1))

theorem row_before_length {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) (i : Fin n) :
    (rowBefore projection i).length=i.val := by
  simp only [rowBefore,rowFields,List.length_take,List.length_ofFn]
  exact Nat.min_eq_left (by omega)

theorem row_split {n r : ℕ} (projection : Fin n → ProjectedRandomBit r) (i : Fin n) :
    rowCache projection=FieldList.stream (rowBefore projection i)++
      frame (projectionCode (projection i)).bits++rowAfter projection i := by
  have hi : i.val < (rowFields projection).length := by simpa only [rowFields,List.length_ofFn] using i.isLt
  have hs : rowFields projection=(rowFields projection).take i.val++
      (rowFields projection)[i.val]::(rowFields projection).drop (i.val+1) := by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have h := congrArg FieldList.stream hs
  simpa only [rowCache,rowBefore,rowAfter,rowFields,List.getElem_ofFn,FieldList.stream,
    List.map_append,List.map_cons,List.flatten_append,List.flatten_cons,List.append_assoc] using h

def originalSource {n : ℕ} (pre tail : List Bool) (node : BooleanNode n) :=
  pre++PCPPRequestNodeSchema.native node++tail
def emittedNode {n r : ℕ} (base index : ℕ) (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) :=
  PCPPRequestNodeSchema.native (firstNode projection node)++
    PCPPRequestNodeSchema.native (secondNode base index projection node)

theorem original_source {n : ℕ} (pre tail : List Bool) (node : BooleanNode n) :
    originalSource pre tail node=PCPPNativeNodeRead.source pre tail (PCPPRequestNodeSchema.tag node).val
      (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2) := by
  rw [originalSource,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.first_tag]
  simp only [PCPPNativeNodeRead.source,List.append_assoc]

def nodeBudget {n r : ℕ} (base index C : ℕ) (projection : Fin n → ProjectedRandomBit r) : BooleanNode n → ℕ
  | .const b => constBudget b
  | .not j => notBudget j base C
  | .and j k => binaryBudget false j k base C
  | .or j k => binaryBudget true j k base C
  | .input i => match projection i with
    | .constant b => projectedConstBudget r (rowBefore projection i) b
    | .bit j => projectedInputBudget (rowBefore projection i) false j (base+2*index) C
    | .negatedBit j => projectedInputBudget (rowBefore projection i) true j (base+2*index) C

def nodeCapacity {n r : ℕ} (base index C : ℕ) (projection : Fin n → ProjectedRandomBit r) : BooleanNode n → Prop
  | .const _ => True
  | .not j => PCPPNativeAddressAppend.budget base j+1 ≤ C
  | .and j k | .or j k => PCPPNativeAddressAppend.budget base j+1 ≤ C ∧ PCPPNativeAddressAppend.budget base k+1 ≤ C
  | .input i => match projection i with
    | .constant _ => True
    | .bit j | .negatedBit j => PCPPNativeSumAppend.budget 0 j.val+1 ≤ C ∧
        PCPPNativeSumAppend.budget 0 (base+2*index)+1 ≤ C

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
