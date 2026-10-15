import Proof.PCP.PCPPNativeQueryLoop

/-! The executed outer stream is the native encoding of the original
shared queryBank construction, in the original projection-row order. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
open SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem emitted_zipIdx {n r : ℕ} (base index : ℕ) (oracle : BooleanCircuit n)
    (rows : List (Fin n → ProjectedRandomBit r)) :
    emitted base index oracle rows=(rows.zipIdx index).flatMap fun p =>
      PCPPNativeQuery.emitted (base+p.2*(2*oracle.size+1)) oracle p.1 := by
  induction rows generalizing index with
  | nil => rfl
  | cons projection rows ih => simp only [emitted,List.zipIdx_cons,List.flatMap_cons,ih]
theorem row_zipIdx {n r : ℕ} (rows : List (Fin n → ProjectedRandomBit r)) :
    rows.zipIdx=(List.range rows.length).map fun i => ((rows[i]?).getD (fun _ => .constant false),i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < rows.length := by simpa only [List.length_zipIdx] using hi
    simp only [List.getElem_zipIdx,List.getElem_map,List.getElem_range,List.getElem?_eq_getElem h,Option.getD_some,Nat.zero_add]
theorem emitted_queryNodes {n r q : ℕ} (base : ℕ) (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) :
    emitted base 0 oracle (List.ofFn projections)=
      (PCPPNative.queryNodesPrefix base oracle projections q).flatMap PCPPRequestNodeSchema.native := by
  rw [emitted_zipIdx,row_zipIdx,List.flatMap_map]
  simp only [PCPPNative.queryNodesPrefix,List.length_ofFn,List.flatMap_assoc,PCPPNativeQuery.emitted]

end NearCubicWires.RepairOrdinary.PCPPNativeQueryLoop
