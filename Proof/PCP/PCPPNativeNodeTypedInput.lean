import Proof.PCP.PCPPNativeNodeRow

/-! Typed input-node execution on the entire retained row. The selected
projection is found from the original input index in the encoded cache;
the physical base, position and capacity counters survive for repetition. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource
open ProjectionNormalization PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retainedInputs (base position C : ℕ) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool) : Prop :=
  ∀ i : Fin 3,heads (![2,3,4] i)=0 ∧ data (![2,3,4] i)=List.replicate (![base,position,C] i) true
def nodeResult {n r : ℕ} (pre tail : List Bool) (base index C : ℕ) (projection : Fin n → ProjectedRandomBit r)
    (node : BooleanNode n) (out : List Bool) (heads : Fin 119 → ℕ) (data : Fin 119 → List Bool) : Prop :=
  data 0=originalSource pre tail node ∧ heads 0=pre.length+(PCPPRequestNodeSchema.native node).length ∧
    data 1=rowCache projection ∧ data 5=out++emittedNode base index projection node ∧
    heads 5=(out++emittedNode base index projection node).length ∧ retainedInputs base (base+2*index) C heads data

theorem typed_input_run {n r : ℕ} (pre tail : List Bool) (base index C : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (i : Fin n) (out : List Bool)
    (hC : nodeCapacity base index C projection (.input i)) :
    ∃ result,runFrom machine (nodeBudget base index C projection (.input i))
      (entry (originalSource pre tail (.input i)) (rowCache projection) pre.length base (base+2*index) C out)=some result ∧
      result.steps ≤ nodeBudget base index C projection (.input i) ∧
      nodeResult pre tail base index C projection (.input i) out result.final.heads result.final.tapes := by
  have sourceEq : originalSource pre tail (.input i)=PCPPNativeNodeRead.source pre tail 1 i.val 0 := original_source pre tail (.input i)
  have headEq : pre.length+(PCPPRequestNodeSchema.native (.input i)).length=
      pre.length+(natWord 1).length+(natWord i.val).length+(natWord 0).length := by
    simp [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.length_append,Nat.add_assoc]
  cases hp : projection i with
  | bit j =>
    have hc : PCPPNativeSumAppend.budget 0 j.val+1 ≤ C ∧ PCPPNativeSumAppend.budget 0 (base+2*index)+1 ≤ C := by
      simpa only [nodeCapacity,hp] using hC
    have cacheEq : rowCache projection=FieldList.stream (rowBefore projection i)++
        frame (projectionCode (inputProjection false j)).bits++rowAfter projection i := by
      simpa only [hp,inputProjection,Bool.false_eq_true,ite_false] using row_split projection i
    obtain ⟨a,ha,as,a0,ah0,a1,af,ak⟩ := projected_input_run pre tail (rowBefore projection i) false j
      (rowAfter projection i) base (base+2*index) C out hc.1 hc.2
    have outputEq : emittedNode base index projection (.input i)=PCPPNativeInput.emitted false j.val (base+2*index) := by
      rw [PCPPNativeInput.emitted_nodes]
      simp only [emittedNode,firstNode,secondNode,hp,Bool.false_eq_true,ite_false]
    refine ⟨a,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [nodeBudget,hp,sourceEq,row_before_length,←cacheEq] using ha
    · simpa only [nodeBudget,hp] using as
    · simpa only [sourceEq,row_before_length] using a0
    · simpa only [headEq,row_before_length] using ah0
    · exact a1.trans cacheEq.symm
    · rw [outputEq]; exact (af 20).2
    · rw [outputEq]; exact (af 20).1
    · intro k
      fin_cases k
      · exact ak 2 (by decide) (by decide) (by decide) (by decide)
      · exact af 24
      · exact af 22
  | negatedBit j =>
    have hc : PCPPNativeSumAppend.budget 0 j.val+1 ≤ C ∧ PCPPNativeSumAppend.budget 0 (base+2*index)+1 ≤ C := by
      simpa only [nodeCapacity,hp] using hC
    have cacheEq : rowCache projection=FieldList.stream (rowBefore projection i)++
        frame (projectionCode (inputProjection true j)).bits++rowAfter projection i := by
      simpa only [hp,inputProjection,ite_true] using row_split projection i
    obtain ⟨a,ha,as,a0,ah0,a1,af,ak⟩ := projected_input_run pre tail (rowBefore projection i) true j
      (rowAfter projection i) base (base+2*index) C out hc.1 hc.2
    have outputEq : emittedNode base index projection (.input i)=PCPPNativeInput.emitted true j.val (base+2*index) := by
      rw [PCPPNativeInput.emitted_nodes]
      simp only [emittedNode,firstNode,secondNode,hp,ite_true]
    refine ⟨a,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [nodeBudget,hp,sourceEq,row_before_length,←cacheEq] using ha
    · simpa only [nodeBudget,hp] using as
    · simpa only [sourceEq,row_before_length] using a0
    · simpa only [headEq,row_before_length] using ah0
    · exact a1.trans cacheEq.symm
    · rw [outputEq]; exact (af 20).2
    · rw [outputEq]; exact (af 20).1
    · intro k
      fin_cases k
      · exact ak 2 (by decide) (by decide) (by decide) (by decide)
      · exact af 24
      · exact af 22
  | constant b =>
    have cacheEq : rowCache projection=FieldList.stream (rowBefore projection i)++
        frame (projectionCode (.constant b : ProjectedRandomBit r)).bits++rowAfter projection i := by
      simpa only [hp] using row_split projection i
    obtain ⟨a,ha,as,a0,ah0,a1,a5,ah5,ak⟩ := projected_const_run r pre tail (rowBefore projection i) b
      (rowAfter projection i) base (base+2*index) C out
    have outputEq : emittedNode base index projection (.input i)=constBits b b := by
      simp only [emittedNode,firstNode,secondNode,hp,constBits,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields]
    refine ⟨a,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [nodeBudget,hp,sourceEq,row_before_length,←cacheEq] using ha
    · simpa only [nodeBudget,hp] using as
    · simpa only [sourceEq,row_before_length] using a0
    · simpa only [headEq,row_before_length] using ah0
    · exact a1.trans cacheEq.symm
    · rw [outputEq]; exact a5
    · rw [outputEq]; exact ah5
    · intro k
      fin_cases k
      · exact ak 2 (by decide) (by decide) (by decide)
      · exact ak 3 (by decide) (by decide) (by decide)
      · exact ak 4 (by decide) (by decide) (by decide)

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
