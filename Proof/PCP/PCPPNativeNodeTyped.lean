import Proof.PCP.PCPPNativeNodeTypedInput

/-! Every typed native node runs through the same fixed finite controller
on its original bytes and the retained encoded projection row. The exact
two-node shared-DAG substitution and live loop counters are returned. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource
open ProjectionNormalization PCPPSubstitution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem typed_node_run {n r : ℕ} (pre tail : List Bool) (base index C : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool)
    (hC : nodeCapacity base index C projection node) :
    ∃ result,runFrom machine (nodeBudget base index C projection node)
      (entry (originalSource pre tail node) (rowCache projection) pre.length base (base+2*index) C out)=some result ∧
      result.steps ≤ nodeBudget base index C projection node ∧
      nodeResult pre tail base index C projection node out result.final.heads result.final.tapes := by
  cases node with
  | input i => exact typed_input_run pre tail base index C projection i out hC
  | const b =>
    have sourceEq : originalSource pre tail (.const b : BooleanNode n)=PCPPNativeNodeRead.source pre tail 0 b.toNat 0 :=
      original_source pre tail (.const b : BooleanNode n)
    have headEq : pre.length+(PCPPRequestNodeSchema.native (.const b : BooleanNode n)).length=
        pre.length+(natWord 0).length+(natWord b.toNat).length+(natWord 0).length := by
      simp [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.length_append,Nat.add_assoc]
    have outputEq : emittedNode base index projection (.const b)=constBits false b := rfl
    obtain ⟨a,ha,as,a0,ah0,a5,ah5,ak⟩ := const_run pre tail (rowCache projection) b base (base+2*index) C out
    refine ⟨a,?_,as,?_,?_,?_,?_,?_,?_⟩
    · simpa only [nodeBudget,sourceEq] using ha
    · exact a0.trans sourceEq.symm
    · exact ah0.trans headEq.symm
    · exact (ak 1 (by decide) (by decide)).2
    · rw [outputEq]; exact a5
    · rw [outputEq]; exact ah5
    · intro i
      fin_cases i
      · exact ak 2 (by decide) (by decide)
      · exact ak 3 (by decide) (by decide)
      · exact ak 4 (by decide) (by decide)
  | not j =>
    have sourceEq : originalSource pre tail (.not j : BooleanNode n)=PCPPNativeNodeRead.source pre tail 2 j 0 :=
      original_source pre tail (.not j : BooleanNode n)
    have headEq : pre.length+(PCPPRequestNodeSchema.native (.not j : BooleanNode n)).length=
        pre.length+(natWord 2).length+(natWord j).length+(natWord 0).length := by
      simp [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.length_append,Nat.add_assoc]
    have outputEq : emittedNode base index projection (.not j)=PCPPNativeNotNode.emitted base j := by
      rw [PCPPNativeNotNode.emitted_nodes r]
      rfl
    obtain ⟨a,ha,as,a0,ah0,a5,ah5,af,ak⟩ := not_retained_run pre tail (rowCache projection) j base (base+2*index) C out hC
    refine ⟨a,?_,as,?_,?_,?_,?_,?_,?_⟩
    · simpa only [nodeBudget,sourceEq] using ha
    · exact a0.trans sourceEq.symm
    · exact ah0.trans headEq.symm
    · exact (ak 1 (by decide) (by decide) (by decide)).2
    · rw [outputEq]; exact a5
    · rw [outputEq]; exact ah5
    · intro i
      fin_cases i
      · exact af 0
      · exact ak 3 (by decide) (by decide) (by decide)
      · exact af 22
  | and j k =>
    have sourceEq : originalSource pre tail (.and j k : BooleanNode n)=PCPPNativeNodeRead.source pre tail 3 j k :=
      original_source pre tail (.and j k : BooleanNode n)
    have headEq : pre.length+(PCPPRequestNodeSchema.native (.and j k : BooleanNode n)).length=
        pre.length+(natWord 3).length+(natWord j).length+(natWord k).length := by
      simp [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.length_append,Nat.add_assoc]
    have outputEq : emittedNode base index projection (.and j k)=PCPPNativeBinary.emitted false base j k := by
      rw [PCPPNativeBinary.emitted_nodes r]
      rfl
    obtain ⟨a,ha,as,a0,ah0,af,ak⟩ := binary_run pre tail (rowCache projection) false j k base (base+2*index) C out hC.1 hC.2
    refine ⟨a,?_,as,?_,?_,?_,?_,?_,?_⟩
    · rw [show (binaryTag false).val=3 by rfl] at ha
      simpa only [nodeBudget,sourceEq] using ha
    · exact a0.trans sourceEq.symm
    · exact ah0.trans headEq.symm
    · exact (ak 1 (by decide) (by decide) (by decide) (by decide)).2
    · rw [outputEq]; exact (af 20).2
    · rw [outputEq]; exact (af 20).1
    · intro i
      fin_cases i
      · exact af 0
      · exact ak 3 (by decide) (by decide) (by decide) (by decide)
      · exact af 22
  | or j k =>
    have sourceEq : originalSource pre tail (.or j k : BooleanNode n)=PCPPNativeNodeRead.source pre tail 4 j k :=
      original_source pre tail (.or j k : BooleanNode n)
    have headEq : pre.length+(PCPPRequestNodeSchema.native (.or j k : BooleanNode n)).length=
        pre.length+(natWord 4).length+(natWord j).length+(natWord k).length := by
      simp [PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.length_append,Nat.add_assoc]
    have outputEq : emittedNode base index projection (.or j k)=PCPPNativeBinary.emitted true base j k := by
      rw [PCPPNativeBinary.emitted_nodes r]
      rfl
    obtain ⟨a,ha,as,a0,ah0,af,ak⟩ := binary_run pre tail (rowCache projection) true j k base (base+2*index) C out hC.1 hC.2
    refine ⟨a,?_,as,?_,?_,?_,?_,?_,?_⟩
    · rw [show (binaryTag true).val=4 by rfl] at ha
      simpa only [nodeBudget,sourceEq] using ha
    · exact a0.trans sourceEq.symm
    · exact ah0.trans headEq.symm
    · exact (ak 1 (by decide) (by decide) (by decide) (by decide)).2
    · rw [outputEq]; exact (af 20).2
    · rw [outputEq]; exact (af 20).1
    · intro i
      fin_cases i
      · exact af 0
      · exact ak 3 (by decide) (by decide) (by decide) (by decide)
      · exact af 22

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
