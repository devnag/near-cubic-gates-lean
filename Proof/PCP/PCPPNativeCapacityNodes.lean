import Proof.PCP.PCPPNativeCapacityScalars

/-! Discharge the native node controller's scalar obligations from the
actual row cache, source arity and current node position. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCapacity
open SourceInterfaces RepairRepresentation RepairSource ProjectionNormalization PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_prefix {n r : ℕ} (projection : Fin n → ProjectedRandomBit r)
    (i : Fin n) (W C : ℕ) (hW : 4 ≤ W) (hn : n ≤ W) (hr : r ≤ W)
    (hrow : (rowCache projection).length ≤ W) (hC : 4096*(W+1)^2 ≤ C) :
    projectionPrefixBudget (rowBefore projection i) (projection i) ≤ 11*C := by
  have hs' := congrArg List.length (row_split projection i)
  rw [List.length_append,List.length_append,frame_length] at hs'
  apply projection_prefix (rowBefore projection i) (projection i) W C hW
  · rw [row_before_length]; omega
  · omega
  · omega
  · cases hp : projection i with
    | bit j => simp only [PCPPNativeProjectionTyped.index]; omega
    | negatedBit j => simp only [PCPPNativeProjectionTyped.index]; omega
    | constant b => cases b <;> simp [PCPPNativeProjectionTyped.index]; omega
  · exact hC

theorem binary_budget (isOr : Bool) (a b base W C : ℕ) (hW : 4 ≤ W)
    (ha : base+a ≤ W) (hb : base+b ≤ W) (hC : 4096*(W+1)^2 ≤ C) :
    binaryBudget isOr a b base C+1 ≤ 16*C := by
  have hc := classify (binaryTag isOr) a b W C hW (by omega) (by omega) hC
  have hla := reusable_address base a C (address base a W C ha hC)
  have hlb := reusable_address base b C (address base b W C hb hC)
  have hl := linear W C hC
  unfold binaryBudget PCPPNativeBinary.budget
  cases isOr <;>
    norm_num [PCPPNativeBinary.firstBits,PCPPRequestNodeSchema.native,
      PCPPRequestNodeSchema.fields,natWord,natBitLength,Fin.isValue,List.cons_append,List.nil_append,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> omega

theorem not_budget (a base W C : ℕ) (hW : 4 ≤ W)
    (ha : base+a ≤ W) (hC : 4096*(W+1)^2 ≤ C) : notBudget a base C+1 ≤ 8*C := by
  have hc := classify 2 a 0 W C hW (by omega) (by omega) hC
  have hla := reusable_address base a C (address base a W C ha hC)
  have hl := linear W C hC
  unfold notBudget PCPPNativeNotNode.budget
  norm_num [PCPPNativeNotNode.firstBits,PCPPNativeNotNode.lastBits,
    PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,natWord,natBitLength,Fin.isValue,List.cons_append,List.nil_append,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  omega

theorem node_bounds {n r : ℕ} (projection : Fin n → ProjectedRandomBit r)
    (node : BooleanNode n) (base index W C : ℕ) (hW : 4 ≤ W)
    (hn : n ≤ W) (hr : r ≤ W) (hrow : (rowCache projection).length ≤ W)
    (hp : base+2*index ≤ W) (hnode : node.WellFormedAt index)
    (hC : 4096*(W+1)^2 ≤ C) :
    nodeCapacity base index C projection node ∧ nodeBudget base index C projection node+1 ≤ 32*C := by
  have hl := linear W C hC
  cases node with
  | const b =>
    refine ⟨trivial,?_⟩
    have hc := classify 0 b.toNat 0 W C hW (by cases b <;> simp; omega) (by omega) hC
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] at hc <;> norm_num [nodeBudget,constBudget,constBits,PCPPRequestNodeSchema.native,
      PCPPRequestNodeSchema.fields,natWord,natBitLength,Fin.isValue,List.cons_append,List.nil_append,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> omega
  | not a =>
    have ha : base+a ≤ W := by simp only [BooleanNode.WellFormedAt] at hnode; omega
    exact ⟨address base a W C ha hC,by have h := not_budget a base W C hW ha hC; exact le_trans h (by omega)⟩
  | and a b =>
    have ha : base+a ≤ W := by simp only [BooleanNode.WellFormedAt] at hnode; omega
    have hb : base+b ≤ W := by simp only [BooleanNode.WellFormedAt] at hnode; omega
    exact ⟨⟨address base a W C ha hC,address base b W C hb hC⟩,
      by have h := binary_budget false a b base W C hW ha hb hC; exact le_trans h (by omega)⟩
  | or a b =>
    have ha : base+a ≤ W := by simp only [BooleanNode.WellFormedAt] at hnode; omega
    have hb : base+b ≤ W := by simp only [BooleanNode.WellFormedAt] at hnode; omega
    exact ⟨⟨address base a W C ha hC,address base b W C hb hC⟩,
      by have h := binary_budget true a b base W C hW ha hb hC; exact le_trans h (by omega)⟩
  | input i =>
    have hx := row_prefix projection i W C hW hn hr hrow hC
    have hs := sum 0 (base+2*index) W C (by omega) hC
    cases hi : projection i with
    | bit j =>
      have hj := sum 0 j.val W C (by omega) hC
      have he := input_emit false j.val (base+2*index) C hj hs
      refine ⟨by simpa only [nodeCapacity,hi] using And.intro hj hs,?_⟩
      simp only [hi] at hx
      simp only [nodeBudget,hi,projectedInputBudget,inputProjection,inputKind,Bool.false_eq_true,ite_false]
      omega
    | negatedBit j =>
      have hj := sum 0 j.val W C (by omega) hC
      have he := input_emit true j.val (base+2*index) C hj hs
      refine ⟨by simpa only [nodeCapacity,hi] using And.intro hj hs,?_⟩
      simp only [hi] at hx
      simp only [nodeBudget,hi,projectedInputBudget,inputProjection,inputKind,ite_true]
      omega
    | constant b =>
      refine ⟨by simp only [nodeCapacity,hi],?_⟩
      simp only [hi] at hx
      cases b <;> norm_num [nodeBudget,hi,projectedConstBudget,constBits,
        PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,natWord,natBitLength,Fin.isValue,List.cons_append,List.nil_append,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] <;> omega

end NearCubicWires.RepairOrdinary.PCPPNativeCapacity
