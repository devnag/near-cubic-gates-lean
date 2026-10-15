import Proof.CaseAnalysis.RowsGateRun

/-! The complete native append/framing work is quadratic in the actual
raw gate width. The already paid degree26 field decoder dominates it. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeBudget
open LocalBitMultitape CloseoutRowsGateSupport CloseoutRowsGateNative
open RepairRepresentation RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem weights_length (compressed : Bool) (fields : List (Bool×List Bool)) (membership : List Bool)
    (w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) :
    (weights compressed fields membership).length ≤ fields.length*(2*w+2) := by
  rw [weights,List.length_flatMap]
  have h := List.sum_le_card_nsmul ((List.range fields.length).map
    (fun j => (emission compressed fields membership j).length)) (2*w+2) (by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      have hj' := List.mem_range.mp hj
      have hf := hw (fields.getD j (false,[])) (by
        rw [List.getD_eq_getElem _ _ hj'];exact List.getElem_mem hj')
      have hl : (fieldWord (fields.getD j (false,[]))).length ≤ 2*w+2 := by
        simp only [fieldWord,weightWord,List.length_cons,List.length_append,List.length_replicate]
        omega
      unfold emission selected PCPPQueryField.selected
      split_ifs
      · exact hl
      · simp)
  simpa only [List.length_map,List.length_range,smul_eq_mul] using h

theorem word_length (compressed : Bool) (fields : List (Bool×List Bool)) (membership source : List Bool)
    (n w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) :
    (word compressed fields membership source n).length ≤
      2*arity compressed fields membership+3+fields.length*(2*w+2)+2*n.bits.length+6 := by
  have ha : natBitLength (arity compressed fields membership) ≤ arity compressed fields membership+1 :=
    Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hm := PCPSerializerMass.value_width (CloseoutRowsStrictThreshold.magnitude source n).bits
  rw [CanonicalPositiveOutput.nat_bits_value] at hm
  have hb := CloseoutRowsStrictNative.magnitude_length source n
  have hw' := weights_length compressed fields membership w hw
  simp only [CloseoutRowsGateNative.word,List.length_append,DecompositionSource.natWord_length,CloseoutRowsStrictNative.produced,
    List.length_cons]
  omega

theorem framed_bound (compressed : Bool) (fields : List (Bool×List Bool)) (membership source : List Bool)
    (n B : ℕ) (hf : fields.length ≤ B+1) (hm : membership.length ≤ B+1)
    (hn : n.bits.length ≤ B+1) (hw : ∀ field∈fields,field.2.length ≤ B+2) :
    framedBudget compressed fields membership source n (B+2) ≤ 1000*(B+2)^2 := by
  have har : arity compressed fields membership ≤ B+1 := by
    cases compressed
    · exact hf
    · exact (show CloseoutRowsSupportCount.ones membership ≤ membership.length by
        rw [CloseoutRowsSupportCount.ones_filter];exact List.length_filter_le _ _).trans hm
  have har2 := Nat.pow_le_pow_left har 2
  have hb : natBitLength (arity compressed fields membership) ≤ B+2 :=
    (Nat.add_le_add_right (Nat.log_le_self _ _) 1).trans (by omega)
  have hmul := Nat.mul_le_mul_right (2*(B+2)+7) hf
  have hwMul := Nat.mul_le_mul_right (2*(B+2)+2) hf
  have hword := word_length compressed fields membership source n (B+2) hw
  unfold framedBudget budget CloseoutRowsGateNativePrefix.budget CloseoutRowsGateNativePrefix.countBudget
    EquationHeaderAppend.budget preparedBudget loopBudget CloseoutRowsStrictNative.budget
  change 2*(4*(fields.length+membership.length)+6+1+
    (16*(arity compressed fields membership)^2+72*arity compressed fields membership+
      12*natBitLength (arity compressed fields membership)+58)+1+
    (fields.length*(2*(B+2)+7)+3+2)+1+(26*n.bits.length+69))+
    4*(word compressed fields membership source n).length+7 ≤ _
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeBudget
