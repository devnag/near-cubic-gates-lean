import Proof.MachineModel.OrdinaryMatrixScoreWeightLoop
import Proof.MachineModel.OrdinaryMatrixScoreBounds

/-! Literal request-to-executed-weight-loop correspondence. The source is
exactly the nested sign/magnitude fields, and the assignment is the actual
framed binary counter word in least-significant-bit order. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreCanonical
open LocalBitMultitape SignedSortKey MatrixScoreWeightList
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def item (p assignment : ℕ) (wi : ℤ×ℕ) : Item :=
  ⟨decide (wi.1<0),binary p wi.1.natAbs,assignment.testBit wi.2⟩
def items (p assignment : ℕ) (weights : List ℤ) := weights.zipIdx.map (item p assignment)

@[simp] theorem items_length (p assignment : ℕ) (weights : List ℤ) :
    (items p assignment weights).length=weights.length := by simp [items]

theorem word_items (p assignment : ℕ) (weights : List ℤ) :
    word (items p assignment weights)=weights.flatMap (fun w => frame (MatrixScoreBatch.signMagnitude p w)) := by
  have h := congrArg (fun xs : List ℤ => xs.flatMap (fun w => frame (MatrixScoreBatch.signMagnitude p w)))
    (List.zipIdx_map_fst 0 weights)
  simpa only [word,items,item,Item.word,MatrixScoreBatch.signMagnitude,List.flatMap_map,Function.comp_apply] using h

theorem binary_testBit (w n i : ℕ) (hi : i<w) :
    (binary w n)[i]'(by simpa using hi)=n.testBit i := by
  induction w generalizing n i with
  | zero => omega
  | succ w ih =>
    cases i with
    | zero =>
      simp only [binary,List.getElem_cons_zero,Nat.testBit_zero]
      by_cases h : n%2=1 <;> simp [h]
    | succ i => simpa only [binary,List.getElem_cons_succ,Nat.testBit_succ] using ih (n/2) i (by omega)

theorem assignment_items (p n : ℕ) (weights : List ℤ) :
    assignment (items p n weights)=Streaming.marks (binary weights.length n) := by
  have h : weights.zipIdx.map (fun wi => n.testBit wi.2)=binary weights.length n := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp only [List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
    exact (binary_testBit weights.length n i (by simpa using hi)).symm
  rw [← h]
  simp [assignment,items,item,Item.assignment,Streaming.marks,List.flatMap_map]

theorem magnitude_width (p n : ℕ) (weights : List ℤ) :
    ∀ e ∈ items p n weights,e.magnitude.length≤p := by
  intro e he
  obtain ⟨wi,_,rfl⟩ := List.mem_map.mp he
  simp [item]

theorem positive_items (p n : ℕ) (weights : List ℤ) (hf : ∀ w ∈ weights,w.natAbs<2^p) :
    positive (items p n weights)=MatrixScoreBatch.part false weights n := by
  unfold positive items MatrixScoreBatch.part
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro wi hwi
  have h := hf wi.1 (List.fst_mem_of_mem_zipIdx hwi)
  simp [item,Item.positive,MatrixScoreBatch.term,binary_value p wi.1.natAbs h]

theorem negative_items (p n : ℕ) (weights : List ℤ) (hf : ∀ w ∈ weights,w.natAbs<2^p) :
    negative (items p n weights)=MatrixScoreBatch.part true weights n := by
  unfold negative items MatrixScoreBatch.part
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro wi hwi
  have h := hf wi.1 (List.fst_mem_of_mem_zipIdx hwi)
  simp [item,Item.negative,MatrixScoreBatch.term,binary_value p wi.1.natAbs h]

end NearCubicWires.RepairOrdinary.MatrixScoreCanonical
