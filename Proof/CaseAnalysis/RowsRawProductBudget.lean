import Proof.CaseAnalysis.RowsRawProductLoop

/-! One polynomial preparation envelope for the actual ordered-stream product.
The width is the logical encoded input, independent of allocated padding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBudget
open CloseoutRowsRawProductLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputLength (left right : List (List ℕ)) :=
  (ExtIncidence.stream left).length+(ExtIncidence.stream right).length
def capacity (left right : List (List ℕ)):=64*(inputLength left right+2)^2

theorem monomial_le (left : List (List ℕ)) (l : List ℕ) (hl : l∈left) :
    (l.flatMap ExtIncidence.block).length+1≤(ExtIncidence.stream left).length := by
  induction left with
  | nil=>simp at hl
  | cons m left ih=>
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
    rcases List.mem_cons.mp hl with rfl|hl
    · omega
    · have h:=ih hl;omega

theorem count_le (left : List (List ℕ)) : left.length≤(ExtIncidence.stream left).length := by
  induction left with
  | nil=>simp
  | cons l left ih=>
    rw [List.length_cons,ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
    omega

theorem row_bound (l : List ℕ) (right : List (List ℕ)) :
    CloseoutRowsRawProductRow.budget l right≤
      16*((l.flatMap ExtIncidence.block).length+1)*((ExtIncidence.stream right).length+1) := by
  induction right with
  | nil=>simp [CloseoutRowsRawProductRow.budget,ExtIncidence.stream];omega
  | cons r right ih=>
    simp only [CloseoutRowsRawProductRow.budget,List.map_cons,List.sum_cons] at ih ⊢
    rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
    unfold CloseoutRowsRawProductPair.budget at ih ⊢
    nlinarith

theorem capacity_fits (left right : List (List ℕ)) :
    (∀ l∈left,(l.flatMap ExtIncidence.block).length+1≤capacity left right) ∧
    (∀ l∈left,CloseoutRowsRawProductRow.budget l right≤capacity left right) := by
  constructor
  · intro l hl
    have h:=monomial_le left l hl
    have hp:=Nat.mul_le_mul_right (inputLength left right+2)
      (show 1 ≤ inputLength left right+2 by omega)
    unfold capacity inputLength at *
    nlinarith
  · intro l hl
    have h:=monomial_le left l hl
    have r:=row_bound l right
    have hm:=Nat.mul_le_mul_right ((ExtIncidence.stream right).length+1)
      (Nat.mul_le_mul_left 16 h)
    unfold capacity inputLength
    nlinarith

theorem budget_bound (left right : List (List ℕ)) :
    budget (capacity left right) left.length≤256*(inputLength left right+2)^3 := by
  have h:=count_le left
  have hn : left.length ≤ inputLength left right:=by unfold inputLength;omega
  have hm:=Nat.mul_le_mul_right (3*capacity left right+7) hn
  unfold budget capacity at *
  nlinarith [Nat.zero_le ((inputLength left right+2)^2)]

theorem row_length (l : List ℕ) (right : List (List ℕ)) :
    (CloseoutRowsRawProductRow.word l right).length≤
      (ExtIncidence.monomialWord l).length*(ExtIncidence.stream right).length := by
  induction right with
  | nil=>simp [CloseoutRowsRawProductRow.word]
  | cons r right ih=>
    simp only [CloseoutRowsRawProductRow.word,List.map_cons,List.flatMap_cons,List.length_append] at ih ⊢
    rw [ExtIncidence.stream_cons,List.length_append]
    simp only [ExtIncidence.monomialWord_length,List.flatMap_append,List.length_append] at ih ⊢
    nlinarith

theorem product_length (left right : List (List ℕ)) :
    (ExtIncidence.stream (product left right)).length≤
      (ExtIncidence.stream left).length*(ExtIncidence.stream right).length+1 := by
  induction left with
  | nil=>simp [product,ExtIncidence.stream]
  | cons l left ih=>
    have h:=row_length l right
    simp only [ExtIncidence.stream,product,List.flatMap_cons,List.flatMap_append,
      List.length_append,List.length_singleton] at ih ⊢
    simp only [CloseoutRowsRawProductRow.word] at h
    have hr:0<(ExtIncidence.stream right).length:=by simp [ExtIncidence.stream]
    simp only [ExtIncidence.stream,List.length_append,List.length_singleton] at h hr
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBudget
