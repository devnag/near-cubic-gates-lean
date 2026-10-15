import Proof.Hierarchy.CompetitorCountProducerHeads
import Proof.MachineModel.OrdinaryMatrixMaskAndPass

/-! A residual-offset selector masks each complete natural-count cell.
The selector is one actual bit per cropped row-major column; duplicating it
over the binary cell selects the count or zero without changing order. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountMask
open SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (xs : List (Bool × ℕ)) := xs.map (fun x => if x.1 then x.2 else 0)
def mask (xs : List (Bool × ℕ)) := xs.map Prod.fst
def counts (xs : List (Bool × ℕ)) := xs.map Prod.snd

theorem and_replicate (flag : Bool) (bits : List Bool) :
    MatrixMaskAndRow.values ((List.replicate bits.length flag).zip bits)=bits.map (fun b => flag && b) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.length_cons,List.replicate_succ,List.zip_cons_cons,MatrixMaskAndRow.values,List.map_cons] at *
    rw [ih]

theorem and_binary (flag : Bool) (Q n : ℕ) :
    MatrixMaskAndRow.values ((List.replicate Q flag).zip (binary Q n))=binary Q (if flag then n else 0) := by
  have h := and_replicate flag (binary Q n)
  rw [binary_length] at h
  rw [h]
  cases flag
  · simp [RankCarrier.binary_zero]
  · simp

theorem selected_length (xs : List (Bool × ℕ)) : (selected xs).length=xs.length := by simp [selected]
theorem mask_length (xs : List (Bool × ℕ)) : (mask xs).length=xs.length := by simp [mask]
theorem counts_length (xs : List (Bool × ℕ)) : (counts xs).length=xs.length := by simp [counts]

theorem selected_word (Q : ℕ) (xs : List (Bool × ℕ)) :
    MatrixMaskAndRow.values ((MatrixMaskExpand.output Q (mask xs)).zip (CompetitorCountFold.raw Q (counts xs)))=
      CompetitorCountFold.raw Q (selected xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change MatrixMaskAndRow.values
      ((List.replicate Q x.1++MatrixMaskExpand.output Q (mask xs)).zip
        (binary Q x.2++CompetitorCountFold.raw Q (counts xs)))=
      binary Q (if x.1 then x.2 else 0)++CompetitorCountFold.raw Q (selected xs)
    rw [List.zip_append (by simp)]
    simp only [MatrixMaskAndRow.values,List.map_append]
    change MatrixMaskAndRow.values ((List.replicate Q x.1).zip (binary Q x.2))++
      MatrixMaskAndRow.values ((MatrixMaskExpand.output Q (mask xs)).zip (CompetitorCountFold.raw Q (counts xs)))=_
    rw [and_binary,ih]

theorem scalar_meaning {α : Type} (columns : List α) (offset : α → Bool) (value : α → ℕ) :
    (selected (columns.map (fun z => (offset z,value z)))).sum=
      (columns.map (fun z => if offset z then value z else 0)).sum := by
  simp only [selected,List.map_map,Function.comp_def]

end NearCubicWires.RepairOrdinary.CompetitorCountMask
