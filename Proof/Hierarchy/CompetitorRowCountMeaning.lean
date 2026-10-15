import Proof.Hierarchy.CompetitorCrossStateMeaning
import Proof.Supplier.RowPowerBinLift

/-! The actual weighted bank sum is congruent to the list of Boolean row
values. Repeated rows and monomial occurrences retain their multiplicity.
The width of the executed request is independent of the semantic radix. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def occurrence {l r : ℕ} (ms : List (List (Equation l r))) (row column : ℕ) : ℕ :=
  polynomialOccurrenceCount
    (fun e (_ : Unit) (_ : Unit) => decide (e.Holds (assignment row column))) ms () ()

def count {l r : ℕ} (rows : List (List (List (Equation l r)))) (row column : ℕ) : ℕ :=
  (rows.map (fun ms => occurrence ms row column%2)).sum

theorem count_le_length {l r : ℕ} (rows : List (List (List (Equation l r))))
    (row column : ℕ) : count rows row column ≤ rows.length := by
  induction rows with
  | nil => simp [count]
  | cons ms rows ih =>
    have hm := Nat.mod_lt (occurrence ms row column) (by decide : 0<2)
    simp only [count,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem lifted_modEq {l r : ℕ} (Q : ℕ) (rows : List (List (List (Equation l r))))
    (row column : ℕ) : Int.ModEq ((2 : ℤ)^Q)
      (rows.map (fun ms => binLift Q (occurrence ms row column))).sum
      (count rows row column) := by
  induction rows with
  | nil => simp [count]
  | cons ms rows ih =>
    simpa only [count,List.map_cons,List.sum_cons,Nat.cast_add] using
      (binLiftModEqParity Q (occurrence ms row column)).add ih

theorem batch_value {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r))))
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (row column : ℕ) :
    ((RowPowerBinLift.batch w Q rows).map (fun c => exactValue c row column)).sum=
      (rows.map (fun ms => binLift Q (occurrence ms row column))).sum := by
  simp only [RowPowerBinLift.batch,List.map_flatMap,sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro ms hm
  exact RowPowerBinLift.cuts_value w Q ms (hw ms hm) row column

theorem request_modEq {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r))))
    (input : EquationRow.Input) (hc : input.cuts=RowPowerBinLift.batch w Q rows)
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (row column : Fin (request input).U) : Int.ModEq ((2 : ℤ)^Q)
      (weightedDominance (leftScore (request input)) (rightScore (request input))
        (weight (request input)) row column)
      (count rows row.val column.val) := by
  rw [request_value,hc,batch_value w Q rows hw]
  exact lifted_modEq Q rows row.val column.val

theorem banks_modEq {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r))))
    (input : EquationRow.Input) (hc : input.cuts=RowPowerBinLift.batch w Q rows)
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (i : Fin ((request input).U*(request input).U)) : Int.ModEq ((2 : ℤ)^Q)
      ((((CompetitorCrossStateMeaning.state (request input)).positive i+
        (CompetitorSameBucketState.state (request input)).positive i : ℕ) : ℤ)-
        ((CompetitorCrossStateMeaning.state (request input)).negative i+
        (CompetitorSameBucketState.state (request input)).negative i : ℕ))
      (count rows i.divNat.val i.modNat.val) := by
  rw [CompetitorCrossStateMeaning.combined_dominance]
  exact request_modEq w Q rows input hc hw i.divNat i.modNat

theorem count_fit {l r : ℕ} (Q : ℕ) (rows : List (List (List (Equation l r))))
    (hrows : rows.length<2^Q) (row column : ℕ) : count rows row column<2^Q :=
  (count_le_length rows row column).trans_lt hrows

theorem odd_even_size (input : EquationRow.Input) (ho : input.odd=true) :
    (request input).U/2+(request input).U/2=(request input).U := by
  have hd := input.oddPositive ho
  have he : input.d=input.d-1+1 := by omega
  change 2^input.d/2+2^input.d/2=2^input.d
  rw [he,pow_succ]
  rw [Nat.mul_div_cancel _ (by decide : 0<2)]
  omega

end NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
