import Proof.Supplier.RowBinLiftWidth

/-! A safe power radix gives the same occurrence conjunctions as canonical
stacking. Its numeric coefficients are deliberately not identified with the
canonical radix coefficients. This is the semantic target of binary blocks. -/
namespace NearCubicWires.RepairOrdinary.RowPowerBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stack {α : Type} (w : ℕ) (es : List (LabelledEquation α)) :=
  stackEquations ((2 : ℤ)^w) es

theorem stack_holds {α : Type} [Fintype α] (w : ℕ)
    (es : List (LabelledEquation α)) (input : α → Bool)
    (hw : ∀ e ∈ es,equationMagnitudeBound e<2^w) :
    (stack w es).Holds input ↔ ∀ e ∈ es,e.Holds input := by
  apply stackEquations_holds_iff
  · positivity
  · intro e he
    have h := (equation_difference_natAbs_le_magnitudeBound e input).trans_lt (hw e he)
    have habs : |e.difference input|<(2 : ℤ)^w := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_lt.mp habs

theorem same_conjunction {α : Type} [Fintype α] (w : ℕ)
    (es : List (LabelledEquation α)) (input : α → Bool)
    (hw : ∀ e ∈ es,equationMagnitudeBound e<2^w) :
    (stack w es).Holds input ↔ (canonicalEquationStack es).Holds input := by
  rw [stack_holds w es input hw,canonicalEquationStack_holds_iff]

theorem stack_width {α : Type} [Fintype α] (w : ℕ)
    (es : List (LabelledEquation α))
    (hw : ∀ e ∈ es,equationMagnitudeBound e<2^w) :
    equationMagnitudeBound (stack w es)<2^(w*es.length) := by
  have h := equationMagnitudeBound_stackEquations_le ((2 : ℤ)^w) es
  have hb : ((2 : ℤ)^w).natAbs=2^w := by simp
  rw [hb] at h
  have horner := RowBinLift.horner_lt_pow (2^w) (by positivity)
    (es.map equationMagnitudeBound) (by
      intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      exact hw e he)
  simpa only [stack,List.length_map,←pow_mul] using h.trans_lt horner

theorem term_members {α : Type} (Q : ℕ) (ms : List (List α))
    (t : ℤ × List α) (ht : t ∈ terms Q ms) (e : α) (he : e ∈ t.2) :
    e ∈ ms.flatten := by
  obtain ⟨j,_,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨selected,hs,rfl⟩ := List.mem_map.mp ht
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  exact List.mem_flatten.mpr ⟨m,(List.mem_sublistsLen.mp hs).1.subset hm,he⟩

def cuts {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) : List Cut :=
  (terms Q ms).map fun t => split t.1 (stack w t.2)

theorem cuts_value {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r)))
    (hw : ∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w) (row column : ℕ) :
    ((cuts w Q ms).map (fun c => exactValue c row column)).sum=
      binLift Q (polynomialOccurrenceCount
        (fun e (_ : Unit) (_ : Unit) => decide (e.Holds (assignment row column))) ms () ()) := by
  have hall (t : ℤ × List (Equation l r)) (ht : t ∈ terms Q ms) :
      decide ((stack w t.2).Holds (assignment row column))=
        t.2.all (fun e => decide (e.Holds (assignment row column))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,List.all_eq_true]
    exact stack_holds w t.2 _ (fun e he => hw e (term_members Q ms t ht e he))
  simp only [cuts,List.map_map,Function.comp_def,split_value]
  calc
    _ = ((terms Q ms).map (fun t => t.1*((t.2.all
        (fun e => decide (e.Holds (assignment row column)))).toNat : ℤ))).sum := by
      congr 1
      apply List.map_congr_left
      intro t ht
      rw [hall t ht]
    _ = _ := terms_value Q ms (fun e => decide (e.Holds (assignment row column)))

theorem cuts_length {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) :
    (cuts w Q ms).length=(RowBinLift.cuts Q ms).length := by
  simp [cuts,RowBinLift.cuts]

def batch {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :=
  rows.flatMap (cuts w Q)

theorem batch_length {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :
    (batch w Q rows).length=(RowBinLift.batch Q rows).length := by
  simp only [batch,RowBinLift.batch,List.length_flatMap,cuts_length]

def input (s w Q : ℕ) (rows : List (List (List (Equation ((s+1)/2) (s/2)))))
    (hs : 67 ≤ s) (hg : (RowBinLift.batch Q rows).length^100 ≤ 2^s) : EquationRow.Input where
  d := (s+1)/2
  p := fieldWidth (batch w Q rows)
  odd := decide (s%2=1)
  cuts := batch w Q rows
  lengths := by
    intro c hc
    obtain ⟨ms,_,hm⟩ := List.mem_flatMap.mp hc
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hm
    simp only [split,List.length_ofFn]
    constructor
    · trivial
    · by_cases hp : s%2=1 <;> simp [hp] <;> omega
  fits := fields_fit (batch w Q rows)
  oddPositive := by intro _; omega
  gateSquare := by
    apply doubled_gateSquare hs
    simpa only [batch_length] using hg

theorem input_value (s w Q : ℕ) (rows : List (List (List (Equation ((s+1)/2) (s/2)))))
    (hs : 67 ≤ s) (hg : (RowBinLift.batch Q rows).length^100 ≤ 2^s)
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (row column : Fin (EquationRow.request (input s w Q rows hs hg)).U) :
    weightedDominance (leftScore (EquationRow.request (input s w Q rows hs hg)))
      (rightScore (EquationRow.request (input s w Q rows hs hg)))
      (weight (EquationRow.request (input s w Q rows hs hg))) row column=
      (rows.map (fun ms => binLift Q (polynomialOccurrenceCount
        (fun e (_ : Unit) (_ : Unit) => decide (e.Holds (assignment row.val column.val)))
        ms () ()))).sum := by
  rw [EquationRow.request_value]
  change (((batch w Q rows).map (fun c => exactValue c row.val column.val)).sum)=_
  simp only [batch,List.map_flatMap,sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro ms hm
  exact cuts_value w Q ms (hw ms hm) row.val column.val

end NearCubicWires.RepairOrdinary.RowPowerBinLift
