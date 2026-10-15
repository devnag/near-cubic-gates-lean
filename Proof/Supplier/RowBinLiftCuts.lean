import Proof.Supplier.RowBinLiftOccurrences
import Proof.Supplier.EquationRowRequest
import Proof.Supplier.EquationGateCapacity

/-! Concrete signed cuts for the A.12 occurrence expansion. The declared width
is computed from the actual emitted fields. The ordinary enumerator must still
produce this word; no precomputed row is added to a source contract. -/
namespace NearCubicWires.RepairOrdinary.RowBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open MatrixScoreBatch EquationRow ExecutableInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Equation (l r : ℕ) := LabelledEquation (Fin l ⊕ Fin r)

def assignment {l r : ℕ} (row column : ℕ) : Fin l ⊕ Fin r → Bool :=
  Sum.elim (fun i => row.testBit i.val) (fun i => column.testBit i.val)

def split {l r : ℕ} (coefficient : ℤ) (e : Equation l r) : Cut :=
  ⟨List.ofFn (fun i => e.weights (Sum.inl i)),
    List.ofFn (fun i => e.weights (Sum.inr i)),e.target,coefficient⟩

theorem linearForm_ofFn {n : ℕ} (w : Fin n → ℤ) (a : ℕ) :
    linearForm (List.ofFn w) a=∑ i : Fin n,w i*bitInt (a.testBit i.val) := by
  have hz : (List.ofFn w).zipIdx=List.ofFn (fun i => (w i,i.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [linearForm,hz,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : a.testBit i.val <;> simp [bitInt,h]

theorem split_score {l r : ℕ} (c : ℤ) (e : Equation l r) (row column : ℕ) :
    linearForm (split c e).leftWeights row+linearForm (split c e).rightWeights column=
      e.score (assignment row column) := by
  simp only [split,linearForm_ofFn,LabelledEquation.score,Fintype.sum_sum_type,
    assignment,Sum.elim_inl,Sum.elim_inr]

theorem split_value {l r : ℕ} (c : ℤ) (e : Equation l r) (row column : ℕ) :
    exactValue (split c e) row column=
      c*((decide (e.Holds (assignment row column))).toNat : ℤ) := by
  rw [exactValue,split_score]
  simp only [split,exactCut,LabelledEquation.Holds,LabelledEquation.difference,sub_eq_zero]
  simp only [eq_comm]
  rfl

def cuts {l r : ℕ} (Q : ℕ) (monomials : List (List (Equation l r))) : List Cut :=
  (terms Q monomials).map fun t => split t.1 (canonicalEquationStack t.2)

theorem stack_all {l r : ℕ} (es : List (Equation l r)) (row column : ℕ) :
    decide ((canonicalEquationStack es).Holds (assignment row column))=
      es.all (fun e => decide (e.Holds (assignment row column))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.all_eq_true,canonicalEquationStack_holds_iff]

theorem cuts_value {l r : ℕ} (Q : ℕ) (monomials : List (List (Equation l r)))
    (row column : ℕ) :
    ((cuts Q monomials).map (fun c => exactValue c row column)).sum=
      binLift Q (polynomialOccurrenceCount
        (fun e (_ : Unit) (_ : Unit) => decide (e.Holds (assignment row column)))
        monomials () ()) := by
  simp only [cuts,List.map_map,Function.comp_def,split_value,stack_all]
  exact terms_value Q monomials (fun e => decide (e.Holds (assignment row column)))

theorem cuts_length {l r : ℕ} (Q : ℕ) (monomials : List (List (Equation l r))) :
    (cuts Q monomials).length=
      ∑ j ∈ Finset.range (min Q monomials.length),monomials.length.choose (j+1) := by
  rw [cuts,List.length_map,terms_length]

theorem cuts_lengths {l r : ℕ} (Q : ℕ) (monomials : List (List (Equation l r)))
    (c : Cut) (hc : c ∈ cuts Q monomials) :
    c.leftWeights.length=l ∧ c.rightWeights.length=r := by
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hc
  simp [split]

end NearCubicWires.RepairOrdinary.RowBinLift
