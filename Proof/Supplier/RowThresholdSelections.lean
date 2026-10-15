import Proof.Foundations.RepresentationSourceContracts
import Proof.Supplier.SupplierEstimator

/-! The threshold row's actual child family is derived from the corrected
source. Its exact top-child aggregation is a natural SUM; no old executor
record or additional source premise is used for the semantic transport. -/
namespace NearCubicWires.RepairOrdinary.ThresholdRows
open RepairRepresentation SupplierPipeline SupplierEstimator SupplierPrinter
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def children (a : DecompositionAlgorithm) {q : ℕ} (c : NormalizedThresholdThresholdCircuit q) :=
  (retainedTopDecomposition a c).children
abbrev Selection (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :=
  (i : Fin r.circuits.length) → Fin (children a (r.circuits.get i)).length

def equations (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : Selection a r) :=
  List.ofFn fun i : Fin r.circuits.length =>
    thresholdChildEquation r i ((children a (r.circuits.get i)).get (sel i))
def equation (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : Selection a r) := canonicalEquationStack (equations a r sel)

theorem equation_holds_iff (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (sel : Selection a r) (x : BitInput r.q) :
    (equation a r sel).Holds (fun i => ((thresholdFourfoldOccurrences r).get i).eval x) ↔
      ∀ i : Fin r.circuits.length,
        ((children a (r.circuits.get i)).get (sel i)).eval (retainedBottomValues (r.circuits.get i) x)=true := by
  unfold equation
  rw [canonicalEquationStack_holds_iff]
  constructor
  · intro h i
    apply (thresholdChildEquation_holds_iff r i _ x).mp
    exact h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact (thresholdChildEquation_holds_iff r i _ x).mpr (h i)

theorem bool_nat (b : Bool) : b.toNat=(if b=true then 1 else 0) := by cases b <;> rfl

theorem list_sum_count {α : Type} (xs : List α) (f : α → Bool) :
    (∑ i : Fin xs.length,(f (xs.get i)).toNat)=(xs.filter f).length := by
  have hm : (xs.map (fun x => (f x).toNat)).sum=(xs.filter f).length := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases hf : f a <;> simp [hf,ih,Nat.add_comm]
  rw [←List.sum_ofFn]
  have he : List.ofFn (fun i : Fin xs.length => (f (xs.get i)).toNat)=xs.map (fun x => (f x).toNat) := by
    simpa only [List.ofFn_get,Function.comp_def] using
      (List.map_ofFn (g := fun x => (f x).toNat) (f := fun i : Fin xs.length => xs.get i)).symm
  rw [he]
  exact hm

theorem selection_indicator (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (sel : Selection a r) (x : BitInput r.q) :
    (if (equation a r sel).Holds (fun i => ((thresholdFourfoldOccurrences r).get i).eval x) then 1 else 0)=
      ∏ i : Fin r.circuits.length,
        (((children a (r.circuits.get i)).get (sel i)).eval (retainedBottomValues (r.circuits.get i) x)).toNat := by
  classical
  simp_rw [bool_nat]
  simp only [Fintype.prod_boole,equation_holds_iff]
  by_cases h : ∀ i : Fin r.circuits.length,
      ((children a (r.circuits.get i)).get (sel i)).eval
        (retainedBottomValues (r.circuits.get i) x)=true
  · simp only [h]
  · simp only [h,ite_false]

theorem selection_sum (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (x : BitInput r.q) :
    (∑ sel : Selection a r,
      if (equation a r sel).Holds (fun i => ((thresholdFourfoldOccurrences r).get i).eval x) then 1 else 0)=
      (conjunctionBit NormalizedThresholdThresholdCircuit.eval r.circuits x).toNat := by
  classical
  simp_rw [selection_indicator]
  have hp := Fintype.prod_sum (κ := fun i : Fin r.circuits.length => Fin (children a (r.circuits.get i)).length)
    (fun i j => (((children a (r.circuits.get i)).get j).eval (retainedBottomValues (r.circuits.get i) x)).toNat)
  rw [←hp]
  have hsum (i : Fin r.circuits.length) := list_sum_count (children a (r.circuits.get i))
    (fun c => c.eval (retainedBottomValues (r.circuits.get i) x))
  simp_rw [hsum]
  have hc (i : Fin r.circuits.length) :
      ((children a (r.circuits.get i)).filter
        (fun c => c.eval (retainedBottomValues (r.circuits.get i) x))).length=
      ((r.circuits.get i).eval x).toNat := retainedTop_count a (r.circuits.get i) x
  simp_rw [hc]
  rw [conjunctionBit_toNat,←List.prod_ofFn]
  congr 1
  simpa only [List.ofFn_get,Function.comp_def] using
    (List.map_ofFn (g := fun c : NormalizedThresholdThresholdCircuit r.q => (c.eval x).toNat)
      (f := fun i : Fin r.circuits.length => r.circuits.get i)).symm

end
end NearCubicWires.RepairOrdinary.ThresholdRows
