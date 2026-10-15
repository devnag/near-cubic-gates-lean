import Proof.Hierarchy.CompetitorSameBucketGateMeaning

/-! Exact B.3 same-bucket identity of the cold producer's literal signed
bank. Zero coverage contributes zero and the enumerated gate sum is the
paper's canonical sameBucketContribution, including all signs and ties. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
open MatrixScoreBatch SupplierPrinter CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem signed_flatMap {α : Type} (xs : List α) (f : α → List Entry) (row col : ℕ) :
    (positive (atCell row col (xs.flatMap f)) : ℤ)-negative (atCell row col (xs.flatMap f))=
      (xs.map (fun x=>(positive (atCell row col (f x)) : ℤ)-negative (atCell row col (f x)))).sum := by
  induction xs with
  | nil => simp [atCell]
  | cons x xs ih =>
    simp only [List.flatMap_cons,atCell_append,positive_append,negative_append,
      Nat.cast_add,List.map_cons,List.sum_cons]
    rw [← ih]
    ring

theorem signed_zeros (u row col : ℕ) :
    (positive (atCell row col (zeros u)) : ℤ)-negative (atCell row col (zeros u))=0 := by
  have h:=zeros_parts u row col
  have hp : positive (atCell row col (zeros u))=0 := by omega
  have hn : negative (atCell row col (zeros u))=0 := by omega
  simp only [hp,hn,Nat.cast_zero,sub_self]

theorem same_signed (r : Request) (row col : Fin r.U) :
    (positive (atCell row.val (r.U+col.val) (entries r)) : ℤ)-
      negative (atCell row.val (r.U+col.val) (entries r))=
      sameBucketContribution (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize)
        (weight r) row col := by
  have hz:=signed_zeros r.U row.val (r.U+col.val)
  have hg:=signed_flatMap (List.finRange r.Gates) (gate r) row.val (r.U+col.val)
  simp only [gate_signed] at hg
  rw [← List.ofFn_eq_map,List.sum_ofFn] at hg
  have hc : (positive (atCell row.val (r.U+col.val) (contributions r)) : ℤ)-
      negative (atCell row.val (r.U+col.val) (contributions r))=
      sameBucketContribution (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize)
        (weight r) row col := hg
  simp only [entries,atCell_append,positive_append,negative_append,Nat.cast_add]
  linear_combination hc+hz

theorem dominance_decomposition (r : Request) (row col : Fin r.U) :
    weightedDominance (leftScore r) (rightScore r) (weight r) row col=
      ((positive (atCell row.val (r.U+col.val) (entries r)) : ℤ)-
        negative (atCell row.val (r.U+col.val) (entries r)))+
      laterBucketContribution (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize)
        (weight r) row col := by
  rw [same_signed]
  exact weightedDominance_eq_stable_same_add_later (leftScore r) (rightScore r) r.bucketSize (weight r) row col

end NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
