import Proof.Supplier.RowTupleFilterBody

/-! The accumulated flag of the physical digit body means exactly the
positional subset predicate used by the row expansion. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterMeaning
open RowTupleFilterParts RowTupleFilterBody
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fold : Data→List ℕ→Data
  | x,[]=>x
  | x,d::ds=>fold (advance x d) ds

theorem fold_source (x : Data) (ds : List ℕ) : (fold x ds).source=x.source := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => exact (ih _).trans (advance_fields x d).1

theorem fold_good (x : Data) (ds : List ℕ) :
    (fold x ds).good=true ↔ x.good=true ∧ ds.Pairwise (·<·) ∧
      (∀ d∈ds,d≤x.bound) ∧ (x.seen=true → ∀ d∈ds,x.previous<d) := by
  induction ds generalizing x with
  | nil => simp [fold]
  | cons d ds ih =>
    rw [fold,ih,advance_good]
    have hfields := advance_fields x d
    rw [hfields.2.1,hfields.2.2.2.1,hfields.2.2.2.2]
    simp only [true_implies]
    constructor
    · rintro ⟨⟨hg,hold,hbound⟩,hpair,hbounds,hprev⟩
      refine ⟨hg,List.pairwise_cons.mpr ⟨hprev,hpair⟩,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hbound
        · exact hbounds a ha
      · intro hs a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hold hs
        · exact (hold hs).trans (hprev a ha)
    · rintro ⟨hg,hpair,hbounds,hprev⟩
      obtain ⟨hp,hpair⟩ := List.pairwise_cons.mp hpair
      exact ⟨⟨hg,fun hs=>hprev hs d (by simp),hbounds d (by simp)⟩,hpair,
        fun a ha=>hbounds a (List.mem_cons_of_mem _ ha),hp⟩

def initial (source : List Bool) (M : ℕ) : Data :=
  ⟨source,0,M-1,0,false,false,false,true⟩

theorem initial_good (source : List Bool) (M : ℕ) (hM : 0<M) (ds : List ℕ) :
    (fold (initial source M) ds).good=RowTupleSubsets.valid M ds := by
  apply Bool.eq_iff_iff.mpr
  rw [fold_good,RowTupleSubsets.valid_iff]
  simp only [initial,Bool.false_eq_true,false_implies,and_true,true_and]
  constructor
  · rintro ⟨hp,hb⟩
    exact ⟨hp,fun d hd=>by have h:=hb d hd; omega⟩
  · rintro ⟨hp,hb⟩
    exact ⟨hp,fun d hd=>by have h:=hb d hd; omega⟩

end NearCubicWires.RepairOrdinary.RowTupleFilterMeaning
