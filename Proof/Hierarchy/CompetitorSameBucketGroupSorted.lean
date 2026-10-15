import Proof.Hierarchy.CompetitorSameBucketGroupSemantics

/-! Stable grouping is derived from the actual sorted list. Filtering a
monotone key into increasing buckets preserves the complete original list,
including the order of different signed contributions within one bucket. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

universe u

theorem sorted_filter_split {α : Type u} (key : α → ℕ) (n : ℕ) (es : List α)
    (hs : es.Pairwise (fun a b => key a≤key b)) :
    es.filter (fun e => decide (key e<n)) ++
      es.filter (fun e => decide (n≤key e))=es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he,hs⟩ := List.pairwise_cons.mp hs
    by_cases hn : key e<n
    · simpa [List.filter_cons,hn,show ¬n≤key e by omega] using congrArg (List.cons e) (ih hs)
    · have hall : ∀ a∈es,n≤key a := by intro a ha; have h:=he a ha; omega
      have hlo : es.filter (fun a => decide (key a<n))=[] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        simpa only [Bool.not_eq_true,decide_eq_false_iff_not] using (show ¬key a<n by have h:=hall a ha; omega)
      have hhi : es.filter (fun a => decide (n≤key a))=es := by
        exact List.filter_eq_self.mpr (by intro a ha; simpa only [decide_eq_true_eq] using hall a ha)
      simp [hn,show n≤key e by omega,hlo,hhi]

theorem sorted_range_filter {α : Type u} (key : α → ℕ) (n : ℕ) (es : List α)
    (hs : es.Pairwise (fun a b => key a≤key b)) :
    (List.range n).flatMap (fun j => es.filter (fun e => decide (key e=j)))=
      es.filter (fun e => decide (key e<n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
    have h := sorted_filter_split key n (es.filter (fun e => decide (key e<n+1))) (hs.filter _)
    have hlo : (es.filter (fun e => decide (key e<n+1))).filter (fun e => decide (key e<n))=
        es.filter (fun e => decide (key e<n)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro a _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      omega
    have hhi : (es.filter (fun e => decide (key e<n+1))).filter (fun e => decide (n≤key e))=
        es.filter (fun e => decide (key e=n)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro a _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      omega
    rw [hlo,hhi] at h
    exact h

theorem sorted_range_groups {α : Type u} (key : α → ℕ) (n : ℕ) (es : List α)
    (hs : es.Pairwise (fun a b => key a≤key b)) (hb : ∀ e∈es,key e<n) :
    (List.range n).flatMap (fun j => es.filter (fun e => decide (key e=j)))=es := by
  rw [sorted_range_filter key n es hs]
  exact List.filter_eq_self.mpr (by intro e he; simpa only [decide_eq_true_eq] using hb e he)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
