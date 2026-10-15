import Proof.Hierarchy.CompetitorSameBucketGroupSorted

/-! Dense row-major groups are the consecutive blocks of the physically
sorted typed source. No runtime grid driver is assumed by this regrouping. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
open SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def groups (u : ℕ) (es : List Entry) : List (List Entry) :=
  (List.range u).flatMap (fun row => (List.range u).map (fun col => atCell row (u+col) es))
def Domain (u : ℕ) (e : Entry) : Prop := e.row < u ∧ u ≤ e.rightTaggedID ∧ e.rightTaggedID < 2*u

theorem groups_length (u : ℕ) (es : List Entry) : (groups u es).length=u*u := by
  simp [groups,List.length_flatMap]

theorem row_group (u row : ℕ) (es : List Entry)
    (hd : ∀ e∈es,Domain u e)
    (hs : es.Pairwise (fun a b => a.row < b.row ∨ a.row=b.row ∧ a.rightTaggedID ≤ b.rightTaggedID)) :
    (List.range u).flatMap (fun col => atCell row (u+col) es)=
      es.filter (fun e => decide (e.row=row)) := by
  let xs := es.filter (fun e => decide (e.row=row))
  have hxs : xs.Pairwise (fun a b => a.rightTaggedID-u ≤ b.rightTaggedID-u) := by
    apply List.Pairwise.imp_of_mem _ (hs.filter (fun e => decide (e.row=row)))
    intro a b ha hb hab
    have hra : a.row=row := by simpa only [List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp ha).2
    have hrb : b.row=row := by simpa only [List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    rcases hab with h|⟨_,h⟩
    · omega
    · omega
  have h := sorted_range_groups (fun e : Entry => e.rightTaggedID-u) u xs hxs (by
    intro e he
    have hd' := hd e (List.mem_filter.mp he).1
    unfold Domain at hd'
    omega)
  have hfields (col : ℕ) : xs.filter (fun e => decide (e.rightTaggedID-u=col))=atCell row (u+col) es := by
    unfold xs atCell
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    have hd' := hd e he
    unfold Domain at hd'
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    omega
  simpa only [hfields] using h

theorem groups_flatten (u : ℕ) (es : List Entry)
    (hd : ∀ e∈es,Domain u e)
    (hs : es.Pairwise (fun a b => a.row < b.row ∨ a.row=b.row ∧ a.rightTaggedID ≤ b.rightTaggedID)) :
    (groups u es).flatten=es := by
  have hrows : es.Pairwise (fun a b => a.row ≤ b.row) := by
    apply hs.imp
    intro a b h
    rcases h with h|⟨h,_⟩  <;> omega
  have h := sorted_range_groups Entry.row u es hrows (fun e he => (hd e he).1)
  simp only [groups,List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_map]
  simpa only [id_eq,row_group u _ es hd hs] using h

theorem sorted_groups_flatten (u p m : ℕ) (es : List Entry)
    (hd : ∀ e∈es,Domain u e) (hm : 2*u ≤ 2^m)
    (hs : es.Pairwise (fun a b => value (word (a.record p m)) ≤ value (word (b.record p m)))) :
    (groups u es).flatten=es := by
  apply groups_flatten u es hd
  apply hs.imp_of_mem
  intro a b ha hb hab
  have hda:=hd a ha
  have hdb:=hd b hb
  unfold Domain at hda hdb
  exact cell_order p m a b (by omega) (by omega) (by omega) (by omega) hab

theorem groups_nonempty (u : ℕ) (es : List Entry)
    (coverage : ∀ row col : Fin u,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=u+col.val) :
    ∀ g∈groups u es,g≠[] := by
  intro g hg
  obtain ⟨row,hr,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨col,hc,rfl⟩ := List.mem_map.mp hg
  obtain ⟨e,he,her,hec⟩ := coverage ⟨row,List.mem_range.mp hr⟩ ⟨col,List.mem_range.mp hc⟩
  have hm : e∈atCell row (u+col) es := by simp [atCell,he,her,hec]
  exact List.ne_nil_of_mem hm

theorem dense_groups (w u : ℕ) (es : List Entry) :
    dense w u es=(groups u es).flatMap (fun g => binary w (positive g)++binary w (negative g)) := by
  have hr : (List.finRange u).map Fin.val=List.range u := List.map_coe_finRange_eq_range
  unfold dense cells CompetitorPlaneStream.oldWords groups
  simp only [List.flatMap_assoc,List.flatMap_map,CompetitorPlaneStream.oldWord,
    CompetitorPlane.pairWord,cell]
  rw [← hr]
  simp only [List.flatMap_map]

theorem group_same (u : ℕ) (es : List Entry) (g : List Entry) (hg : g∈groups u es) :
    ∀ a∈g,∀ b∈g,a.row=b.row ∧ a.rightTaggedID=b.rightTaggedID := by
  obtain ⟨row,_,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨col,_,rfl⟩ := List.mem_map.mp hg
  intro a ha b hb
  have ha' : a.row=row ∧ a.rightTaggedID=u+col := by
    simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp ha).2
  have hb' : b.row=row ∧ b.rightTaggedID=u+col := by
    simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
  omega

theorem groups_strict (u : ℕ) (es : List Entry) :
    (groups u es).Pairwise (fun g h => ∀ a∈g,∀ b∈h,
      a.row<b.row ∨ a.row=b.row ∧ a.rightTaggedID<b.rightTaggedID) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro row _
    rw [List.pairwise_map]
    apply List.pairwise_lt_range.imp
    intro c d hcd a ha b hb
    have ha' : a.row=row ∧ a.rightTaggedID=u+c := by
      simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp ha).2
    have hb' : b.row=row ∧ b.rightTaggedID=u+d := by
      simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact Or.inr ⟨by omega,by omega⟩
  · apply List.pairwise_lt_range.imp
    intro row next hrow g hg h hh
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hg
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hh
    intro a ha b hb
    have ha' : a.row=row ∧ a.rightTaggedID=u+c := by
      simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp ha).2
    have hb' : b.row=next ∧ b.rightTaggedID=u+d := by
      simpa only [atCell,List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact Or.inl (by omega)

theorem groups_fit (w u : ℕ) (es : List Entry)
    (hf : ∀ row col : Fin u,positive (atCell row.val (u+col.val) es)<2^w ∧
      negative (atCell row.val (u+col.val) es)<2^w) :
    ∀ g∈groups u es,positive g<2^w ∧ negative g<2^w := by
  intro g hg
  obtain ⟨row,hr,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨col,hc,rfl⟩ := List.mem_map.mp hg
  exact hf ⟨row,List.mem_range.mp hr⟩ ⟨col,List.mem_range.mp hc⟩

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
