import Proof.Hierarchy.CompetitorSameBucketGroupBounds
import Proof.Hierarchy.CompetitorSameBucketKeyRecords

/-! Typed witnesses of the SAME physical canonical key producer. The map
to signed records is literal; the sorter permutation lifts without assuming
injectivity of truncated encodings. Domain and coefficient bounds come from
the source request and actual packet occurrences. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
open MatrixScoreBatch CompetitorSameBucketGroup
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pair (r : Request) (coefficient : ℤ) (left right : Option KeyLoop.Record) : List Entry :=
  match left,right with
  | some a,some b => if CompetitorSameBucketPairCompare.fires r.U a.2.1 b.2.1 a.2.2 b.2.2 then
      [⟨coefficient,a.2.1,b.2.1⟩] else []
  | _,_ => []
noncomputable def gate (r : Request) (g : Fin r.Gates) : List Entry :=
  (CompetitorSameBucketPacketRows.rows r g).flatMap (fun xs => xs.flatMap (fun a =>
    xs.flatMap (fun b => pair r (weight r g) a b)))
noncomputable def contributions (r : Request) := (List.finRange r.Gates).flatMap (gate r)
def zeros (u : ℕ) : List Entry :=
  (List.finRange u).flatMap (fun row => (List.finRange u).map (fun col => ⟨0,row.val,u+col.val⟩))
noncomputable def entries (r : Request) := contributions r++zeros r.U

theorem pair_map (r : Request) (c : ℤ) (a b : Option KeyLoop.Record) :
    (pair r c a b).map (Entry.record r.p r.M)=CompetitorSameBucketKeyRecords.pair r c a b := by
  cases a <;> cases b <;> simp [pair,CompetitorSameBucketKeyRecords.pair]
  split <;> simp [Entry.record]

theorem records_map (r : Request) :
    (entries r).map (Entry.record r.p r.M)=CompetitorSameBucketKeyRecords.records r := by
  simp only [entries,contributions,gate,zeros,CompetitorSameBucketKeyRecords.records,
    CompetitorSameBucketKeyRecords.contributions,
    CompetitorSameBucketKeys.zeroRecords,List.map_append,List.map_flatMap,List.map_map,pair_map]
  rfl

theorem length_bound (r : Request) : (entries r).length ≤ 26*r.U^2 := by
  have h:=CompetitorSameBucketKeyRecords.records_length r
  rw [← records_map,List.length_map] at h
  exact h

theorem ranked_ids (r : Request) (g : Fin r.Gates) :
    ∀ e∈MatrixScoreRawRanks.entries r g,e.2.1 < 2*r.U := by
  apply CompetitorSameBucketPacketRows.indexed_ids
  intro e he
  obtain ⟨copy,_,rfl⟩ := List.mem_map.mp he
  have h := (SupplierPrinter.stableDominanceCopyId copy).isLt
  simpa only [two_mul] using h

theorem row_ids (r : Request) (g : Fin r.Gates) (xs : List (Option KeyLoop.Record))
    (hx : xs∈CompetitorSameBucketPacketRows.rows r g) (e : KeyLoop.Record) (he : some e∈xs) :
    e.2.1 < 2*r.U := by
  have hmem : some e∈CompetitorSameBucketPackets.records r g := by
    rw [← CompetitorSameBucketPacketRows.rows_flatten]
    exact List.mem_flatten.mpr ⟨xs,hx,he⟩
  simp only [CompetitorSameBucketPackets.records,List.mem_append,List.mem_map,List.mem_replicate] at hmem
  rcases hmem with ⟨a,ha,hae⟩ | ⟨_,hae⟩
  · cases Option.some.inj hae
    exact ranked_ids r g e ha
  · contradiction

theorem pair_membership (r : Request) (c : ℤ) (a b : Option KeyLoop.Record) (e : Entry)
    (he : e∈pair r c a b) :
    ∃ x y,a=some x ∧ b=some y ∧ e=⟨c,x.2.1,y.2.1⟩ ∧
      x.2.1 < r.U ∧ r.U ≤ y.2.1 ∧ x.2.2 < y.2.2 := by
  cases a with
  | none => simp [pair] at he
  | some x =>
    cases b with
    | none => simp [pair] at he
    | some y =>
      simp only [pair] at he
      split at he
      next h =>
        have heq:=List.mem_singleton.mp he
        exact ⟨x,y,rfl,rfl,heq,(CompetitorSameBucketPairCompare.fires_iff ..).mp h⟩
      next => simp at he

theorem entries_domain (r : Request) : ∀ e∈entries r,Domain r.U e := by
  intro e he
  rcases List.mem_append.mp he with he|he
  · simp only [contributions,gate,List.mem_flatMap] at he
    obtain ⟨g,_,xs,hxs,a,_,b,hb,he⟩:=he
    obtain ⟨x,y,_,rfl,rfl,hx,hy,_⟩:=pair_membership r _ a b e he
    exact ⟨hx,hy,row_ids r g xs hxs y hb⟩
  · simp only [zeros,List.mem_flatMap,List.mem_map] at he
    obtain ⟨row,_,col,_,rfl⟩:=he
    refine ⟨row.isLt,Nat.le_add_right _ _,?_⟩
    change r.U+col.val < 2*r.U
    have h:=col.isLt
    omega

theorem entries_bits (r : Request) : ∀ e∈entries r,e.coefficient.natAbs < 2^r.p := by
  intro e he
  rcases List.mem_append.mp he with he|he
  · simp only [contributions,gate,List.mem_flatMap] at he
    obtain ⟨g,_,xs,_,a,_,b,_,he⟩:=he
    obtain ⟨x,y,_,_,rfl,_⟩:=pair_membership r _ a b e he
    exact (r.fits _ (List.get_mem r.cuts g)).2.2
  · simp only [zeros,List.mem_flatMap,List.mem_map] at he
    obtain ⟨row,_,col,_,rfl⟩:=he
    exact Nat.two_pow_pos _

theorem zero_present (r : Request) (row col : Fin r.U) :
    (⟨0,row.val,r.U+col.val⟩ : Entry)∈entries r := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨row,by simp,List.mem_map.mpr ⟨col,by simp,rfl⟩⟩

theorem sorted_witness (r : Request) (sorted : List StablePartition.Record)
    (hs : sorted.Perm (CompetitorSameBucketKeyRecords.records r)) :
    ∃ es : List Entry,sorted=es.map (Entry.record r.p r.M) ∧ es.Perm (entries r) := by
  rw [← records_map] at hs
  have heq := congrFun (congrFun (List.eq_map_comp_perm (Entry.record r.p r.M)) sorted) (entries r)
  rw [← heq] at hs
  exact hs

theorem sorted_properties (r : Request) (es : List Entry) (h : es.Perm (entries r)) :
    (∀ e∈es,Domain r.U e) ∧ (∀ e∈es,e.coefficient.natAbs < 2^r.p) ∧
    (∀ row col : Fin r.U,∃ e∈es,e.row=row.val ∧ e.rightTaggedID=r.U+col.val) ∧
    es.length ≤ 26*r.U^2 := by
  refine ⟨fun e he=>entries_domain r e (h.mem_iff.mp he),
    fun e he=>entries_bits r e (h.mem_iff.mp he),?_,?_⟩
  · intro row col
    exact ⟨⟨0,row.val,r.U+col.val⟩,h.mem_iff.mpr (zero_present r row col),rfl,rfl⟩
  · rw [h.length_eq]
    exact length_bound r

end NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
