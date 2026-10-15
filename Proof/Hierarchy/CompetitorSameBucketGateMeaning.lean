import Proof.Hierarchy.CompetitorSameBucketPacketBuckets

/-! Exact mathematical meaning of the SAME emitted local scan: one signed
coefficient precisely when the canonical stable buckets agree and the
dominance comparison holds. Repeated scores are handled by the actual IDs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
open MatrixScoreBatch SupplierPrinter CompetitorSameBucketGroup
open CompetitorSameBucketRankMeaning CompetitorSameBucketPacketRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def GateCondition (r : Request) (g : Fin r.Gates) (row col : Fin r.U) : Prop :=
  (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize).leftBucket row g=
    (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize).rightBucket g col ∧
    leftScore r row g ≤ rightScore r g col

noncomputable instance (r : Request) (g : Fin r.Gates) (row col : Fin r.U) : Decidable (GateCondition r g row col) := by
  unfold GateCondition
  infer_instance

theorem packet_unique_id (r : Request) (g : Fin r.Gates) (e : KeyLoop.Record)
    (copy : StableDominanceCopy r.U r.U)
    (he : some e∈CompetitorSameBucketPackets.records r g) (hid : e.2.1=(ranked r g copy).2.1) :
    e=ranked r g copy := by
  obtain ⟨a,rfl⟩:=(entries_member r g e).mp ((packet_member r g e).mp he)
  exact congrArg (ranked r g) (ranked_id_injective r g a copy hid)

theorem gate_cell_member (r : Request) (g : Fin r.Gates) (row col : Fin r.U) (e : Entry) :
    e∈atCell row.val (r.U+col.val) (gate r g) ↔
      e=⟨weight r g,row.val,r.U+col.val⟩ ∧ GateCondition r g row col := by
  constructor
  · intro he
    obtain ⟨he,hcoord⟩:=List.mem_filter.mp he
    have coords : e.row=row.val ∧ e.rightTaggedID=r.U+col.val := of_decide_eq_true hcoord
    simp only [gate,List.mem_flatMap] at he
    obtain ⟨xs,hxs,a,ha,b,hb,he⟩:=he
    obtain ⟨x,y,rfl,rfl,rfl,_,_,hcompare⟩:=pair_membership r (weight r g) a b e he
    have hrow:=(same_row_iff r g x y).mp ⟨xs,hxs,ha,hb⟩
    have hx : x=ranked r g (.inl row) := packet_unique_id r g x (.inl row) hrow.1 coords.1
    have hy : y=ranked r g (.inr col) := packet_unique_id r g y (.inr col) hrow.2.1 coords.2
    subst x
    subst y
    refine ⟨rfl,?_,(rank_comparison r g row col).mp hcompare⟩
    exact (canonical_same_row r g row col).mp ⟨xs,hxs,ha,hb⟩
  · rintro ⟨rfl,hcondition⟩
    obtain ⟨xs,hxs,ha,hb⟩:=(canonical_same_row r g row col).mpr hcondition.1
    have hf : CompetitorSameBucketPairCompare.fires r.U
        (ranked r g (.inl row)).2.1 (ranked r g (.inr col)).2.1
        (ranked r g (.inl row)).2.2 (ranked r g (.inr col)).2.2=true :=
      (CompetitorSameBucketPairCompare.fires_iff ..).mpr
        ⟨row.isLt,Nat.le_add_right _ _,(rank_comparison r g row col).mpr hcondition.2⟩
    apply List.mem_filter.mpr
    refine ⟨?_,by simp⟩
    apply List.mem_flatMap.mpr
    refine ⟨xs,hxs,List.mem_flatMap.mpr ⟨some (ranked r g (.inl row)),ha,?_⟩⟩
    apply List.mem_flatMap.mpr
    refine ⟨some (ranked r g (.inr col)),hb,?_⟩
    simp only [pair,hf,↓reduceIte]
    exact List.mem_singleton.mpr rfl

theorem gate_cell (r : Request) (g : Fin r.Gates) (row col : Fin r.U) :
    atCell row.val (r.U+col.val) (gate r g)=
      if GateCondition r g row col then [⟨weight r g,row.val,r.U+col.val⟩] else [] := by
  classical
  by_cases hc : GateCondition r g row col
  · rw [if_pos hc]
    have he:=(gate_cell_member r g row col ⟨weight r g,row.val,r.U+col.val⟩).mpr ⟨rfl,hc⟩
    have hlen:=gate_cell_count r g row.val (r.U+col.val)
    have hpos : 0 < (atCell row.val (r.U+col.val) (gate r g)).length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem he)
    cases hlist : atCell row.val (r.U+col.val) (gate r g) with
    | nil => simp [hlist] at hpos
    | cons a tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by simp only [hlist,List.length_cons] at hlen;omega)
      subst tail
      simp only [hlist,List.mem_singleton] at he
      rw [he]
  · rw [if_neg hc]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    exact hc ((gate_cell_member r g row col e).mp he).2

theorem gate_signed (r : Request) (g : Fin r.Gates) (row col : Fin r.U) :
    (positive (atCell row.val (r.U+col.val) (gate r g)) : ℤ)-
      negative (atCell row.val (r.U+col.val) (gate r g))=
      if GateCondition r g row col then weight r g else 0 := by
  classical
  rw [gate_cell]
  split <;> simp

end NearCubicWires.RepairOrdinary.CompetitorSameBucketEntries
