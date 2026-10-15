import Proof.Hierarchy.CompetitorSameBucketRankMeaning

/-! Literal fixed packet chunks are exactly the canonical stable buckets.
The proof uses positions recorded by the actual rank annotator and includes
all padded cells, so no alternative bucket partition is supplied. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketRankMeaning
open MatrixScoreBatch SupplierPrinter CompetitorSameBucketPacketRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem chunks_get {α : Type} (b n : ℕ) (xs : List α) (i : ℕ) (hi : i < n) :
    (chunks b n xs)[i]'(by simpa only [chunks_length] using hi)=(xs.drop (i*b)).take b := by
  induction n generalizing xs i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [chunks]
    | succ i =>
      have hit : i < n := by omega
      simp only [chunks,List.getElem_cons_succ]
      rw [ih _ i hit,List.drop_drop]
      have he : b+i*b=(i+1)*b := by ring
      rw [he]

theorem chunks_member {α : Type} (b n : ℕ) (xs ys : List α) :
    ys∈chunks b n xs ↔ ∃ i,i < n ∧ ys=(xs.drop (i*b)).take b := by
  constructor
  · intro hy
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hy
    have hit : i < n := by simpa only [chunks_length] using hi
    exact ⟨i,hit,he.symm.trans (chunks_get b n xs i hit)⟩
  · rintro ⟨i,hi,rfl⟩
    exact List.mem_iff_getElem.mpr ⟨i,by simpa only [chunks_length] using hi,chunks_get b n xs i hi⟩

theorem slice_member {α : Type} (xs : List α) (a : α) (offset b : ℕ) :
    a∈(xs.drop offset).take b ↔ ∃ i,offset ≤ i ∧ i < offset+b ∧ xs[i]?=some a := by
  constructor
  · intro ha
    obtain ⟨j,hj⟩:=List.mem_iff_getElem?.mp ha
    have hlen:=(List.getElem?_eq_some_iff.mp hj).1
    have hsmall : j < b := by rw [List.length_take] at hlen;omega
    rw [List.getElem?_take_of_lt hsmall,List.getElem?_drop] at hj
    exact ⟨offset+j,by omega,by omega,hj⟩
  · rintro ⟨i,hlo,hhi,hi⟩
    apply List.mem_iff_getElem?.mpr
    refine ⟨i-offset,?_⟩
    rw [List.getElem?_take_of_lt (by omega : i-offset < b),List.getElem?_drop,Nat.add_sub_of_le hlo]
    exact hi

theorem packet_member (r : Request) (g : Fin r.Gates) (e : KeyLoop.Record) :
    some e∈CompetitorSameBucketPackets.records r g ↔ e∈MatrixScoreRawRanks.entries r g := by
  simp [CompetitorSameBucketPackets.records]

theorem packet_rank_bound (r : Request) (g : Fin r.Gates) (e : KeyLoop.Record)
    (he : some e∈CompetitorSameBucketPackets.records r g) : e.2.2/(r.bucketSize+1) < r.Buckets := by
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp he
  have hr:=packet_position r g i e hi
  have hlen:=(List.getElem?_eq_some_iff.mp hi).1
  rw [CompetitorSameBucketPackets.records_length] at hlen
  rw [hr]
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
  exact hlen

theorem packet_slice (r : Request) (g : Fin r.Gates) (bucket : ℕ) (e : KeyLoop.Record) :
    some e∈((CompetitorSameBucketPackets.records r g).drop (bucket*(r.bucketSize+1))).take (r.bucketSize+1) ↔
      some e∈CompetitorSameBucketPackets.records r g ∧ e.2.2/(r.bucketSize+1)=bucket := by
  rw [slice_member]
  constructor
  · rintro ⟨i,hlo,hhi,hi⟩
    have hr:=packet_position r g i e hi
    refine ⟨List.mem_iff_getElem?.mpr ⟨i,hi⟩,?_⟩
    rw [hr]
    apply Nat.div_eq_of_lt_le hlo
    have he : (bucket+1)*(r.bucketSize+1)=bucket*(r.bucketSize+1)+(r.bucketSize+1) := by ring
    rwa [he]
  · rintro ⟨he,hbucket⟩
    obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp he
    have hr:=packet_position r g i e hi
    have hb:=(Nat.div_eq_iff (Nat.succ_pos r.bucketSize)).mp hbucket
    rw [hr] at hb
    change bucket*(r.bucketSize+1) ≤ i ∧ i ≤ bucket*(r.bucketSize+1)+(r.bucketSize+1)-1 at hb
    exact ⟨i,hb.1,by omega,hi⟩

theorem same_row_iff (r : Request) (g : Fin r.Gates) (a b : KeyLoop.Record) :
    (∃ xs∈rows r g,some a∈xs ∧ some b∈xs) ↔
      some a∈CompetitorSameBucketPackets.records r g ∧ some b∈CompetitorSameBucketPackets.records r g ∧
      a.2.2/(r.bucketSize+1)=b.2.2/(r.bucketSize+1) := by
  constructor
  · rintro ⟨xs,hxs,ha,hb⟩
    obtain ⟨i,_,rfl⟩:= (chunks_member (r.bucketSize+1) r.Buckets (CompetitorSameBucketPackets.records r g) xs).mp hxs
    obtain ⟨ha,hai⟩:= (packet_slice r g i a).mp ha
    obtain ⟨hb,hbi⟩:= (packet_slice r g i b).mp hb
    exact ⟨ha,hb,hai.trans hbi.symm⟩
  · rintro ⟨ha,hb,he⟩
    let bucket:=a.2.2/(r.bucketSize+1)
    have hbucket : bucket < r.Buckets := packet_rank_bound r g a ha
    refine ⟨((CompetitorSameBucketPackets.records r g).drop (bucket*(r.bucketSize+1))).take (r.bucketSize+1),?_,?_,?_⟩
    · apply (chunks_member (r.bucketSize+1) r.Buckets (CompetitorSameBucketPackets.records r g) _).mpr
      exact ⟨bucket,hbucket,rfl⟩
    · exact (packet_slice r g bucket a).mpr ⟨ha,rfl⟩
    · exact (packet_slice r g bucket b).mpr ⟨hb,he.symm⟩

theorem canonical_same_row (r : Request) (g : Fin r.Gates) (row col : Fin r.U) :
    (∃ xs∈rows r g,some (ranked r g (.inl row))∈xs ∧ some (ranked r g (.inr col))∈xs) ↔
      (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize).leftBucket row g=
      (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize).rightBucket g col := by
  rw [same_row_iff]
  have hl:=(packet_member r g _).mpr (copy_present r g (.inl row))
  have hr:=(packet_member r g _).mpr (copy_present r g (.inr col))
  simp only [hl,hr,true_and]
  rw [Fin.ext_iff]
  rfl

end NearCubicWires.RepairOrdinary.CompetitorSameBucketRankMeaning
