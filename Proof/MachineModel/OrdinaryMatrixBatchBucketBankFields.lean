import Proof.MachineModel.OrdinaryMatrixBucketTemplate

/-! All five cold scanner-bank inputs are fields retained by the same
original-request execution, including its paid shared capacity counter. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketBankFields
open LocalBitMultitape SignedSortKey MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 306 := ![130,295,291,299,222]
def fields (r : Request) : Fin 5 → List Bool :=
  ![List.replicate (MatrixScoreReusableRanks.D r) true,frame (binary (H r) 0),
    frame (binary (H r) (r.bucketSize+1)),frame (binary r.M 0),UnaryTemplate.tape r.Buckets]

theorem count_field (r : Request) :
    ∃ actual,run MatrixBatchBucketUsage.machine (MatrixBatchBucketUsage.budget r)
      (MatrixBatchBucketUsage.input r)=some actual ∧
      actual.final.tapes 222=UnaryTemplate.tape r.Buckets ∧ actual.final.heads 222=0 := by
  obtain ⟨native,hn,n89,h89,n222,h222,n166,h166,ns⟩ := MatrixBatchBucketUsage.source_fields r
  obtain ⟨actual,ha,atapes,ah,_,_,_,_,_⟩ := MatrixBatchBucketUsage.usage_run r native hn
    n89 h89 n222 h222 n166 h166 ns
  exact ⟨actual,ha,(atapes 222).trans n222,(ah 222).trans h222⟩

theorem source_fields (r : Request) :
    ∃ actual,run MatrixBatchRankReverse.machine (MatrixBatchRankReverse.budget r)
      (MatrixBatchRankReverse.input r)=some actual ∧
      (∀ j,actual.final.tapes (slots j)=fields r j) ∧
      (∀ j,actual.final.heads (slots j)=0) ∧ actual.steps ≤ MatrixBatchRankReverse.budget r := by
  obtain ⟨state,ranked,used,_,rt,rh,hu,ut,uh,_,_,_,_,_,_,_,_,_,_,_⟩ := MatrixBatchRetainedFields.retained_run r
  obtain ⟨same,hc,c222,h222⟩ := count_field r
  have heq : same=used := Option.some.inj (hc.symm.trans hu)
  subst same
  obtain ⟨same,endpoints,hs,he,et,eh,_,_,e291,h291,e295,h295,e299,h299,_⟩ := MatrixBatchBucketEndpoints.raw_run r
  have heq : same=used := Option.some.inj (hs.symm.trans hu)
  subst same
  obtain ⟨same,actual,hs,ha,atapes,ah,_,_,_,_,_,_,_,_,_,_,_,_,as⟩ := MatrixBatchRankReverse.raw_run r
  have heq : same=endpoints := Option.some.inj (hs.symm.trans he)
  subst same
  have uD : used.final.tapes 130=List.replicate (MatrixScoreReusableRanks.D r) true :=
    (ut 130).trans ((rt 44).trans (MatrixBatchRootCapacity.native_d r state))
  have hD : used.final.heads 130=0 := (uh 130).trans (by exact rh 44)
  refine ⟨actual,ha,?_,?_,as⟩
  · intro j
    fin_cases j
    · exact (atapes 130 (by decide)).trans ((et 130).trans uD)
    · exact (atapes 295 (by decide)).trans e295
    · exact (atapes 291 (by decide)).trans e291
    · exact (atapes 299 (by decide)).trans e299
    · exact (atapes 222 (by decide)).trans ((et 222).trans c222)
  · intro j
    fin_cases j
    · exact (ah 130).trans ((eh 130).trans hD)
    · exact (ah 295).trans h295
    · exact (ah 291).trans h291
    · exact (ah 299).trans h299
    · exact (ah 222).trans ((eh 222).trans h222)

theorem capacity_fit (r : Request) :
    4*H r+3 ≤ MatrixScoreReusableRanks.D r ∧ 4*r.M+3 ≤ MatrixScoreReusableRanks.D r := by
  have hc := MatrixScoreReusableRanks.capacity_gap r
  have hw := MatrixScoreRawRanksBounds.header_width r
  have hq : r.d+r.p+1 ≤ (r.d+r.p+1)^2 := by nlinarith
  have hu : 1 ≤ r.U+1 := by omega
  have hm := Nat.mul_le_mul_right ((r.d+r.p+1)^2) hu
  unfold MatrixScoreRawRanksBounds.capacity at hc
  unfold H
  constructor <;> nlinarith

end NearCubicWires.RepairOrdinary.MatrixBatchBucketBankFields
