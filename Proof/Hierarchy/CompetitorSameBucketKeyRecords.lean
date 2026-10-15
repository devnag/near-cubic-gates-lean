import Proof.Hierarchy.CompetitorSameBucketColdZeroGrid

/-! Typed records of the exact emitted same-bucket stream. This supplies
the existing sorter's uniform-width input and its U² record-count bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyRecords
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch
open CompetitorSameBucketKeys (key zeroRecords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pair (r : Request) (coefficient : ℤ) (left right : Option KeyLoop.Record) : List StablePartition.Record :=
  match left,right with
  | some a,some b => if CompetitorSameBucketPairCompare.fires r.U a.2.1 b.2.1 a.2.2 b.2.2 then
      [key r.p r.M coefficient a.2.1 b.2.1] else []
  | _,_ => []
noncomputable def gate (r : Request) (g : Fin r.Gates) : List StablePartition.Record :=
  (CompetitorSameBucketPacketRows.rows r g).flatMap (fun xs => xs.flatMap (fun a =>
    xs.flatMap (fun b => pair r (weight r g) a b)))
noncomputable def contributions (r : Request):=(List.finRange r.Gates).flatMap (gate r)
noncomputable def records (r : Request):=contributions r++zeroRecords r.p r.M r.U

theorem pair_word (r : Request) (coefficient : ℤ) (a b : Option KeyLoop.Record) :
    CompetitorSameBucketCandidate.pairBits r coefficient a b=
      (pair r coefficient a b).flatMap (fun e=>frame (RadixSemantics.word e)) := by
  cases a <;> cases b <;> simp [pair,CompetitorSameBucketCandidate.pairBits,
    CompetitorSameBucketCandidate.pairOutput,CompetitorSameBucketPairEmit.output]
  split <;> simp_all [CompetitorSameBucketKeyAppend.word]

theorem contribution_word (r : Request) : CompetitorSameBucketGateNative.output r=
    (contributions r).flatMap (fun e=>frame (RadixSemantics.word e)) := by
  simp only [contributions,gate,CompetitorSameBucketGateNative.output,CompetitorSameBucketGateLoop.emissions,
    CompetitorSameBucketGateScan.output,CompetitorSameBucketBucketLoop.emissions,
    CompetitorSameBucketOuterLoop.emissions,CompetitorSameBucketCandidate.emissions,List.flatMap_assoc,←pair_word]

theorem output_word (r : Request) : CompetitorSameBucketColdZeroGrid.output r=
    (records r).flatMap (fun e=>frame (RadixSemantics.word e)) := by
  rw [CompetitorSameBucketColdZeroGrid.output,contribution_word,CompetitorSameBucketZeroGrid.zero_records]
  simp only [records,List.flatMap_append]

private theorem flatMap_bound {α β : Type} (f : α → List β) (xs : List α) (k : ℕ)
    (hf : ∀ x∈xs,(f x).length≤k) : (xs.flatMap f).length≤xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha:=hf a (by simp)
    have ht:=ih (by intro x hx; exact hf x (by simp [hx]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

theorem pair_length (r : Request) (coefficient : ℤ) (a b : Option KeyLoop.Record) : (pair r coefficient a b).length≤1 := by
  cases a <;> cases b <;> simp [pair]
  split <;> simp

theorem gate_length (r : Request) (g : Fin r.Gates) :
    (gate r g).length≤r.Buckets*(r.bucketSize+1)^2 := by
  unfold gate
  have h:=flatMap_bound (fun xs=>xs.flatMap (fun a=>xs.flatMap (fun b=>pair r (weight r g) a b)))
    (CompetitorSameBucketPacketRows.rows r g) ((r.bucketSize+1)^2) (by
      intro xs hxs
      have size:=CompetitorSameBucketPacketRows.rows_size r g xs hxs
      have outer:=flatMap_bound (fun a=>xs.flatMap (fun b=>pair r (weight r g) a b)) xs xs.length (by
        intro a _
        simpa using flatMap_bound (fun b=>pair r (weight r g) a b) xs 1 (by intro b _; exact pair_length r _ a b))
      simpa [size,pow_two] using outer)
  simpa [CompetitorSameBucketPacketRows.rows_length] using h

theorem records_length (r : Request) : (records r).length≤26*r.U^2 := by
  have h:=flatMap_bound (gate r) (List.finRange r.Gates) (r.Buckets*(r.bucketSize+1)^2)
    (by intro g _; exact gate_length r g)
  simp only [List.length_finRange] at h
  have aggregate:=CompetitorSameBucket.request_all_pairs r
  have hn:=CompetitorSameBucketKeys.zero_count r.p r.M r.U
  simp only [records,List.length_append,contributions]
  nlinarith

theorem pair_width (r : Request) (coefficient : ℤ) (a b : Option KeyLoop.Record)
    (e : StablePartition.Record) (he : e∈pair r coefficient a b) : (RadixSemantics.word e).length=r.p+2+2*r.M := by
  cases a <;> cases b <;> simp [pair] at he
  rw [he.2]
  exact CompetitorSameBucketKeys.key_width ..

theorem uniform_width (r : Request) : ∀ e∈records r,(RadixSemantics.word e).length=r.p+2+2*r.M := by
  intro e he
  rcases List.mem_append.mp he with he|he
  · simp only [contributions,gate,List.mem_flatMap] at he
    obtain ⟨g,_,xs,_,a,_,b,_,he⟩:=he
    exact pair_width r (weight r g) a b e he
  · exact CompetitorSameBucketKeys.zero_width r.p r.M r.U e he

theorem nonempty (r : Request) : records r≠[] := by
  intro he
  have hu:=MatrixScoreBatch.dimension_positive r
  have hlen:=congrArg List.length he
  simp only [records,List.length_append,CompetitorSameBucketKeys.zero_count,List.length_nil] at hlen
  nlinarith

theorem sort_width (r : Request) : SortPreparation.width (records r)=r.p+2+2*r.M := by
  have h:=uniform_width r
  cases he : records r with
  | nil => exact False.elim (nonempty r he)
  | cons a xs =>
    have ha:=h a (by simp [he])
    simpa [he,SortPreparation.width,SortPreparation.firstWord] using ha

theorem sort_uniform (r : Request) : ∀ e∈records r,
    (RadixSemantics.word e).length=SortPreparation.width (records r) := by
  rw [sort_width]
  exact uniform_width r

end NearCubicWires.RepairOrdinary.CompetitorSameBucketKeyRecords
