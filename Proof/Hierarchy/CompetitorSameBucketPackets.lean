import Proof.Hierarchy.CompetitorSameBucketRankWorkspace

/-! Proof view of the actual padded ranked packet as fixed-width records.
`none` is only a description of existing false backing; no new tag/codec is
written. Every real record retains the existing ranked occurrence framing. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPackets
open LocalBitMultitape MatrixScoreBatch MatrixBatchBucketEndpoints
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (r : Request) := 4*H r+1
def count (r : Request) := r.Buckets*(r.bucketSize+1)
noncomputable def records (r : Request) (gate : Fin r.Gates) : List (Option KeyLoop.Record) :=
  (MatrixScoreRawRanks.entries r gate).map some++List.replicate (count r-(r.U+r.U)) none

def word (r : Request) : Option KeyLoop.Record → List Bool
  | none => List.replicate (width r) false
  | some e => CompetitorSameBucketRankFields.source r.S r.M e.1 e.2.1 e.2.2

theorem word_length (r : Request) (e : Option KeyLoop.Record) : (word r e).length=width r := by
  cases e with
  | none => simp [word]
  | some e => simp [word,CompetitorSameBucketRankFields.source,KeyLoop.word_length,width,H]; omega

theorem count_bounds (r : Request) : r.U+r.U<count r ∧ count r≤5*r.U := by
  have hu := dimension_positive r
  have hb : r.bucketSize+1≤2*r.U+1 := CompetitorSameBucket.block_width_le r.U r.Capacity r.Gates
  have hdiv := Nat.div_mul_le_self (r.U+r.U) (r.bucketSize+1)
  have hmod := Nat.mod_lt (r.U+r.U) (by omega : 0<r.bucketSize+1)
  have hparts := Nat.mod_add_div (r.U+r.U) (r.bucketSize+1)
  change r.U+r.U<((r.U+r.U)/(r.bucketSize+1)+1)*(r.bucketSize+1) ∧
    ((r.U+r.U)/(r.bucketSize+1)+1)*(r.bucketSize+1)≤5*r.U
  constructor <;> nlinarith

theorem records_length (r : Request) (gate : Fin r.Gates) : (records r gate).length=count r := by
  have hc := (count_bounds r).1
  simp [records,MatrixBucketCallBounds.entries_length]
  omega

theorem packet_fits (r : Request) : count r*width r≤MatrixScoreReusableRanks.D r := by
  have hc := (count_bounds r).2
  have hH : H r≤8*(r.d+r.p+1) := by
    have h := MatrixScoreRawRanksBounds.header_width r
    unfold H
    omega
  have hwidth : width r≤33*(r.d+r.p+1) := by unfold width; omega
  have hm := Nat.mul_le_mul hc hwidth
  have hq : r.d+r.p+1≤(r.d+r.p+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (165*r.U) hq
  have hd := MatrixScoreReusableRanks.capacity_gap r
  unfold MatrixScoreRawRanksBounds.capacity at hd
  nlinarith

theorem pad_tail (cap : ℕ) (bits : List Bool) (n : ℕ) (hc : bits.length+n≤cap) :
    ZeroPadding.pad cap (bits++List.replicate n false)=ZeroPadding.pad cap bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc,←List.replicate_add]
  congr 2
  omega

theorem bits (r : Request) (gate : Fin r.Gates) :
    (records r gate).flatMap (word r)=KeyLoop.fields r.S r.M (MatrixScoreRawRanks.entries r gate)++
      List.replicate ((count r-(r.U+r.U))*width r) false := by
  unfold records
  rw [List.flatMap_append,List.flatMap_map]
  have he : (fun e => word r (some e))=(fun e : KeyLoop.Record =>
      frame (KeyLoop.word r.S r.M e++SignedSortKey.binary (r.M+r.S+1) e.2.2)) := by
    funext e
    rcases e with ⟨score,id,rank⟩
    rfl
  rw [he]
  change KeyLoop.fields r.S r.M (MatrixScoreRawRanks.entries r gate)++
    (List.replicate (count r-(r.U+r.U)) none).flatMap (word r)=_
  congr 1
  induction count r-(r.U+r.U) with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.flatMap_cons,word,ih,Nat.succ_mul,←List.replicate_add]
    congr 1
    omega

theorem actual_padding (r : Request) (gate : Fin r.Gates) :
    ZeroPadding.pad (MatrixScoreReusableRanks.D r) (MatrixScoreRawRanks.output r gate)=
      ZeroPadding.pad (MatrixScoreReusableRanks.D r) ((records r gate).flatMap (word r)) := by
  let fields := KeyLoop.fields r.S r.M (MatrixScoreRawRanks.entries r gate)
  have hfields : fields.length=(r.U+r.U)*width r := by
    rw [show fields.length=(MatrixScoreRawRanks.entries r gate).length*(4*H r+1) from by
      have hL (e : KeyLoop.Record) :
          (frame (KeyLoop.word r.S r.M e++SignedSortKey.binary (r.M+r.S+1) e.2.2)).length=4*H r+1 := by
        simp [H]
        omega
      simp only [fields,KeyLoop.fields,List.length_flatMap,hL]
      simp]
    rw [MatrixBucketCallBounds.entries_length]
    rfl
  have hc := (count_bounds r).1
  have hf := packet_fits r
  have hprod : (r.U+r.U)*width r+(count r-(r.U+r.U))*width r=count r*width r := by
    rw [←Nat.add_mul,Nat.add_sub_of_le (by omega)]
  have htail : fields.length+(count r-(r.U+r.U))*width r≤MatrixScoreReusableRanks.D r := by
    rw [hfields,hprod]
    exact hf
  have hone : fields.length+1≤MatrixScoreReusableRanks.D r := by
    have hw : 1≤width r := by unfold width; omega
    have hm := Nat.mul_le_mul (by omega : 1≤count r-(r.U+r.U)) hw
    omega
  rw [bits,pad_tail _ _ _ htail]
  change ZeroPadding.pad (MatrixScoreReusableRanks.D r) (fields++[false])=ZeroPadding.pad _ fields
  exact pad_tail _ fields 1 hone

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPackets
