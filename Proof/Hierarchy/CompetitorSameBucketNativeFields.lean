import Proof.Hierarchy.CompetitorSameBucketNativeLayout
import Proof.Hierarchy.CompetitorSameBucketRetained

/-! Exact selected fields of the physical initialized workspace. This is
one finite layout check for the actual GateNative consumer, avoiding any
new bank or record codec. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdNativeFields
open LocalBitMultitape RecoveryRootRound
open MatrixScoreBatch (Request)
open MatrixBatchBucketEndpoints (H)
open CompetitorSameBucketColdNativeLayout (slots ambient entry advanced advances)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryData (r : Request) (j : Fin 56) : List Bool :=
  if h : j.val<41 then ambient r ⟨j.val,h⟩ else
    ![UnaryTemplate.tape (r.bucketSize+1),UnaryTemplate.tape (H r),List.replicate (MatrixScoreReusableRanks.D r) false,
      List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false,UnaryTemplate.tape (r.bucketSize+1),
      List.replicate (MatrixScoreReusableRanks.D r) true,List.replicate (MatrixScoreReusableRanks.D r+1) false,
      UnaryTemplate.tape ((4*H r+1)*(r.bucketSize+1)),List.replicate (MatrixScoreReusableRanks.D r) false,
      UnaryTemplate.tape r.Buckets,MatrixBatchGateNativeLoop.output r,MatrixCoefficientLoop.output r.p r.cuts,
      List.replicate (MatrixScoreReusableRanks.D r) false,List.replicate (CompetitorSameBucketBucketBody.scalarCapacity r) false,
      UnaryTemplate.tape r.Gates] ⟨j.val-41,by omega⟩
def entryHeads (j : Fin 56) : ℕ := if j=38 ∨ j=41 ∨ j=45 ∨ j=48 ∨ j=50 ∨ j=55 then 1 else 0

theorem entry_tapes (r : Request) : (entry r).tapes=entryData r := by
  rw [entry,CompetitorSameBucketGateNative.cfg_tapes]
  funext j
  fin_cases j <;> rfl

theorem entry_heads (r : Request) : (entry r).heads=entryHeads := by
  funext j
  fin_cases j <;> rfl

noncomputable def copiedTapes (r : Request) (base : Fin 398 → List Bool) :=
  CompetitorSameBucketColdCopies.output r
    (CompetitorSameBucketColdAllocate.output (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base)

theorem old_field (r : Request) (w : ℕ) (base : Fin 398 → List Bool)
    (hb : ∀ j,base (CompetitorSameBucketColdRetained.slots j)=CompetitorSameBucketColdRetained.values r w j)
    (j : Fin 17) : copiedTapes r base ((CompetitorSameBucketColdRetained.slots j).castAdd 44)=
      CompetitorSameBucketColdRetained.values r w j := by
  have old := (CompetitorSameBucketColdAllocate.output_old _ _ base (hb 9) (hb 13)
    (CompetitorSameBucketColdRetained.slots j)).trans (hb j)
  fin_cases j <;> simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,
    CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdRetained.slots] using old

theorem selected_tapes (r : Request) (w : ℕ) (base : Fin 398 → List Bool)
    (hb : ∀ j,base (CompetitorSameBucketColdRetained.slots j)=CompetitorSameBucketColdRetained.values r w j) :
    ∀ j,copiedTapes r base (slots j)=(entry r).tapes j := by
  intro j
  rw [entry_tapes]
  fin_cases j
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 0
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 1
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 2
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 3
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 4
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 5
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 6
  · simp [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient]
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 8
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 9
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 10
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 11
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 12
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 13
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 14
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 15
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 16
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 17
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 18
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 19
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 20
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 21
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 22
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 23
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 24
  · simp [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient]
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 26
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 27
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 28
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 29
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 30
  · simp [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient]
  · simp [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient]
  · simp [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient]
  · exact old_field r w base hb 2
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 34
  · exact old_field r w base hb 9
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_reset (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base
  · exact old_field r w base hb 10
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.packet_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 0
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 35
  · exact old_field r w base hb 5
  · exact old_field r w base hb 7
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.packet_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 1
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 36
  · exact old_field r w base hb 12
  · exact old_field r w base hb 13
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.packet_reset (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base
  · exact old_field r w base hb 11
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.packet_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 2
  · exact old_field r w base hb 6
  · exact old_field r w base hb 4
  · exact old_field r w base hb 8
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.packet_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 3
  · simpa [copiedTapes,CompetitorSameBucketColdCopies.output,CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,CompetitorSameBucketColdCopyFields.values,slots,entryData,ambient] using CompetitorSameBucketColdAllocate.scalar_cell (CompetitorSameBucketBucketBody.scalarCapacity r) (MatrixScoreReusableRanks.D r) base 37
  · exact old_field r w base hb 3

theorem selected_heads {s : ℕ} (r : Request) (c : Configuration 442 s)
    (ho : ∀ j,c.heads ((CompetitorSameBucketColdRetained.slots j).castAdd 44)=0)
    (hf : ∀ j : Fin 44,c.heads (j.natAdd 398)=0) :
    ∀ j,(advanced c).heads (slots j)=(entry r).heads j := by
  intro j
  rw [entry_heads]
  fin_cases j
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 0)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 1)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 2)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 3)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 4)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 5)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 6)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 7)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 8)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 9)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 10)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 11)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 12)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 13)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 14)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 15)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 16)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 17)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 18)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 19)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 20)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 21)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 22)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 23)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 24)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 25)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 26)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 27)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 28)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 29)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 30)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 31)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 32)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 33)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 2)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 34)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 9)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 38)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 10))
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 39)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 35)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 5))
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 7)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 40)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 36)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 12))
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 13)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 43)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 11))
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 41)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 6))
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 4)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (ho 8)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 42)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (hf 37)
  · simpa [advanced,advances,slots,entryHeads,CompetitorSameBucketColdRetained.slots] using (congrArg (fun n : ℕ => n+1) (ho 3))

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdNativeFields
