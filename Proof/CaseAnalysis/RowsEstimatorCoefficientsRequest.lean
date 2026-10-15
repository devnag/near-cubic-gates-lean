import Proof.CaseAnalysis.RowsEstimatorCoefficientsAppend
import Proof.Hierarchy.CompetitorCountTableRecord

/-! The unchanged selected-count and actual count-table programs append
unreduced coefficient fields. Their counts still come from the original
physical table and selected SUM, never from a supplied count numeral. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairRepresentation MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorRationalDecision
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace CountRequest
open CompetitorCountRecordRequest

def extra (b : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ) (i : Fin 27) : List Bool :=
  match i.val with
    | 22 => frame (binary (width b) (q.positive))
    | 23 => frame (binary (width b) (q.negative))
    | 24 => frame (binary (width b) q.denominator)
    | 25 => frame (binary b denominator)
    | _ => []
def input (r : Request) (Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ)) : Fin 118 → List Bool :=
  Fin.addCases (m := 91) (n := 27) (motive := fun _ => List Bool)
    (CompetitorSelectedRequestCount.input r Q xs) (extra (scalarWidth r Q) q denominator)
theorem append_dock {s : ℕ} (base : ExecutionReceipt 91 s) (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ)
    (source : List Bool) (b86 : base.final.tapes 86=frame (binary b count))
    (b76 : base.final.tapes 76=List.replicate b true) (bh86 : base.final.heads 86=0)
    (bh76 : base.final.heads 76=0) (b0 : base.final.tapes 0=source) :
    ∃ tail,runFrom CompetitorCountRecordRequest.last (CompetitorCountRecordAppend.budget b)
      (Composition.restart (TapeEmbedding.receipt (fun _ : Fin 27 => 0) (extra b q denominator) base).final CompetitorCountRecordRequest.last.start)=some tail ∧
      tail.steps≤CompetitorCountRecordAppend.budget b ∧
      tail.final.tapes 117=Stream.recordWord b q count denominator ∧
      tail.final.heads 117=(Stream.recordWord b q count denominator).length ∧
      tail.final.tapes 0=source := by
  let ext := extra b q denominator
  let before := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext base
  have hnew (j : Fin 27) : before.final.heads (j.natAdd 91)=0 :=
    TapeEmbedding.receipt_heads_new _ _ base j
  have tnew (j : Fin 27) : before.final.tapes (j.natAdd 91)=ext j :=
    TapeEmbedding.receipt_tapes_new _ _ base j
  obtain ⟨app,ha,as,appTape,ah,_,_⟩ := Append.record_run b q count denominator
  have ht : ∀ j,before.final.tapes (CompetitorCountRecordRequest.slots j)=
      Append.input b q count denominator j := by
    intro j
    fin_cases j
    · exact b76
    · exact tnew 0
    · exact tnew 1
    · exact tnew 2
    · exact tnew 3
    · exact tnew 4
    · exact tnew 5
    · exact tnew 6
    · exact tnew 7
    · exact tnew 8
    · exact tnew 9
    · exact tnew 10
    · exact tnew 11
    · exact tnew 12
    · exact tnew 13
    · exact tnew 14
    · exact tnew 15
    · exact tnew 16
    · exact tnew 17
    · exact tnew 18
    · exact tnew 19
    · exact tnew 20
    · exact tnew 21
    · exact tnew 22
    · exact tnew 23
    · exact tnew 24
    · exact tnew 25
    · exact b86
    · exact tnew 26
  have hh : ∀ j,before.final.heads (CompetitorCountRecordRequest.slots j)=0 := by
    intro j
    fin_cases j
    · exact bh76
    · exact hnew 0
    · exact hnew 1
    · exact hnew 2
    · exact hnew 3
    · exact hnew 4
    · exact hnew 5
    · exact hnew 6
    · exact hnew 7
    · exact hnew 8
    · exact hnew 9
    · exact hnew 10
    · exact hnew 11
    · exact hnew 12
    · exact hnew 13
    · exact hnew 14
    · exact hnew 15
    · exact hnew 16
    · exact hnew 17
    · exact hnew 18
    · exact hnew 19
    · exact hnew 20
    · exact hnew 21
    · exact hnew 22
    · exact hnew 23
    · exact hnew 24
    · exact hnew 25
    · exact bh86
    · exact hnew 26
  obtain ⟨tail,htail,_,ts,th,tt,keep⟩ := RecoveryFocus.dock CompetitorCountRecordRequest.slots (by decide)
    CompetitorCountRecordAppend.machine _ before.final.heads before.final.tapes _ hh ht app ha
  have ht' : runFrom CompetitorCountRecordRequest.last (CompetitorCountRecordAppend.budget b)
      (Composition.restart before.final CompetitorCountRecordRequest.last.start)=some tail := htail
  exact ⟨tail,ht',ts.trans_le as,(tt 28).trans appTape,
    (th 28).trans (by rw [ah,Function.update_self]),((keep 0 (by decide)).2).trans b0⟩

theorem program_run {s : ℕ} (p : Machine 91 s) (fuel : ℕ) (data : Fin 91 → List Bool)
    (base : ExecutionReceipt 91 s) (hr : run p fuel data=some base) (bs : base.steps≤fuel)
    (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator : ℕ) (source : List Bool)
    (b86 : base.final.tapes 86=frame (binary b count))
    (b76 : base.final.tapes 76=List.replicate b true) (bh86 : base.final.heads 86=0)
    (bh76 : base.final.heads 76=0) (b0 : base.final.tapes 0=source) : ∃ actual,
    run (Composition.machine (TapeEmbedding.machine 27 p) CompetitorCountRecordRequest.last)
      (fuel+1+CompetitorCountRecordAppend.budget b)
      (Fin.addCases (m := 91) (n := 27) (motive := fun _ => List Bool) data (extra b q denominator))=some actual ∧
      actual.steps≤fuel+1+CompetitorCountRecordAppend.budget b ∧
      actual.final.tapes 117=Stream.recordWord b q count denominator ∧
      actual.final.heads 117=(Stream.recordWord b q count denominator).length ∧
      actual.final.tapes 0=source := by
  let ext := extra b q denominator
  have hfirst := TapeEmbedding.run_embed p (fun _ : Fin 27 => 0) ext _ _ base hr
  let before := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext base
  obtain ⟨tail,htail,ts,tt,th,t0⟩ := append_dock base b q count denominator source b86 b76 bh86 bh76 b0
  have hall := Composition.run_join (TapeEmbedding.machine 27 p) CompetitorCountRecordRequest.last _ _ _ before tail hfirst htail
  have hcost : before.steps+1+tail.steps≤fuel+1+CompetitorCountRecordAppend.budget b := by
    change base.steps+1+tail.steps≤fuel+1+CompetitorCountRecordAppend.budget b
    omega
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 27 => 0) ext
      (initialConfiguration p data))=initialConfiguration
      (Composition.machine (TapeEmbedding.machine 27 p) CompetitorCountRecordRequest.last)
      (Fin.addCases (m := 91) (n := 27) (motive := fun _ => List Bool) data ext) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left]
      · simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_right]
    · rfl
  rw [hi] at hall
  exact ⟨Composition.joinedReceipt before tail,hall,hcost,tt,th,t0⟩

theorem record_run (r : Request) (Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (hx : ∀ x∈selected xs,x<2^Q) : ∃ actual,
    run CompetitorCountRecordRequest.machine (CompetitorCountRecordRequest.budget r Q) (input r Q q denominator xs)=some actual ∧ actual.steps≤CompetitorCountRecordRequest.budget r Q ∧
      actual.final.tapes 117=Stream.recordWord (scalarWidth r Q) q (selected xs).sum denominator ∧
      actual.final.heads 117=(Stream.recordWord (scalarWidth r Q) q (selected xs).sum denominator).length ∧
      actual.final.tapes 0=MatrixScoreBatch.physicalInput r := by
  obtain ⟨base,hbase,bs,b86,b76,bh86,bh76,b0⟩ := CompetitorCountRecordRequestInput.selected_run r Q xs hn hx
  exact program_run CompetitorSelectedRequestCount.machine (CompetitorSelectedRequestCount.budget r Q)
    (CompetitorSelectedRequestCount.input r Q xs) base hbase bs (scalarWidth r Q) q
    (selected xs).sum denominator (MatrixScoreBatch.physicalInput r) b86 b76 bh86 bh76 b0

end CountRequest

namespace Table
open CompetitorCountTableRecord

def input (p : Program) (r : Request) (Q : ℕ) (odd : Bool)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ)) :=
  Fin.addCases (m := CompetitorSelectedTable.tapes p) (n := 27) (motive := fun _ => List Bool)
    (CompetitorSelectedTable.extend p xs (CompetitorCountTable.input p r Q odd))
    (CountRequest.extra (scalarWidth r Q) q denominator)
theorem record_run (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) (odd : Bool)
    (f : Fin r.U → Fin r.U → ℕ) (select : Fin r.U → Fin r.U → Bool)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (hQ : Q≤CompetitorSameBucketColdDense.width r)
    (he : odd=true → r.U/2+r.U/2=r.U)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin (r.U*r.U),Int.ModEq ((2 : ℤ)^Q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ actual,run (CompetitorCountTableRecord.machine a) (CompetitorCountTableRecord.budget a r Q)
      (input (producer a) r Q odd q denominator (CompetitorSelectedCells.cells odd f select))=some actual ∧
      actual.steps≤CompetitorCountTableRecord.budget a r Q ∧
      actual.final.tapes (CompetitorCountTableRecord.slots (producer a) 117)=Stream.recordWord
        (scalarWidth r Q) q (selected (CompetitorSelectedCells.cells odd f select)).sum denominator ∧
      actual.final.heads (CompetitorCountTableRecord.slots (producer a) 117)=(Stream.recordWord
        (scalarWidth r Q) q (selected (CompetitorSelectedCells.cells odd f select)).sum denominator).length ∧
      actual.final.tapes (CompetitorCountTableRecord.slots (producer a) 0)=MatrixScoreBatch.physicalInput r := by
  let p := producer a
  let xs := CompetitorSelectedCells.cells odd f select
  let ext := CountRequest.extra (scalarWidth r Q) q denominator
  obtain ⟨base,hbase,bs,bh,bt,bQ,_,_,b0⟩ := CompetitorCountTable.cold_run a r Q odd f hQ he
    (fun i => hf i.divNat i.modNat) hc
  let middle : ExecutionReceipt (CompetitorSelectedTable.tapes p) _ :=
    TapeEmbedding.receipt (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs) base
  let before : ExecutionReceipt (CompetitorCountTableRecord.tapes p) _ := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle
  have hmid := TapeEmbedding.run_embed (CompetitorCountTable.machine a) (fun _ : Fin 92 => 0)
    (CompetitorSelectedTable.extra xs) _ _ base hbase
  have hfirst := TapeEmbedding.run_embed (TapeEmbedding.machine 92 (CompetitorCountTable.machine a))
    (fun _ : Fin 27 => 0) ext _ _ middle hmid
  have hcword : base.final.tapes (CompetitorCountTable.slot p 141)=CompetitorCountFold.raw Q (counts xs) :=
    bt.trans (CompetitorSelectedCells.cells_word Q odd f select).symm
  have hmheads : middle.final.heads=CompetitorSelectedTable.heads p (MatrixScoreBatch.output r).length := by
    change Fin.addCases (m := CompetitorCountTable.tapes p) (n := 92)
      (motive := fun _ => ℕ) base.final.heads (fun _ : Fin 92 => 0)=_
    rw [bh]
    rfl
  have hhead : ∀ i,before.final.heads (CompetitorCountTableRecord.slots p i)=0 := by
    intro i
    refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro j
    · simp only [CompetitorCountTableRecord.slots,Fin.addCases_left]
      change (TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle).final.heads
        ((CompetitorSelectedTable.slot p j).castAdd 27)=0
      rw [TapeEmbedding.receipt_heads_old]
      rw [hmheads]
      exact CompetitorSelectedTable.slot_heads p _ j
    · simp only [CompetitorCountTableRecord.slots,Fin.addCases_right]
      exact TapeEmbedding.receipt_heads_new (fun _ : Fin 27 => 0) ext middle j
  have htape : ∀ i,before.final.tapes (CompetitorCountTableRecord.slots p i)=CountRequest.input r Q q denominator xs i := by
    intro i
    refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro j
    · simp only [CompetitorCountTableRecord.slots,CountRequest.input,Fin.addCases_left]
      change (TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle).final.tapes
        ((CompetitorSelectedTable.slot p j).castAdd 27)=_
      rw [TapeEmbedding.receipt_tapes_old]
      change CompetitorSelectedTable.extend p xs base.final.tapes (CompetitorSelectedTable.slot p j)=
        CompetitorSelectedRequestCount.input r Q xs j
      exact CompetitorSelectedTable.extend_slot p r Q xs base.final.tapes b0 bQ hcword j
    · simp only [CompetitorCountTableRecord.slots,CountRequest.input,Fin.addCases_right]
      exact TapeEmbedding.receipt_tapes_new (fun _ : Fin 27 => 0) ext middle j
  obtain ⟨child,ch,cs,ct,co,c0⟩ := CountRequest.record_run r Q q denominator xs
    (CompetitorSelectedCells.cells_length odd f select) (CompetitorSelectedCells.cells_fit Q odd f select hf)
  obtain ⟨tail,th,_,ts,hh,tt,_⟩ := RecoveryFocus.dock (CompetitorCountTableRecord.slots p) (CompetitorCountTableRecord.slots_injective p)
    CompetitorCountRecordRequest.machine _ before.final.heads before.final.tapes _ hhead htape child ch
  have htail : runFrom (CompetitorCountTableRecord.last p) (CompetitorCountRecordRequest.budget r Q)
      (Composition.restart before.final (CompetitorCountTableRecord.last p).start)=some tail := th
  have hj := Composition.run_join (CompetitorCountTableRecord.first a) (CompetitorCountTableRecord.last p) _ _ _ before tail hfirst htail
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 27 => 0) ext
      (TapeEmbedding.config (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs)
        (initialConfiguration (CompetitorCountTable.machine a) (CompetitorCountTable.input p r Q odd))))=
      initialConfiguration (CompetitorCountTableRecord.machine a) (input p r Q odd q denominator xs) := by
    apply configuration_ext
    · rfl
    · funext i
      dsimp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
      change Fin.addCases (m := CompetitorSelectedTable.tapes p) (n := 27) (motive := fun _ => ℕ)
        (Fin.addCases (m := CompetitorCountTable.tapes p) (n := 92) (motive := fun _ => ℕ)
          (fun _ => 0) (fun _ => 0)) (fun _ => 0) i=0
      refine Fin.addCases (m := CompetitorSelectedTable.tapes p) (n := 27) ?_ ?_ i <;> intro j
      · refine Fin.addCases (m := CompetitorCountTable.tapes p) (n := 92) ?_ ?_ j <;> intro k <;>
          simp only [Fin.addCases_left,Fin.addCases_right]
      · simp only [Fin.addCases_right]
    · rfl
  rw [hi] at hj
  have hcost : before.steps+1+tail.steps≤CompetitorCountTableRecord.budget a r Q := by
    change base.steps+1+tail.steps≤_
    rw [ts]
    unfold CompetitorCountTableRecord.budget
    omega
  exact ⟨Composition.joinedReceipt before tail,hj,hcost,(tt 117).trans ct,(hh 117).trans co,(tt 0).trans c0⟩

end Table
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
