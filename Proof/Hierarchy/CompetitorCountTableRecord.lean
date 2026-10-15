import Proof.Hierarchy.CompetitorSelectedTableInput
import Proof.Hierarchy.CompetitorCountRecordRequestBounds

/-! Execute the actual natural count table and consume its output in place
in the request-derived six-field record caller. The row producer supplies
only its mask and coefficient/normalization fields, not the count stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open RepairRepresentation MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := CompetitorSelectedTable.tapes p+27
def slots (p : Program) : Fin 118 → Fin (tapes p) :=
  Fin.addCases (m := 91) (n := 27) (motive := fun _ => Fin (tapes p))
    (fun i => (CompetitorSelectedTable.slot p i).castAdd 27)
    (fun i => i.natAdd (CompetitorSelectedTable.tapes p))
def input (p : Program) (r : Request) (Q : ℕ) (odd : Bool)
    (q : ℚ) (denominator : ℕ) (xs : List (Bool × ℕ)) :=
  Fin.addCases (m := CompetitorSelectedTable.tapes p) (n := 27) (motive := fun _ => List Bool)
    (CompetitorSelectedTable.extend p xs (CompetitorCountTable.input p r Q odd))
    (CompetitorCountRecordRequest.extra (scalarWidth r Q) q denominator)
noncomputable def first (a : WilliamsAlgorithm) :=
  TapeEmbedding.machine 27 (TapeEmbedding.machine 92 (CompetitorCountTable.machine a))
noncomputable def last (p : Program) := RecoveryFocus.machine (slots p) CompetitorCountRecordRequest.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (first a) (last (producer a))
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) :=
  CompetitorCountTable.budget a r Q+1+CompetitorCountRecordRequest.budget r Q

theorem slots_injective (p : Program) : Function.Injective (slots p) := by
  intro i j
  refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro x
  all_goals refine Fin.addCases (m := 91) (n := 27) ?_ ?_ j <;> intro y
  · intro h
    apply congrArg (fun z : Fin 91 => z.castAdd 27)
    apply CompetitorSelectedTable.slot_injective p
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.val_castAdd] at h'
    exact Fin.ext h'
  · intro h
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h'
    omega
  · intro h
    apply congrArg (fun z : Fin 27 => z.natAdd 91)
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [slots,Fin.addCases_right,Fin.val_natAdd] at h'
    omega

theorem record_run (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) (odd : Bool)
    (f : Fin r.U → Fin r.U → ℕ) (select : Fin r.U → Fin r.U → Bool)
    (q : ℚ) (denominator : ℕ)
    (hQ : Q≤CompetitorSameBucketColdDense.width r)
    (he : odd=true → r.U/2+r.U/2=r.U)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin (r.U*r.U),Int.ModEq ((2 : ℤ)^Q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ actual,run (machine a) (budget a r Q)
      (input (producer a) r Q odd q denominator (CompetitorSelectedCells.cells odd f select))=some actual ∧
      actual.steps≤budget a r Q ∧
      actual.final.tapes (slots (producer a) 117)=CompetitorMonomialStream.recordWord
        (scalarWidth r Q) q (selected (CompetitorSelectedCells.cells odd f select)).sum denominator ∧
      actual.final.heads (slots (producer a) 117)=(CompetitorMonomialStream.recordWord
        (scalarWidth r Q) q (selected (CompetitorSelectedCells.cells odd f select)).sum denominator).length ∧
      actual.final.tapes (slots (producer a) 0)=MatrixScoreBatch.physicalInput r := by
  let p := producer a
  let xs := CompetitorSelectedCells.cells odd f select
  let ext := CompetitorCountRecordRequest.extra (scalarWidth r Q) q denominator
  obtain ⟨base,hbase,bs,bh,bt,bQ,_,_,b0⟩ := CompetitorCountTable.cold_run a r Q odd f hQ he
    (fun i => hf i.divNat i.modNat) hc
  let middle : ExecutionReceipt (CompetitorSelectedTable.tapes p) _ :=
    TapeEmbedding.receipt (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs) base
  let before : ExecutionReceipt (tapes p) _ := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle
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
  have hhead : ∀ i,before.final.heads (slots p i)=0 := by
    intro i
    refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro j
    · simp only [slots,Fin.addCases_left]
      change (TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle).final.heads
        ((CompetitorSelectedTable.slot p j).castAdd 27)=0
      rw [TapeEmbedding.receipt_heads_old]
      rw [hmheads]
      exact CompetitorSelectedTable.slot_heads p _ j
    · simp only [slots,Fin.addCases_right]
      exact TapeEmbedding.receipt_heads_new (fun _ : Fin 27 => 0) ext middle j
  have htape : ∀ i,before.final.tapes (slots p i)=CompetitorCountRecordRequest.input r Q q denominator xs i := by
    intro i
    refine Fin.addCases (m := 91) (n := 27) ?_ ?_ i <;> intro j
    · simp only [slots,CompetitorCountRecordRequest.input,Fin.addCases_left]
      change (TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext middle).final.tapes
        ((CompetitorSelectedTable.slot p j).castAdd 27)=_
      rw [TapeEmbedding.receipt_tapes_old]
      change CompetitorSelectedTable.extend p xs base.final.tapes (CompetitorSelectedTable.slot p j)=
        CompetitorSelectedRequestCount.input r Q xs j
      exact CompetitorSelectedTable.extend_slot p r Q xs base.final.tapes b0 bQ hcword j
    · simp only [slots,CompetitorCountRecordRequest.input,Fin.addCases_right]
      exact TapeEmbedding.receipt_tapes_new (fun _ : Fin 27 => 0) ext middle j
  obtain ⟨child,ch,cs,ct,co,c0⟩ := CompetitorCountRecordRequest.record_run r Q q denominator xs
    (CompetitorSelectedCells.cells_length odd f select) (CompetitorSelectedCells.cells_fit Q odd f select hf)
  obtain ⟨tail,th,_,ts,hh,tt,_⟩ := RecoveryFocus.dock (slots p) (slots_injective p)
    CompetitorCountRecordRequest.machine _ before.final.heads before.final.tapes _ hhead htape child ch
  have htail : runFrom (last p) (CompetitorCountRecordRequest.budget r Q)
      (Composition.restart before.final (last p).start)=some tail := th
  have hj := Composition.run_join (first a) (last p) _ _ _ before tail hfirst htail
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 27 => 0) ext
      (TapeEmbedding.config (fun _ : Fin 92 => 0) (CompetitorSelectedTable.extra xs)
        (initialConfiguration (CompetitorCountTable.machine a) (CompetitorCountTable.input p r Q odd))))=
      initialConfiguration (machine a) (input p r Q odd q denominator xs) := by
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
  have hcost : before.steps+1+tail.steps≤budget a r Q := by
    change base.steps+1+tail.steps≤_
    rw [ts]
    unfold budget
    omega
  exact ⟨Composition.joinedReceipt before tail,hj,hcost,(tt 117).trans ct,(hh 117).trans co,(tt 0).trans c0⟩

end NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
