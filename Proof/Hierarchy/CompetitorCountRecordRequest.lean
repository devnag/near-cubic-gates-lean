import Proof.Hierarchy.CompetitorCountRecordRequestInput
import Proof.Hierarchy.CompetitorCountRecordAppendBounds

/-! One fixed program executes the original Request's selected-count SUM
and appends the exact six-field record. The request derives every SUM driver,
scalar width and record workspace; only the actual mask/count table and
coefficient/normalization fields remain row-producer inputs. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open MatrixScoreBatch CompetitorSelectedCount CompetitorCountMask
open CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 29 → Fin 118 :=
  ![76,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,86,117]
def extra (b : ℕ) (q : ℚ) (denominator : ℕ) (i : Fin 27) : List Bool :=
  match i.val with
    | 22 => frame (binary (width b) (positive q))
    | 23 => frame (binary (width b) (negative q))
    | 24 => frame (binary (width b) q.den)
    | 25 => frame (binary b denominator)
    | _ => []
def input (r : Request) (Q : ℕ) (q : ℚ) (denominator : ℕ) (xs : List (Bool × ℕ)) : Fin 118 → List Bool :=
  Fin.addCases (m := 91) (n := 27) (motive := fun _ => List Bool)
    (CompetitorSelectedRequestCount.input r Q xs) (extra (scalarWidth r Q) q denominator)
noncomputable def first := TapeEmbedding.machine 27 CompetitorSelectedRequestCount.machine
noncomputable def last := RecoveryFocus.machine slots CompetitorCountRecordAppend.machine
noncomputable def machine := Composition.machine first last
def budget (r : Request) (Q : ℕ) := CompetitorSelectedRequestCount.budget r Q+1+
  CompetitorCountRecordAppend.budget (scalarWidth r Q)

theorem append_dock {s : ℕ} (base : ExecutionReceipt 91 s) (b : ℕ) (q : ℚ) (count denominator : ℕ)
    (source : List Bool) (b86 : base.final.tapes 86=frame (binary b count))
    (b76 : base.final.tapes 76=List.replicate b true) (bh86 : base.final.heads 86=0)
    (bh76 : base.final.heads 76=0) (b0 : base.final.tapes 0=source) :
    ∃ tail,runFrom last (CompetitorCountRecordAppend.budget b)
      (Composition.restart (TapeEmbedding.receipt (fun _ : Fin 27 => 0) (extra b q denominator) base).final last.start)=some tail ∧
      tail.steps≤CompetitorCountRecordAppend.budget b ∧
      tail.final.tapes 117=CompetitorMonomialStream.recordWord b q count denominator ∧
      tail.final.heads 117=(CompetitorMonomialStream.recordWord b q count denominator).length ∧
      tail.final.tapes 0=source := by
  let ext := extra b q denominator
  let before := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext base
  have hnew (j : Fin 27) : before.final.heads (j.natAdd 91)=0 :=
    TapeEmbedding.receipt_heads_new _ _ base j
  have tnew (j : Fin 27) : before.final.tapes (j.natAdd 91)=ext j :=
    TapeEmbedding.receipt_tapes_new _ _ base j
  obtain ⟨app,ha,as,appTape,ah,_,_⟩ := CompetitorCountRecordAppend.record_run b q count denominator
  have ht : ∀ j,before.final.tapes (slots j)=
      CompetitorCountRecordAppend.input b q count denominator j := by
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
  have hh : ∀ j,before.final.heads (slots j)=0 := by
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
  obtain ⟨tail,htail,_,ts,th,tt,keep⟩ := RecoveryFocus.dock slots (by decide)
    CompetitorCountRecordAppend.machine _ before.final.heads before.final.tapes _ hh ht app ha
  have ht' : runFrom last (CompetitorCountRecordAppend.budget b)
      (Composition.restart before.final last.start)=some tail := htail
  exact ⟨tail,ht',ts.trans_le as,(tt 28).trans appTape,
    (th 28).trans (by rw [ah,Function.update_self]),((keep 0 (by decide)).2).trans b0⟩

theorem program_run {s : ℕ} (p : Machine 91 s) (fuel : ℕ) (data : Fin 91 → List Bool)
    (base : ExecutionReceipt 91 s) (hr : run p fuel data=some base) (bs : base.steps≤fuel)
    (b : ℕ) (q : ℚ) (count denominator : ℕ) (source : List Bool)
    (b86 : base.final.tapes 86=frame (binary b count))
    (b76 : base.final.tapes 76=List.replicate b true) (bh86 : base.final.heads 86=0)
    (bh76 : base.final.heads 76=0) (b0 : base.final.tapes 0=source) : ∃ actual,
    run (Composition.machine (TapeEmbedding.machine 27 p) last)
      (fuel+1+CompetitorCountRecordAppend.budget b)
      (Fin.addCases (m := 91) (n := 27) (motive := fun _ => List Bool) data (extra b q denominator))=some actual ∧
      actual.steps≤fuel+1+CompetitorCountRecordAppend.budget b ∧
      actual.final.tapes 117=CompetitorMonomialStream.recordWord b q count denominator ∧
      actual.final.heads 117=(CompetitorMonomialStream.recordWord b q count denominator).length ∧
      actual.final.tapes 0=source := by
  let ext := extra b q denominator
  have hfirst := TapeEmbedding.run_embed p (fun _ : Fin 27 => 0) ext _ _ base hr
  let before := TapeEmbedding.receipt (fun _ : Fin 27 => 0) ext base
  obtain ⟨tail,htail,ts,tt,th,t0⟩ := append_dock base b q count denominator source b86 b76 bh86 bh76 b0
  have hall := Composition.run_join (TapeEmbedding.machine 27 p) last _ _ _ before tail hfirst htail
  have hcost : before.steps+1+tail.steps≤fuel+1+CompetitorCountRecordAppend.budget b := by
    change base.steps+1+tail.steps≤fuel+1+CompetitorCountRecordAppend.budget b
    omega
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 27 => 0) ext
      (initialConfiguration p data))=initialConfiguration
      (Composition.machine (TapeEmbedding.machine 27 p) last)
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

theorem record_run (r : Request) (Q : ℕ) (q : ℚ) (denominator : ℕ) (xs : List (Bool × ℕ))
    (hn : xs.length≤r.U*r.U) (hx : ∀ x∈selected xs,x<2^Q) : ∃ actual,
    run machine (budget r Q) (input r Q q denominator xs)=some actual ∧ actual.steps≤budget r Q ∧
      actual.final.tapes 117=CompetitorMonomialStream.recordWord (scalarWidth r Q) q (selected xs).sum denominator ∧
      actual.final.heads 117=(CompetitorMonomialStream.recordWord (scalarWidth r Q) q (selected xs).sum denominator).length ∧
      actual.final.tapes 0=MatrixScoreBatch.physicalInput r := by
  obtain ⟨base,hbase,bs,b86,b76,bh86,bh76,b0⟩ := CompetitorCountRecordRequestInput.selected_run r Q xs hn hx
  exact program_run CompetitorSelectedRequestCount.machine (CompetitorSelectedRequestCount.budget r Q)
    (CompetitorSelectedRequestCount.input r Q xs) base hbase bs (scalarWidth r Q) q
    (selected xs).sum denominator (MatrixScoreBatch.physicalInput r) b86 b76 bh86 bh76 b0

end NearCubicWires.RepairOrdinary.CompetitorCountRecordRequest
