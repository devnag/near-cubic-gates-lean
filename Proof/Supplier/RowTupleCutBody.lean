import Proof.Supplier.RowTupleCutAppend

/-! The actual tuple consumer emits the complete signed cut: all equation
coordinates, its threshold, then the cached binLift coefficient. The cache
is retained at head zero while the row append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 RowTupleFramedBody.machine
noncomputable def machine := Composition.machine first RowTupleCutAppend.machine
noncomputable def entry {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient))
    (RowTupleList.cfg q gs p F w M k rows tuple pos out bound)
def word {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (coefficient : ℤ) :=
  RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds))++
    frame (MatrixScoreBatch.signMagnitude p coefficient)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := RowTupleFramedBody.budget gs F w M rows ds+4*p+9

theorem fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (entry q gs p F w M k rows tuple pos out bound coefficient).heads 48=0 ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).heads 31=out.length ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).heads 34=0 ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 48=frame (MatrixScoreBatch.signMagnitude p coefficient) ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 31=out ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 34=List.replicate (F+1) false := by
  simp [entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,
    RowTupleCursorBody.entry,RowTupleCursorBody.padding,RowTupleCursorLayout.data,RowTupleCursorLayout.heads,
    RowCommonReusable.data,Fin.addCases]

private theorem output_heads {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out next : List Bool) (bound : ℕ) (coefficient : ℤ) :
    Function.update (entry q gs p F w M k rows tuple pos out bound coefficient).heads 31 next.length=
      (entry q gs p F w M k rows tuple pos next bound coefficient).heads := by
  funext i
  fin_cases i <;> simp [entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,
    RowTupleCursorBody.entry,RowTupleCursorLayout.heads,Fin.addCases]
private theorem output_tapes {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out next : List Bool) (bound : ℕ) (coefficient : ℤ) :
    Function.update (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 31 next=
      (entry q gs p F w M k rows tuple pos next bound coefficient).tapes := by
  funext i
  fin_cases i <;> simp [entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,
    RowTupleCursorBody.entry,RowTupleCursorBody.padding,RowTupleCursorLayout.data,RowCommonReusable.data,Fin.addCases]

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) (coefficient : ℤ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs p F w M rows ds)
      (entry machine.start gs p F w M ds.length rows (pre++RowTupleFramedBody.word w ds++tail) pre.length out bound coefficient)=some r ∧
      r.final.heads=(entry machine.start gs p F w M ds.length rows (pre++RowTupleFramedBody.word w ds++tail)
        (pre.length+(RowTupleFramedBody.word w ds).length) (out++word gs p rows ds coefficient)
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient).heads ∧
      r.final.tapes=(entry machine.start gs p F w M ds.length rows (pre++RowTupleFramedBody.word w ds++tail)
        (pre.length+(RowTupleFramedBody.word w ds).length) (out++word gs p rows ds coefficient)
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient).tapes ∧
      r.steps≤budget gs p F w M rows ds := by
  obtain ⟨base,hbase,bh,bt,_⟩:=RowTupleFramedBody.tuple_run gs p F Q w M rows ds pre tail out bound hl hd hb hM hQ hp hF
  let a:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient)) base
  have ha:=TapeEmbedding.run_embed RowTupleFramedBody.machine (fun _ : Fin 1=>0)
    (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient)) _ _ base hbase
  let next:=entry first.start gs p F w M ds.length rows (pre++RowTupleFramedBody.word w ds++tail)
    (pre.length+(RowTupleFramedBody.word w ds).length)
    (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient
  have ah : a.final.heads=next.heads := by
    change Fin.addCases (m:=48) (n:=1) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
    rw [bh]
    rfl
  have atapes : a.final.tapes=next.tapes := by
    change Fin.addCases (m:=48) (n:=1) (motive:=fun _=>List Bool) base.final.tapes
      (fun _=>frame (MatrixScoreBatch.signMagnitude p coefficient))=_
    rw [bt]
    rfl
  have cap : 2*(MatrixScoreBatch.signMagnitude p coefficient).length+1≤F+1 := by
    have h:=RowCommonBounds.padding_fits gs (gs.length*Q) p
    simp only [MatrixScoreBatch.signMagnitude,List.length_cons,SignedSortKey.binary_length]
    omega
  have hf:=fields first.start gs p F w M ds.length rows (pre++RowTupleFramedBody.word w ds++tail)
    (pre.length+(RowTupleFramedBody.word w ds).length)
    (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient
  obtain ⟨b,hbRun,bh',bt',_⟩:=RowTupleCutAppend.append_run (MatrixScoreBatch.signMagnitude p coefficient)
    (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (F+1) a.final.heads a.final.tapes cap (by rw [ah]; exact hf.1) (by rw [ah]; exact hf.2.1)
    (by rw [ah]; exact hf.2.2.1) (by rw [atapes]; exact hf.2.2.2.1)
    (by rw [atapes]; exact hf.2.2.2.2.1) (by rw [atapes]; exact hf.2.2.2.2.2)
  change runFrom RowTupleCutAppend.machine _ (Composition.restart a.final RowTupleCutAppend.machine.start)=some b at hbRun
  have whole:=Composition.run_join first RowTupleCutAppend.machine _ _ _ a b ha hbRun
  have timeEq : RowTupleFramedBody.budget gs F w M rows ds+1+
      (4*(MatrixScoreBatch.signMagnitude p coefficient).length+4)=budget gs p F w M rows ds := by
    simp only [MatrixScoreBatch.signMagnitude,List.length_cons,SignedSortKey.binary_length,budget]
    omega
  rw [timeEq] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.heads=_
    rw [bh',ah]
    simpa only [next,word,entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,List.append_assoc]
      using output_heads first.start gs p F w M ds.length rows _ _ _ _ _ coefficient
  · change b.final.tapes=_
    rw [bt',atapes]
    simpa only [next,word,entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,List.append_assoc]
      using output_tapes first.start gs p F w M ds.length rows _ _ _ _ _ coefficient

end NearCubicWires.RepairOrdinary.RowTupleCutBody
