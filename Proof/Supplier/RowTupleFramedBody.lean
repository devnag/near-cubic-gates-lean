import Proof.Supplier.RowTupleFrame

/-! One actual enumerated frame executes through the complete reusable
equation body and its paid three-cell trailer. The next cursor is exactly
the end of that frame, including the zero-degree case. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFramedBody
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (w : ℕ) (ds : List ℕ) := frame (SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds))
theorem word_length (w : ℕ) (ds : List ℕ) : (word w ds).length=2*w*ds.length+3 := by
  simp [word]
  ring
noncomputable def machine := Composition.machine RowTupleCursorBody.machine RowTupleFrame.skip
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :=
  Composition.restart (RowTupleCursorBody.entry gs p F w M k rows tuple pos out bound) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := RowTupleCursorBody.budget gs F w M rows ds+4

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds)
      (entry gs p F w M ds.length rows (pre++word w ds++tail) pre.length out bound)=some r ∧
      r.final.heads=(entry gs p F w M ds.length rows (pre++word w ds++tail)
        (pre.length+(word w ds).length)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).heads ∧
      r.final.tapes=(entry gs p F w M ds.length rows (pre++word w ds++tail)
        (pre.length+(word w ds).length)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hword : word w ds=RowTupleFilterLoop.word w ds++RowTupleFrame.trailer :=
    RowTupleFrame.encoded_word w ds (fun d hd'=>(hd d hd').trans hb)
  have htape : pre++word w ds++tail=pre++RowTupleFilterLoop.word w ds++(RowTupleFrame.trailer++tail) := by
    rw [hword]
    simp only [List.append_assoc]
  obtain ⟨a,ha,ah,atapes,_⟩:=RowTupleCursorBody.tuple_run gs p F Q w M rows ds pre
    (RowTupleFrame.trailer++tail) out bound hl hd hb hM hQ hp hF
  rw [←htape] at ha ah atapes
  obtain ⟨b,hbRun,bh,bt,_⟩:=RowTupleFrame.skip_run a.final.heads a.final.tapes
  change runFrom RowTupleFrame.skip 3 (Composition.restart a.final RowTupleFrame.skip.start)=some b at hbRun
  have whole:=Composition.run_join RowTupleCursorBody.machine RowTupleFrame.skip _ _ _ a b ha hbRun
  have budgetEq : RowTupleCursorBody.budget gs F w M rows ds+1+3=budget gs F w M rows ds := by unfold budget; omega
  rw [budgetEq] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,bt.trans atapes,runFrom_steps_le machine _ _ _ whole⟩
  change b.final.heads=_
  rw [bh,ah]
  funext i
  by_cases hi:i=44
  · subst i
    simp [entry,Composition.restart,RowTupleCursorBody.entry,RowTupleCursorLayout.heads,word_length]
    omega
  · simp [entry,Composition.restart,RowTupleCursorBody.entry,RowTupleCursorLayout.heads,hi]

end NearCubicWires.RepairOrdinary.RowTupleFramedBody
