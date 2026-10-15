import Proof.Supplier.RowTupleCursorEquation
import Proof.Supplier.RowTupleBlank

/-! The exact reusable tuple-store layout: only the coordinate counter,
occurrence stream and count need erasure between adjacent tuples. The
cached last lookup bound remains available and is overwritten by the next
digit read. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorLayout
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F w M k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) (bound : ℕ) (is : List (Fin gs.length)) : Fin 48→List Bool :=
  Fin.addCases (m:=36) (n:=12) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (RowCommonReusable.data gs j p F [] out is) (fun _=>CompareMachine.word (n+1)))
    ![rows.flatten,List.replicate (gs.length+2) false,UnaryTemplate.tape gs.length,
      frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w bound),[false],
      List.replicate (2*w+1) false,List.replicate (RowMaskLookupReusable.capacity gs.length w M) false,
      tuple,CompareMachine.word w,CompareMachine.word k,
      List.replicate (RowTupleCursorReady.capacity gs.length w M k) false]
def heads (pos : ℕ) (out : List Bool) : Fin 48→ℕ := fun i=>
  if i=31 then out.length else if i=44 then pos else
    if i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 then 1 else 0

theorem row_pick (i : Fin 48) : RecoveryFocus.pick rowSlots i=
    Fin.addCases (m:=36) (n:=12) (motive:=fun _=>Option (Fin 36)) (fun j=>some j) (fun _=>none) i := by
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · simpa only [rowSlots,Fin.addCases_left] using RecoveryFocus.pick_slot rowSlots row_injective j
  · fin_cases j <;> decide

theorem fold_static (rows : List (List Bool)) (ds : List ℕ) (x : Data)
    (hp:x.pos=0) (hi:x.index=0) (hc:x.counter=0) (hf:x.flag=false) :
    (RowTupleMaskLoop.fold rows x ds).source=x.source ∧
      (RowTupleMaskLoop.fold rows x ds).pos=0 ∧
      (RowTupleMaskLoop.fold rows x ds).index=0 ∧
      (RowTupleMaskLoop.fold rows x ds).counter=0 ∧
      (RowTupleMaskLoop.fold rows x ds).flag=false := by
  induction ds generalizing x with
  | nil => exact ⟨rfl,hp,hi,hc,hf⟩
  | cons d ds ih =>
    exact ih (RowTupleMaskLoop.advance rows x d) rfl rfl rfl rfl

private theorem tuple_input_tapes (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (pre tail : List Bool) (bound : ℕ) :
    (RowTupleCursorReady.input N w M rows ds pre tail bound).tapes=
      (![rows.flatten,List.replicate (N+2) false,[],CompareMachine.word 0,UnaryTemplate.tape N,
        frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w bound),[false],
        List.replicate (2*w+1) false,List.replicate (RowMaskLookupReusable.capacity N w M) false,
        pre++RowTupleFilterLoop.word w ds++tail,CompareMachine.word w,CompareMachine.word ds.length,
        List.replicate (RowTupleCursorReady.capacity N w M ds.length) false] : Fin 14→List Bool) := by
  funext i
  fin_cases i <;> simp [RowTupleCursorReady.input,RowTupleCursorReady.before,
    RowTupleCursorReady.start,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,RowMaskConsume.bank,
    RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,RowMaskConsume.capacities,
    ZeroPadding.config,ZeroPadding.pad,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
    Fin.addCases,UnaryTemplate.tape,CompareMachine.word,List.replicate_succ]

theorem input_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)≤F) :
    (RowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).tapes=
      data gs 0 p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) out bound [] := by
  have hc : (RowTupleCursorEquation.common gs p F rows ds out).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (RowCommonReusable.data gs 0 p F [] out (indices gs.length rows ds))
        (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (RowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [RowCommonReusable.entry_tapes gs 0 p F [] out _ hF hD]
  funext i
  simp only [RowTupleCursorEquation.input,Composition.restart,RecoveryFocus.config,
    RowTupleBlank.tuple_pick,RowTupleCursorEquation.ambient,TapeEmbedding.config,hc,tuple_input_tapes]
  fin_cases i <;> simp [data,RowCommonReusable.data,Fin.addCases,RowOccurrenceLoop.word,CompareMachine.word]

theorem input_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :
    (RowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).heads=heads pre.length out := by
  funext i
  simp only [RowTupleCursorEquation.input,Composition.restart,RecoveryFocus.config,
    RowTupleBlank.tuple_pick,RowTupleCursorEquation.ambient,TapeEmbedding.config]
  fin_cases i <;> rfl

theorem result_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)≤F) :
    (RowTupleCursorEquation.result gs p F w M rows ds pre tail out bound).tapes=
      data gs (n+1) p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound (indices gs.length rows ds) := by
  have hc : (RowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 3 (n+1) 1 []
      (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (RowCommonReusable.data gs (n+1) p F []
          (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
          (indices gs.length rows ds)) (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (RowCommonClear.entry gs (n+1) p F [] _ (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [RowCommonReusable.entry_tapes gs (n+1) p F [] _ _ hF hD]
  obtain ⟨hs,_,hi,hc0,hf⟩:=fold_static rows ds (RowTupleCursorReady.start rows bound) rfl rfl rfl rfl
  simp only [RowTupleCursorReady.start] at hs hi hc0 hf
  funext i
  simp only [RowTupleCursorEquation.result,RecoveryFocus.config,row_pick,hc]
  fin_cases i
  all_goals first | rfl | skip
  all_goals simp [data,RowTupleCursorEquation.middle,RecoveryFocus.config,RowTupleBlank.tuple_pick,
    RowTupleCursorReady.output,RowTupleCursorReady.after,RowTupleMaskLoop.cfg,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,
    RowMaskConsume.bank,ZeroPadding.config,RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,
    RowMaskConsume.capacities,ZeroPadding.pad,Fin.addCases,hs,hi,hc0,hf,
    RowTupleCursorReady.start,UnaryTemplate.tape,List.replicate_succ]

theorem result_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :
    (RowTupleCursorEquation.result gs p F w M rows ds pre tail out bound).heads=
      heads (pre.length+2*w*ds.length)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds))) := by
  have hp:=(fold_static rows ds (RowTupleCursorReady.start rows bound) rfl rfl rfl rfl).2.1
  funext i
  simp only [RowTupleCursorEquation.result,RecoveryFocus.config,row_pick]
  fin_cases i
  all_goals first | rfl | skip
  all_goals simp [heads,RowTupleCursorEquation.middle,RecoveryFocus.config,RowTupleBlank.tuple_pick,
    RowTupleCursorReady.middleHeads,RowTupleCursorReady.after,RowTupleCursorReady.selected,
    RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,
    RowMaskLookupReusable.cfg,RowMaskPositionParts.heads,Fin.addCases,hp]

end NearCubicWires.RepairOrdinary.RowTupleCursorLayout
