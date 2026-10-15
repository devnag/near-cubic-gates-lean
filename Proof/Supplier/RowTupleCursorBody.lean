import Proof.Supplier.RowTupleCursorLayout
import Proof.Supplier.RowTupleCursorErase
import Proof.Supplier.RowTupleResetBounds

/-! A reusable whole-tuple body: the actual selected digits produce the
common-width equation, then paid erasure restores all per-tuple fields.
The stream cursor advances and the equation append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (F : ℕ) : Fin 48→ℕ := fun i=>if i=15 ∨ i=23 ∨ i=24 then F else 0
noncomputable def machine := Composition.machine RowTupleCursorEquation.machine RowTupleCursorErase.machine
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :=
  (⟨machine.start,RowTupleCursorLayout.heads pos out,
    fun i=>ZeroPadding.pad (padding F i) (RowTupleCursorLayout.data gs 0 p F w M k rows tuple out bound [] i)⟩ : Configuration 48 _)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := RowTupleCursorEquation.budget gs F w M rows ds+2*F+9

theorem erase_pick (i : Fin 48) : RecoveryFocus.pick RowTupleCursorErase.eraseSlots i=
    if i=15 then some 0 else if i=23 then some 1 else if i=24 then some 2
    else if i=33 then some 3 else if i=34 then some 4 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 0
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 1
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 2
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 3
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 4
    | decide

theorem cleared_data {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F w M k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) (bound : ℕ) (is : List (Fin gs.length)) (hF:2≤F) :
    RowTupleCursorErase.cleared F
      (fun i=>ZeroPadding.pad (padding F i) (RowTupleCursorLayout.data gs j p F w M k rows tuple out bound is i))=
      fun i=>ZeroPadding.pad (padding F i) (RowTupleCursorLayout.data gs 0 p F w M k rows tuple out bound [] i) := by
  funext i
  simp only [RowTupleCursorErase.cleared,install,erase_pick]
  fin_cases i <;> simp [padding,RowTupleCursorErase.eraseInput,RowTupleCursorLayout.data,
    RowCommonReusable.data,Fin.addCases,ZeroPadding.pad,UnaryTemplate.tape,CompareMachine.word,
    RowOccurrenceLoop.word]
  all_goals simp only [←List.replicate_succ]
  all_goals first | rfl | (congr 1; omega)

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds)
      (entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) pre.length out bound)=some r ∧
      r.final.heads=(entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (pre.length+2*w*ds.length)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).heads ∧
      r.final.tapes=(entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (pre.length+2*w*ds.length)
        (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap:=RowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hpos : 2≤F := by have := RowCommonBounds.padding_fits gs (gs.length*Q) p; omega
  have hinner:=(RowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF
  obtain ⟨base,hbase,bh,bt,bs⟩:=RowTupleCursorEquation.equation_run gs p F Q w M rows ds pre tail out bound hl hd hb hM hQ hp hF
  obtain ⟨a,ha,af,as,_⟩:=ZeroPadding.run_config RowTupleCursorEquation.machine (padding F) _ _ base hbase
  let output:=out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds))
  let lastBound:=(RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound
  have ah : a.final.heads=RowTupleCursorLayout.heads (pre.length+2*w*ds.length) output := by
    rw [af]
    change base.final.heads=_
    rw [bh,RowTupleCursorLayout.result_heads]
  have atapes : a.final.tapes=fun i=>ZeroPadding.pad (padding F i)
      (RowTupleCursorLayout.data gs (n+1) p F w M ds.length rows
        (pre++RowTupleFilterLoop.word w ds++tail) output lastBound (indices gs.length rows ds) i) := by
    rw [af]
    change (fun i=>ZeroPadding.pad (padding F i) (base.final.tapes i))=_
    rw [bt,RowTupleCursorLayout.result_tapes gs p F w M rows ds pre tail out bound (by omega) hinner]
  have fits:=RowTupleResetBounds.fields_fit gs p F (indices gs.length rows ds) hcap
  obtain ⟨b,hbRun,bh',bt',_⟩:=RowTupleCursorErase.clear_run F a.final.heads a.final.tapes
    (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl)
    (by
      intro i
      rw [atapes]
      fin_cases i
      · simpa [RowTupleCursorErase.workSlots,padding,RowTupleCursorLayout.data,
          RowCommonReusable.data,Fin.addCases,UnaryTemplate.tape] using (show n+1+1<F by omega)
      · simpa [RowTupleCursorErase.workSlots,padding,RowTupleCursorLayout.data,
          RowCommonReusable.data,Fin.addCases] using fits.2.1
      · simpa [RowTupleCursorErase.workSlots,padding,RowTupleCursorLayout.data,
          RowCommonReusable.data,Fin.addCases,CompareMachine.word] using fits.2.2)
    (by rw [atapes]; simp [padding,RowTupleCursorLayout.data,RowCommonReusable.data,Fin.addCases])
    (by rw [atapes]; simp [padding,RowTupleCursorLayout.data,RowCommonReusable.data,Fin.addCases])
  change runFrom RowTupleCursorErase.machine _ (Composition.restart a.final RowTupleCursorErase.machine.start)=some b at hbRun
  have whole:=Composition.run_join RowTupleCursorEquation.machine RowTupleCursorErase.machine _ _ _ a b ha hbRun
  have inputEq : Composition.leftConfig 8
      (ZeroPadding.config (padding F) (RowTupleCursorEquation.input gs p F w M rows ds pre tail out bound))=
      entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) pre.length out bound := by
    apply configuration_ext
    · rfl
    · exact RowTupleCursorLayout.input_heads gs p F w M rows ds pre tail out bound
    · change (fun i=>ZeroPadding.pad (padding F i) ((RowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).tapes i))=_
      rw [RowTupleCursorLayout.input_tapes gs p F w M rows ds pre tail out bound (by omega) hinner]
      rfl
  rw [inputEq,show RowTupleCursorEquation.budget gs F w M rows ds+1+(2*F+8)=budget gs F w M rows ds by unfold budget; omega] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh'.trans ah,?_,runFrom_steps_le machine _ _ _ whole⟩
  change b.final.tapes=_
  rw [bt',atapes,cleared_data gs (n+1) p F w M ds.length rows _ output lastBound _ hpos]
  rfl

end NearCubicWires.RepairOrdinary.RowTupleCursorBody
