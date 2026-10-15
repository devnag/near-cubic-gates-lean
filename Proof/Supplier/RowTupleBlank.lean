import Proof.Supplier.RowTupleFixedCapacity

/-! The whole tuple-to-equation machine starts with blank scratch and
recording tapes. Zero-padding transport removes the earlier supplied false
allocations without changing the machine, actual data, or execution time. -/
namespace NearCubicWires.RepairOrdinary.RowTupleBlank
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def keep (i : Fin 48) : Bool := decide (i=0 ∨ i=9 ∨ i=13 ∨ i=18 ∨ i=21 ∨ i=29 ∨
  i=31 ∨ i=33 ∨ i=35 ∨ i=36 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=44 ∨ i=45 ∨ i=46)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  let c:=RowTupleFixedCapacity.input gs p F w M rows ds tail out
  {c with tapes:=fun i=>if keep i then c.tapes i else []}
noncomputable def padding {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) : Fin 48→ℕ :=
  fun i=>if keep i then 0 else (RowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i |>.length

theorem tuple_pick (i : Fin 48) : RecoveryFocus.pick tupleSlots i=
    (if i=36 then some 0 else if i=37 then some 1 else if i=23 then some 2 else if i=24 then some 3
    else if i=38 then some 4 else if i=39 then some 5 else if i=40 then some 6 else if i=41 then some 7
    else if i=42 then some 8 else if i=43 then some 9 else if i=44 then some 10 else if i=45 then some 11
    else if i=46 then some 12 else if i=47 then some 13 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 0
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 1
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 2
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 3
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 4
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 5
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 6
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 7
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 8
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 9
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 10
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 11
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 12
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 13
    | decide

theorem zero_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)≤F)
    (i : Fin 48) (hi : keep i=false) :
    (RowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i=
      List.replicate ((RowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i).length false := by
  have hc : (RowTupleFixedCapacity.common gs p F rows ds out).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (RowCommonReusable.data gs 0 p F [] out (indices gs.length rows ds))
        (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (RowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [RowCommonReusable.entry_tapes gs 0 p F [] out (indices gs.length rows ds) hF hD]
  simp only [RowTupleFixedCapacity.input,Composition.restart,RecoveryFocus.config,
    tuple_pick,RowTupleFixedCapacity.ambient,TapeEmbedding.config,hc]
  fin_cases i <;> simp only [keep,decide_eq_false_iff_not] at hi
  all_goals first
    | (exact False.elim (hi (by decide)))
    | (simp [RowCommonReusable.data,RowTupleMaskReady.input,RowTupleMaskReady.before,
        RowTupleMaskReady.start,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,RowMaskConsume.bank,
        RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,RowMaskConsume.capacities,
        ZeroPadding.config,ZeroPadding.pad,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
        Fin.addCases,UnaryTemplate.tape,CompareMachine.word])
  all_goals simp only [List.replicate_succ]

theorem padded_input {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)≤F) :
    ZeroPadding.config (padding gs p F w M rows ds tail out) (input gs p F w M rows ds tail out)=
      RowTupleFixedCapacity.input gs p F w M rows ds tail out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    cases hi:keep i
    · simpa [ZeroPadding.config,padding,input,hi,ZeroPadding.pad] using
        (zero_tapes gs p F w M rows ds tail out hF hD i hi).symm
    · simp [ZeroPadding.config,padding,input,hi,ZeroPadding.pad_zero]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (RowTupleFixedCapacity.budget gs F w M rows ds)
      (input gs p F w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤RowTupleFixedCapacity.budget gs F w M rows ds := by
  obtain ⟨base,hbRun,bt,bh,bs⟩:=RowTupleFixedCapacity.equation_run gs p F Q w M rows ds tail out hl hd hb hM hQ hp hF
  have hpos : 1≤F := by have := RowCommonBounds.padding_fits gs (gs.length*Q) p; omega
  have hinner := (RowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF
  rw [←padded_input gs p F w M rows ds tail out hpos hinner] at hbRun
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_unpad machine (padding gs p F w M rows ds tail out) _ _ base hbRun
  have ht:=congrArg (fun c=>c.tapes (31 : Fin 48)) rf
  have hh:=congrArg (fun c=>c.heads (31 : Fin 48)) rf
  refine ⟨r,hr,?_,hh.trans bh,rs.le.trans bs⟩
  simpa [ZeroPadding.config,padding,keep,ZeroPadding.pad_zero] using ht.trans bt

end NearCubicWires.RepairOrdinary.RowTupleBlank
