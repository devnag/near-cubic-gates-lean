import Proof.Supplier.RowTupleCutBody

/-! The actual selected tuple stream emits every complete signed cut,
reusing one cached coefficient and retaining the whole-row append cursor. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding RowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine RowTupleCutBody.machine 44
noncomputable def cfg {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :=
  RowTupleCutBody.entry q gs p F w M k rows tuple pos out bound coefficient
def stream (w : ℕ) (xs : List (List ℕ)) := xs.flatMap (RowTupleFramedBody.word w)
def output {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) (coefficient : ℤ) := xs.flatMap fun ds=>
  RowTupleCutBody.word gs p rows ds coefficient
def finalBound (rows : List (List Bool)) : List (List ℕ)→ℕ→ℕ
  | [],b=>b
  | ds::xs,b=>finalBound rows xs (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows b) ds).bound
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) :=
  (xs.map fun ds=>RowTupleCutBody.budget gs p F w M rows ds+2).sum+1

theorem fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (cfg q gs p F w M k rows tuple pos out bound coefficient).tapes 44=tuple ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).heads 44=pos ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).tapes 31=out ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).heads 31=out.length := by
  simp [cfg,RowTupleCutBody.entry,TapeEmbedding.config,Composition.restart,RowTupleList.cfg,RowTupleFramedBody.entry,RowTupleCursorBody.entry,
    RowTupleCursorBody.padding,RowTupleCursorLayout.heads,RowTupleCursorLayout.data,
    RowCommonReusable.data,Fin.addCases]

private theorem read_end (pre : List Bool) : readTapeBit pre pre.length=false := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [readTapeBit,List.getD]

private theorem read_frame (pre tail : List Bool) (w : ℕ) (ds : List ℕ) :
    readTapeBit (pre++RowTupleFramedBody.word w ds++tail) pre.length=true := by
  simpa only [RowTupleFramedBody.word,SignedSortKey.binary,frame,List.append_assoc,List.cons_append] using
    Streaming.read_append pre
      ((RowTupleDigits.encode w ds%2==1)::frame (SignedSortKey.binary (w*ds.length) (RowTupleDigits.encode w ds/2))++tail) true

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control=p.start)
    (hread : c.scanned tape=true) (hbody : runFrom p fuel c=some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) body.final)=some tail) :
    ∃ r, runFrom (StreamController.machine p tape) (fuel+tailFuel+2)
      (controlConfig (fun _ => test s) c)=some r ∧ r.final=tail.final := by
  obtain ⟨bodyPrefix,halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final,tail.steps+1,max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code body.final)=some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle,hm,hmf,_,_⟩ := bodyPrefix.followedBy returned hr
  have hrestart : Composition.restart c p.start=c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) :=
    ⟨middle.final,middle.steps+1,max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((body.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => test s) c)=some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle
      (StreamController.test_halted p tape) he hm
  have hs := runFrom_steps_le p fuel c body hbody
  have hmore := runFrom_moreFuel (StreamController.machine p tape) _ (fuel-body.steps) _ result hrun
  have ht : ((body.steps+(tailFuel+1))+1)+(fuel-body.steps)=fuel+tailFuel+2 := by omega
  rw [ht] at hmore
  exact ⟨result,hmore,hmf⟩

theorem list_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M k : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) (pre out : List Bool) (bound : ℕ) (coefficient : ℤ)
    (hl : ∀ row∈rows,row.length=gs.length)
    (hk : ∀ ds∈xs,ds.length=k) (hd : ∀ ds∈xs,∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : k≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs p F w M rows xs)
      (cfg machine.start gs p F w M k rows (pre++stream w xs) pre.length out bound coefficient)=some r ∧
      r.final.heads=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs coefficient) (finalBound rows xs bound) coefficient).heads ∧
      r.final.tapes=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs coefficient) (finalBound rows xs bound) coefficient).tapes ∧
      r.steps≤budget gs p F w M rows xs := by
  induction xs generalizing pre out bound with
  | nil =>
    let c:=RowTupleCutBody.entry RowTupleCutBody.machine.start gs p F w M k rows pre pre.length out bound coefficient
    have hr : c.scanned 44=false := by
      change readTapeBit (c.tapes 44) (c.heads 44)=false
      obtain ⟨ht,hh,_,_⟩:=fields RowTupleCutBody.machine.start gs p F w M k rows pre pre.length out bound coefficient
      change c.tapes 44=pre at ht
      change c.heads 44=pre.length at hh
      rw [ht,hh]
      exact read_end pre
    obtain ⟨r,hrun,rf,rs⟩:=(Timed.single (StreamController.test_halted RowTupleCutBody.machine 44)
      (StreamController.stop_step RowTupleCutBody.machine 44 c hr)).run
      (StreamController.stop_halted RowTupleCutBody.machine 44)
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [budget,List.map_nil,List.sum_nil,stream,List.flatMap_nil,List.append_nil,
        cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,
        machine,StreamController.machine,controlConfig,Composition.restart,c,Nat.zero_add] using hrun
    · rw [rf]
      simp only [cfg,RowTupleCutBody.entry,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,TapeEmbedding.config,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · rw [rf]
      simp only [cfg,RowTupleCutBody.entry,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,TapeEmbedding.config,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · simpa [budget] using rs.le
  | cons ds xs ih =>
    have hk0:=hk ds (by simp)
    have hd0:=hd ds (by simp)
    obtain ⟨a,ha,ah,atapes,_⟩:=RowTupleCutBody.tuple_run gs p F Q w M rows ds pre
      (stream w xs) out bound coefficient hl hd0 hb hM (hk0.trans_le hQ) hp hF
    rw [hk0] at ha ah atapes
    let nextOut:=out++RowTupleCutBody.word gs p rows ds coefficient
    let nextBound:=(RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound
    obtain ⟨b,hbRun,bh,bt,_⟩:=ih (pre++RowTupleFramedBody.word w ds) nextOut nextBound
      (fun d hd'=>hk d (List.mem_cons_of_mem ds hd'))
      (fun d hd'=>hd d (List.mem_cons_of_mem ds hd'))
    have hnext : (controlConfig (fun _=>test _) a.final)=
        cfg machine.start gs p F w M k rows ((pre++RowTupleFramedBody.word w ds)++stream w xs)
          (pre++RowTupleFramedBody.word w ds).length nextOut nextBound coefficient := by
      apply configuration_ext
      · rfl
      · change a.final.heads=_
        rw [ah]
        simp only [cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,List.length_append,nextOut,nextBound]
      · change a.final.tapes=_
        rw [atapes]
        rfl
    rw [←hnext] at hbRun
    have hr : (RowTupleCutBody.entry RowTupleCutBody.machine.start gs p F w M k rows
        (pre++RowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).scanned 44=true := by
      have hf:=fields RowTupleCutBody.machine.start gs p F w M k rows
        (pre++RowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient
      change readTapeBit
        ((cfg RowTupleCutBody.machine.start gs p F w M k rows
          (pre++RowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).tapes 44)
        ((cfg RowTupleCutBody.machine.start gs p F w M k rows
          (pre++RowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).heads 44)=true
      rw [hf.1,hf.2.1]
      exact read_frame pre (stream w xs) w ds
    obtain ⟨r,hRun,rf⟩:=round_run RowTupleCutBody.machine 44 _ _ _ a b rfl hr ha hbRun
    have htime : RowTupleCutBody.budget gs p F w M rows ds+budget gs p F w M rows xs+2=
        budget gs p F w M rows (ds::xs) := by simp only [budget,List.map_cons,List.sum_cons]; omega
    rw [htime] at hRun
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [machine,StreamController.machine,cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun
    · rw [rf,bh]
      simp only [cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · rw [rf,bt]
      simp only [cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · exact runFrom_steps_le machine _ _ _ (by
        simpa only [machine,StreamController.machine,cfg,RowTupleCutBody.entry,TapeEmbedding.config,RowTupleList.cfg,RowTupleFramedBody.entry,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun)

end NearCubicWires.RepairOrdinary.RowTupleCutList
