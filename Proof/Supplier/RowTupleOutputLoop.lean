import Proof.Supplier.RowTupleOutputMeaning

/-! Exhaust the fixed-width binary cursor, emitting each selected positional
candidate exactly once. The exponential candidate count has no unary tape. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputLoop
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleOutputParts
open RowTupleOutputBody RowTupleOutputMeaning SignedSortKey
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine RowTupleOutputBody.machine 15
def budget (w k count : ℕ) := count*(RowTupleOutputBody.budget w k+2)+1

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

theorem loop_run (w k M n count : ℕ) (x : Data) (out : List Bool)
    (hremaining : n+count=2^(w*k)) (hM : 0<M) (hMw : M≤2^w)
    (hx : x.source=frame (binary (w*k+1) n)) (hb : x.bound=M-1) (hp : x.previous<2^w) :
    ∃ r,runFrom machine (budget w k count)
      (cfg machine.start w k x (decide (n<2^(w*k))) out)=some r ∧
      r.final.heads=(cfg machine.start w k (iterated w k n count x) false
        (out++output w k M n count)).heads ∧
      r.final.tapes=(cfg machine.start w k (iterated w k n count x) false
        (out++output w k M n count)).tapes ∧ r.steps≤budget w k count := by
  induction count generalizing n x out with
  | zero =>
    have hflag : decide (n<2^(w*k))=false := by simp [show n=2^(w*k) by omega]
    rw [hflag]
    let c := cfg RowTupleOutputBody.machine.start w k x false out
    have hread : c.scanned 15=false := by rfl
    have ht := Timed.single (StreamController.test_halted RowTupleOutputBody.machine 15)
      (StreamController.stop_step RowTupleOutputBody.machine 15 c hread)
    obtain ⟨r,hr,rf,rs⟩ := ht.run (StreamController.stop_halted RowTupleOutputBody.machine 15)
    have hi : controlConfig (fun _=>test (Fintype.card (RecoveryCalls.Control sizes))) c=
        cfg machine.start w k x false out := by apply configuration_ext <;> rfl
    rw [hi] at hr
    refine ⟨r,by simpa only [machine,budget,Nat.zero_mul,Nat.zero_add] using hr,?_,?_,by simpa [budget] using rs.le⟩
    · rw [rf]; simp [iterated,output,c,controlConfig]; rfl
    · rw [rf]; simp [iterated,output,c,controlConfig]; rfl
  | succ count ih =>
    have hn : n<2^(w*k) := by omega
    have hflag : decide (n<2^(w*k))=true := by simp [hn]
    rw [hflag]
    obtain ⟨body,hbody,bh,bt,_⟩ := RowTupleOutputBody.body_run w k n M x true out hn hM hMw hx hb hp
    have hf := updated_fields w k n x hp
    have he := emitted_eq w k M n x hM hb hx
    rw [he] at bh bt
    obtain ⟨tail,ht,th,tt,_⟩ := ih (n+1) (updated w k n x) (out++entryWord w k M n)
      (by omega) hf.1 (hf.2.1.trans hb) hf.2.2
    have hi : controlConfig (fun _=>test (Fintype.card (RecoveryCalls.Control sizes))) body.final=
        cfg machine.start w k (updated w k n x) (decide (n+1<2^(w*k))) (out++entryWord w k M n) := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [←hi] at ht
    obtain ⟨r,hr,rf⟩ := round_run RowTupleOutputBody.machine 15 (RowTupleOutputBody.budget w k)
      (budget w k count) (cfg RowTupleOutputBody.machine.start w k x true out) body tail rfl
      (by rfl) hbody ht
    have htime : RowTupleOutputBody.budget w k+budget w k count+2=budget w k (count+1) := by
      unfold budget; ring
    rw [htime] at hr
    have hstart : controlConfig (fun _=>test (Fintype.card (RecoveryCalls.Control sizes)))
        (cfg RowTupleOutputBody.machine.start w k x true out)=cfg machine.start w k x true out := by
      apply configuration_ext <;> rfl
    rw [hstart] at hr
    refine ⟨r,hr,?_,?_,runFrom_steps_le machine _ _ r hr⟩
    · rw [rf,th]
      simp only [iterated,output_succ,List.append_assoc]
    · rw [rf,tt]
      simp only [iterated,output_succ,List.append_assoc]

end NearCubicWires.RepairOrdinary.RowTupleOutputLoop
