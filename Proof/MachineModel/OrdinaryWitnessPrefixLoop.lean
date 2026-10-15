import Proof.MachineModel.OrdinaryWitnessPrefixBody

/-! The bounded witness loop consumes precisely B supplied bits, with a
small binary comparison per bit. Its source suffix is retained and unread. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefixLoop
open LocalBitMultitape
open RecordController (code test stop)
open WitnessPrefixBody (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 6 17 := StreamController.machine WitnessPrefixBody.machine 2
def budget (w n : ℕ) : ℕ := n*(8*w+12)+1

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

theorem loop_run (w counter bound cap : ℕ) (pre bits suffix out : List Bool)
    (hremaining : counter+bits.length=bound+1) (hbound : bound+1<2^w) (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 6 17,
      runFrom machine (budget w bits.length)
        (config (test 15) w counter bound cap (decide (counter≤bound))
          (pre++frame (bits++suffix)) out pre.length)=some r ∧
      r.final=config (stop 15) w (bound+1) bound cap false
        (pre++frame (bits++suffix)) (out++Streaming.marks bits) (pre.length+2*bits.length) := by
  induction bits generalizing counter pre out with
  | nil =>
    have hc : counter=bound+1 := by simpa using hremaining
    subst counter
    let c := config WitnessPrefixBody.machine.start w (bound+1) bound cap false
      (pre++frame suffix) out pre.length
    have hread : c.scanned 2=false := by rfl
    let endpoint := controlConfig (fun _ => stop 15) c
    let tail : ExecutionReceipt 6 17 := ⟨endpoint,0,endpoint.tapeCells⟩
    have ht : runFrom machine 0 endpoint=some tail :=
      runFrom_zero_of_halted machine endpoint (StreamController.stop_halted _ _)
    have hr := runFrom_step machine (controlConfig (fun _ => test 15) c) endpoint tail
      (StreamController.test_halted _ _) (StreamController.stop_step WitnessPrefixBody.machine 2 c hread) ht
    refine ⟨⟨tail.final,tail.steps+1,max (controlConfig (fun _ => test 15) c).tapeCells tail.peakTapeCells⟩,?_,?_⟩
    · simpa [budget,c,controlConfig,config,TapeEmbedding.config,WitnessCounterCheck.config] using hr
    · simp [tail,endpoint,c,Streaming.marks,controlConfig,config,TapeEmbedding.config,WitnessCounterCheck.config]
  | cons bit bits ih =>
    have hc : counter≤bound := by simp only [List.length_cons] at hremaining; omega
    have hflag : decide (counter≤bound)=true := by simp [hc]
    rw [hflag]
    let source := pre++frame ((bit::bits)++suffix)
    have hbit : readTapeBit source (pre.length+1)=bit := by
      have he : source=(pre++[true])++(bit::frame (bits++suffix)) := by
        simp [source,frame,List.append_assoc]
      rw [he]
      have hl : pre.length+1=(pre++[true]).length := by simp
      rw [hl]
      exact Streaming.read_append _ _ bit
    obtain ⟨body,hb,hbf⟩ := WitnessPrefixBody.body_run w counter bound cap source out pre.length
      (by omega) (by omega) hcap
    rw [hbit] at hbf
    obtain ⟨tail,ht,htf⟩ := ih (counter+1) (pre++[true,bit]) (out++[true,bit])
      (by simp only [List.length_cons] at hremaining; omega)
    have hsource : (pre++[true,bit])++frame (bits++suffix)=source := by
      simp [source,frame,List.append_assoc]
    have hcursor : (pre++[true,bit]).length=pre.length+2 := by simp
    rw [hsource,hcursor] at ht htf
    have htail : runFrom machine (budget w bits.length)
        (controlConfig (fun _ => test 15) body.final)=some tail := by rw [hbf]; exact ht
    have hread : (config WitnessPrefixBody.machine.start w counter bound cap true source out pre.length).scanned 2=true := by rfl
    obtain ⟨r,hr,hrf⟩ := round_run WitnessPrefixBody.machine 2 (8*w+10) (budget w bits.length)
      (config WitnessPrefixBody.machine.start w counter bound cap true source out pre.length)
      body tail rfl hread hb htail
    have htime : (8*w+10)+budget w bits.length+2=budget w (bit::bits).length := by
      simp only [budget,List.length_cons]
      ring
    rw [htime] at hr
    refine ⟨r,hr,?_⟩
    rw [hrf,htf]
    have hcursor' : pre.length+2+2*bits.length=pre.length+2*(bit::bits).length := by simp; omega
    rw [hcursor']
    simp only [Streaming.marks,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append,source]

end NearCubicWires.RepairOrdinary.WitnessPrefixLoop
