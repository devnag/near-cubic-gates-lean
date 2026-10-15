import Proof.MachineModel.OrdinaryTransitionArrayBody

/-! The whole head/tape-array walk streams actual head fields, validated action
tags and claimed scans. Every array iteration and loop return is charged. -/
namespace NearCubicWires.RepairOrdinary.TransitionArray
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Item where
  tag : TagMachine.Word
  read : Bool
  head : ℕ

def tags : List Item → List Bool
  | [] => []
  | e::es => TagMachine.tagWord e.tag++tags es
def scans : List Item → List Bool
  | [] => []
  | e::es => e.read::scans es
def fields (w : ℕ) : List Item → List Bool
  | [] => []
  | e::es => frame (binary w e.head)++fields w es
def nextHead (e : Item) : ℕ := HeadMove.apply (decodeMove [e.tag 2,e.tag 3]) e.head
def nextFields (w : ℕ) : List Item → List Bool
  | [] => []
  | e::es => frame (binary w (nextHead e))++nextFields w es
def walk (w cap : ℕ) (d : TransitionTape.Store) : List Item → TransitionTape.Store
  | [] => d
  | e::es => walk w cap (finished d w cap e.head e.tag e.read) es

abbrev bodyStates := Fintype.card (RecoveryCalls.Control sizes)
noncomputable def loop := StreamController.machine machine (16 : Fin 18)
def loopBudget (w n : ℕ) : ℕ := n*(bodyBudget w+2)+1

theorem executed_head (d : TransitionTape.Store) (w cap : ℕ) (e : Item) :
    (executed d w cap e.head e.tag e.read).head.head=nextHead e :=
  TransitionTape.finished_head _ _ _ _ _

theorem finished_difference (d : TransitionTape.Store) (w cap : ℕ) (e : Item)
    (hb : d.head.difference.length≤2*w+1) :
    (finished d w cap e.head e.tag e.read).head.difference.length≤2*w+1 :=
  TransitionTape.finished_difference _ _ _ _ _ hb

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control=p.start)
    (hread : c.scanned tape=true) (hbody : runFrom p fuel c=some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => RecordController.test s) body.final)=some tail) :
    ∃ r,runFrom (StreamController.machine p tape) (fuel+tailFuel+2)
      (controlConfig (fun _ => RecordController.test s) c)=some r ∧ r.final=tail.final := by
  obtain ⟨bodyPrefix,halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) := ⟨tail.final,tail.steps+1,max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig RecordController.code body.final)=some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle,hm,hmf,_,_⟩ := bodyPrefix.followedBy returned hr
  have hrestart : Composition.restart c p.start=c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) := ⟨middle.final,middle.steps+1,max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((body.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => RecordController.test s) c)=some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle (StreamController.test_halted p tape) he hm
  have hs := runFrom_steps_le p fuel c body hbody
  have hmore := runFrom_moreFuel (StreamController.machine p tape) _ (fuel-body.steps) _ result hrun
  have ht : ((body.steps+(tailFuel+1))+1)+(fuel-body.steps)=fuel+tailFuel+2 := by omega
  rw [ht] at hmore
  exact ⟨result,hmore,hmf⟩

theorem loop_run (w cap : ℕ) (entries : List Item) (d : TransitionTape.Store)
    (pre out tagPre tagTail scanPre scanTail : List Bool)
    (hvalid : ∀ e∈entries,TagMachine.valid true e.tag=true)
    (hheads : ∀ e∈entries,e.head+1<2^w)
    (hserial : d.serial+entries.length<2^(2*w)) (htape : d.tape+entries.length<2^w)
    (hback : d.head.difference.length≤2*w+1) (hcap : 4*w+3≤cap)
    (htag : d.source=tagPre++Streaming.marks (tags entries)++tagTail) (hpos : d.pos=tagPre.length)
    (hscan : d.scans=scanPre++Streaming.marks (scans entries)++scanTail) (hcursor : d.cursor=scanPre.length) :
    ∃ r,runFrom loop (loopBudget w entries.length)
      (cfg (RecordController.test bodyStates) d w cap (pre++fields w entries) pre.length out)=some r ∧
      r.final=cfg (RecordController.stop bodyStates) (walk w cap d entries) w cap (pre++fields w entries)
        (pre.length+(fields w entries).length) (out++nextFields w entries) := by
  induction entries generalizing d pre out tagPre scanPre with
  | nil =>
    let c := cfg machine.start d w cap pre pre.length out
    have hread : c.scanned 16=false := by
      change readTapeBit pre pre.length=false
      simp [readTapeBit,List.getD]
    let endpoint := controlConfig (fun _ => RecordController.stop bodyStates) c
    let tail : ExecutionReceipt 18 (bodyStates+2) := ⟨endpoint,0,endpoint.tapeCells⟩
    have ht : runFrom loop 0 endpoint=some tail :=
      runFrom_zero_of_halted loop endpoint (StreamController.stop_halted _ _)
    have hr := runFrom_step loop (controlConfig (fun _ => RecordController.test bodyStates) c) endpoint tail
      (StreamController.test_halted _ _) (StreamController.stop_step machine 16 c hread) ht
    refine ⟨⟨tail.final,tail.steps+1,max (controlConfig (fun _ => RecordController.test bodyStates) c).tapeCells tail.peakTapeCells⟩,?_,?_⟩
    · simpa only [loopBudget,List.length_nil,Nat.zero_mul,Nat.zero_add,fields,List.append_nil,
        c,controlConfig,cfg,TapeEmbedding.config,TransitionTape.cfg] using hr
    · simp only [tail,endpoint,c,controlConfig,cfg,TapeEmbedding.config,TransitionTape.cfg,
        fields,nextFields,walk,List.append_nil,List.length_nil,Nat.add_zero]
  | cons e es ih =>
    let source := pre++fields w (e::es)
    let d1 := finished d w cap e.head e.tag e.read
    let out1 := out++frame (binary w (nextHead e))
    have hevalid := hvalid e (by simp)
    have hehead := hheads e (by simp)
    have htag' : d.source=tagPre++Streaming.marks (TagMachine.tagWord e.tag)++
        (Streaming.marks (tags es)++tagTail) := by
      simpa only [tags,Streaming.marks_append,List.append_assoc] using htag
    have hscan' : d.scans=scanPre++true::e.read::(Streaming.marks (scans es)++scanTail) := by
      simpa only [scans,Streaming.marks,List.flatMap_cons,List.cons_append,List.nil_append,List.append_assoc] using hscan
    obtain ⟨body,hb,hbf,_⟩ := body_run d w cap e.head pre (fields w es) out tagPre
      (Streaming.marks (tags es)++tagTail) scanPre (Streaming.marks (scans es)++scanTail) e.tag e.read
      hevalid htag' hpos hscan' hcursor (by simp only [List.length_cons] at hserial; omega) hehead
      (by simp only [List.length_cons] at htape; omega) hback hcap
    have hbodySource : pre++frame (binary w e.head)++fields w es=source := by
      simp only [source,fields,List.append_assoc]
    rw [hbodySource] at hb hbf
    rw [executed_head] at hbf
    have hsource : (pre++frame (binary w e.head))++fields w es=source := by
      simp only [source,fields,List.append_assoc]
    have hposition : (pre++frame (binary w e.head)).length=pre.length+2*w+1 := by simp; omega
    have htags : d1.source=(tagPre++Streaming.marks (TagMachine.tagWord e.tag))++Streaming.marks (tags es)++tagTail := by
      change d.source=_
      simpa only [List.append_assoc] using htag'
    have htagpos : d1.pos=(tagPre++Streaming.marks (TagMachine.tagWord e.tag)).length := by
      change d.pos+8=_
      rw [hpos]
      simp [TagMachine.tagWord]
    have hscans : d1.scans=(scanPre++[true,e.read])++Streaming.marks (scans es)++scanTail := by
      change d.scans=_
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using hscan'
    have hscanpos : d1.cursor=(scanPre++[true,e.read]).length := by change d.cursor+2=_; simp [hcursor]
    obtain ⟨tail,ht,htf⟩ := ih d1 (pre++frame (binary w e.head)) out1
      (tagPre++Streaming.marks (TagMachine.tagWord e.tag)) (scanPre++[true,e.read])
      (by intro a ha; exact hvalid a (by simp [ha])) (by intro a ha; exact hheads a (by simp [ha]))
      (by change d.serial+1+es.length<_; simp only [List.length_cons] at hserial; omega)
      (by change d.tape+1+es.length<_; simp only [List.length_cons] at htape; omega)
      (finished_difference d w cap e hback) htags htagpos hscans hscanpos
    rw [hsource,hposition] at ht htf
    have htail : runFrom loop (loopBudget w es.length)
        (controlConfig (fun _ => RecordController.test bodyStates) body.final)=some tail := by
      rw [hbf]
      exact ht
    have hread : (cfg machine.start d w cap source pre.length out).scanned 16=true := by
      change readTapeBit source pre.length=true
      cases w with
      | zero => simp at hehead
      | succ w =>
        simp only [source,fields,binary,frame,List.cons_append]
        exact Streaming.read_append pre _ true
    obtain ⟨r,hr,hrf⟩ := round_run machine 16 (bodyBudget w) (loopBudget w es.length)
      (cfg machine.start d w cap source pre.length out) body tail rfl hread hb htail
    have htime : bodyBudget w+loopBudget w es.length+2=loopBudget w (e::es).length := by
      simp only [loopBudget,List.length_cons]
      ring
    rw [htime] at hr
    refine ⟨r,hr,?_⟩
    rw [hrf,htf]
    have hposition' : pre.length+2*w+1+(fields w es).length=pre.length+(fields w (e::es)).length := by
      simp [fields]
      omega
    rw [hposition']
    have hout : out1++nextFields w es=out++nextFields w (e::es) := by
      simp only [out1,nextFields,List.append_assoc]
    rw [hout]
    rfl

end NearCubicWires.RepairOrdinary.TransitionArray
