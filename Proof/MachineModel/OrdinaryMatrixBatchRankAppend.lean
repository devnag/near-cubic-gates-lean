import Proof.MachineModel.OrdinaryMatrixScoreReusableRanks

/-! Append the literal ranked gate packet by its existing frame markers.
Only the bounded packet source is returned; the batch output stays streaming. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRankAppend
open LocalBitMultitape RecoveryExecution
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (words : List (List Bool)) := words.flatMap frame
def stream (words : List (List Bool)) := fields words++[false]
def body := MatrixScoreBankField.machine
def copyMachine := StreamController.machine body 0
def cfg (q : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 5 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem copy_prefix (words : List (List Bool)) (pre suffix out : List Bool)
    (hn : ∀ w∈words,w≠[]) :
    Timed copyMachine ((fields words).length+2*words.length+1)
      (cfg (test 3) (pre++stream words++suffix) pre.length out)
      (cfg (stop 3) (pre++stream words++suffix) (pre.length+(fields words).length) (out++fields words)) := by
  induction words generalizing pre out with
  | nil =>
    have hs := StreamController.stop_step body 0 (MatrixScoreBankField.cfg 0 (pre++[false]++suffix) pre.length out)
      (by simpa [MatrixScoreBankField.cfg,Configuration.scanned,List.append_assoc] using Streaming.read_append pre suffix false)
    simpa [copyMachine,fields,stream,cfg,controlConfig,MatrixScoreBankField.cfg] using Timed.single (StreamController.test_halted body 0) hs
  | cons bits words ih =>
    have hbits := hn bits (by simp)
    let source := pre++frame bits++(stream words++suffix)
    let entry := MatrixScoreBankField.cfg 0 source pre.length out
    obtain ⟨base,hb,bf,bs⟩ := MatrixScoreBankField.field_run bits pre (stream words++suffix) out
    have hread : entry.scanned 0=true := by
      cases bits with
      | nil => contradiction
      | cons b rest =>
        simpa [entry,source,MatrixScoreBankField.cfg,Configuration.scanned,frame,List.append_assoc]
          using Streaming.read_append pre (b::frame rest++(stream words++suffix)) true
    have enter := Timed.single (StreamController.test_halted body 0) (StreamController.enter_step body 0 entry hread)
    have bprefix := (StreamController.body_prefix body 0 _ entry base hb).1
    have copied : Timed copyMachine base.steps (controlConfig code entry) (controlConfig code base.final) := ⟨_,bprefix⟩
    have returned := Timed.single (StreamController.body_halted body 0 base.final.control)
      (StreamController.return_step body 0 base.final (by rw [bf]; rfl))
    have head := enter.trans (copied.trans returned)
    rw [bf,bs] at head
    have tail := ih (pre++frame bits) (out++frame bits) (by intro w hw; exact hn w (by simp [hw]))
    have hsource : (pre++frame bits)++stream words++suffix=source := by simp [source,List.append_assoc]
    have hlen : (pre++frame bits).length=pre.length+(frame bits).length := List.length_append
    rw [hsource,hlen] at tail
    have whole := head.trans tail
    have htime : (1+((2*bits.length+1)+1))+((fields words).length+2*words.length+1)=
        (fields (bits::words)).length+2*(bits::words).length+1 := by
      simp [fields,frame_length]
      omega
    rw [htime] at whole
    simpa [copyMachine,entry,source,fields,stream,cfg,controlConfig,Composition.restart,MatrixScoreBankField.cfg,
      List.append_assoc,Nat.add_assoc] using whole

def terminate : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,some false],![.stay,.right]⟩ else none
def packetMachine := Composition.machine copyMachine terminate
def packetBudget (words : List (List Bool)) := (fields words).length+2*words.length+3
def packetInput (words : List (List Bool)) (out : List Bool) :=
  Composition.leftConfig 2 (cfg (test 3) (stream words) 0 out)

theorem packet_run (words : List (List Bool)) (out : List Bool) (hn : ∀ w∈words,w≠[]) :
    ∃ actual,runFrom packetMachine (packetBudget words) (packetInput words out)=some actual ∧
      actual.final.heads= ![(fields words).length,(out++stream words).length] ∧
      actual.final.tapes= ![stream words,out++stream words] ∧ actual.steps=packetBudget words := by
  obtain ⟨base,hb,bf,bs⟩ := (copy_prefix words [] [] out hn).run (by rfl)
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hb bf
  let entry : Configuration 2 2 := ⟨0,![(fields words).length,(out++fields words).length],![stream words,out++fields words]⟩
  let final : Configuration 2 2 := ⟨1,![(fields words).length,(out++stream words).length],![stream words,out++stream words]⟩
  have hs : step terminate entry=some final := by
    simp [step,terminate,entry]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,final,stream,List.length_append,Nat.add_assoc]
    · funext i
      fin_cases i
      · rfl
      · change writeTapeBit (out++fields words) (out.length+(fields words).length) false=out++stream words
        rw [←List.length_append,Streaming.write_append]
        simp only [stream,List.append_assoc]
  obtain ⟨last,hl,lf,ls⟩ := (Timed.single (by rfl) hs).run (by rfl)
  have he : Composition.restart base.final terminate.start=entry := by rw [bf]; rfl
  rw [←he] at hl
  have joined := Composition.run_join copyMachine terminate _ _ _ base last hb hl
  refine ⟨Composition.joinedReceipt base last,joined,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
  · change last.final.tapes=_
    rw [lf]
  · change base.steps+1+last.steps=_
    rw [bs,ls]
    unfold packetBudget
    omega

def selected (i : Fin 2) : Bool := decide (i=0)
def machine := MaskedReset.machine packetMachine selected
def input (words : List (List Bool)) (out : List Bool) := Rewind.recording (packetInput words out) 0
def budget (words : List (List Bool)) := 2*packetBudget words+2

theorem append_run (words : List (List Bool)) (out : List Bool) (hn : ∀ w∈words,w≠[]) :
    ∃ actual,runFrom machine (budget words) (input words out)=some actual ∧
      actual.final.heads= ![0,(out++stream words).length,0] ∧
      actual.final.tapes= ![stream words,out++stream words,List.replicate (packetBudget words) false] ∧
      actual.steps=budget words := by
  obtain ⟨base,hb,bh,bt,bs⟩ := packet_run words out hn
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=0 := by simpa [selected] using hi
    subst i
    rw [bh,bs]
    change (fields words).length≤packetBudget words
    unfold packetBudget
    omega
  obtain ⟨actual,ha,haf,has,_⟩ := MaskedReset.reset_run packetMachine selected _ (packetInput words out) base hb hh
  rw [bs] at ha has
  refine ⟨actual,ha,?_,?_,has⟩
  · rw [haf,bh]
    funext i
    fin_cases i <;> rfl
  · rw [haf,bt,bs]
    funext i
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.MatrixBatchRankAppend
