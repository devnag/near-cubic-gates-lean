import Proof.CaseAnalysis.RowsEstimatorParityShift

/-! Reusable copies append complete support frames or native frame fragments at logical length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Fragment
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def body (bits : List Bool):=bits.flatMap (fun b=>[true,b])
def word (close : Bool) (bits : List Bool):=body bits++if close then [false] else []
theorem frame_eq (bits : List Bool) : frame bits=body bits++[false] := by
  induction bits with
  | nil=>rfl
  | cons b bs ih=>simp [frame,body,ih]

def machine (close : Bool) : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then
      some ⟨if bits 0 then 1 else 2,![none,if bits 0 || close then some (bits 0) else none],
        ![.right,if bits 0 || close then .right else .stay]⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _=>.right⟩ else none
def cfg:=CloseoutRowsTouching.FrameStream.cfg

theorem marker_step (close b : Bool) (pre tail out : List Bool) :
    step (machine close) (cfg 0 (pre++b::tail) pre.length out)=
      some (cfg (if b then 1 else 2) (pre++b::tail) (pre.length+1)
        (out++if b || close then [b] else [])) := by
  simp [step,machine,cfg,CloseoutRowsTouching.FrameStream.cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;cases close <;> cases b <;> fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;cases close <;> cases b <;> fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem bit_step (close b : Bool) (pre tail out : List Bool) :
    step (machine close) (cfg 1 (pre++b::tail) pre.length out)=
      some (cfg 0 (pre++b::tail) (pre.length+1) (out++[b])) := by
  exact CloseoutRowsTouching.FrameStream.bit_step b pre tail out

theorem copy_timed (close : Bool) (pre bits tail out : List Bool) :
    Timed (machine close) (2*bits.length+1)
      (cfg 0 (pre++frame bits++tail) pre.length out)
      (cfg 2 (pre++frame bits++tail) (pre.length+2*bits.length+1) (out++word close bits)) := by
  induction bits generalizing pre out with
  | nil=>simpa [frame,word,body] using Timed.single (by rfl) (marker_step close false pre tail out)
  | cons b bits ih=>
    let source:=pre++frame (b::bits)++tail
    have hm:step (machine close) (cfg 0 source pre.length out)=
        some (cfg 1 source (pre.length+1) (out++[true])):=by
      simpa [source,frame,List.append_assoc] using marker_step close true pre (b::frame bits++tail) out
    have hb:step (machine close) (cfg 1 source (pre.length+1) (out++[true]))=
        some (cfg 0 source (pre.length+2) (out++[true,b])):=by
      simpa [source,frame,List.append_assoc,Nat.add_assoc] using bit_step close b (pre++[true]) (frame bits++tail) (out++[true])
    have he:(pre++[true,b])++frame bits++tail=source:=by simp [source,frame,List.append_assoc]
    have ht:=ih (pre++[true,b]) (out++[true,b])
    rw [he] at ht
    have hp:(pre++[true,b]).length=pre.length+2:=by simp
    rw [hp] at ht
    have h:=(Timed.single (by rfl) hm).trans ((Timed.single (by rfl) hb).trans ht)
    have htime:1+(1+(2*bits.length+1))=2*(b::bits).length+1:=by simp;omega
    have hpos:pre.length+2+2*bits.length+1=pre.length+2*(b::bits).length+1:=by simp;omega
    rw [htime,hpos] at h
    simpa only [source,word,body,frame,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append] using h

noncomputable def reusable (close : Bool):=MaskedReset.machine (machine close) (fun i=>decide (i=0))

theorem reusable_run (close : Bool) (bits tail out : List Bool) :
    Step (reusable close) (4*bits.length+4) (![0,out.length,0]) (![frame bits++tail,out,[]])
      (![0,(out++word close bits).length,0])
      (![frame bits++tail,out++word close bits,List.replicate (2*bits.length+1) false]) := by
  obtain ⟨base,hb,bf,bs⟩:=(copy_timed close [] bits tail out).run (by rfl)
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.reset_run (machine close) (fun i=>decide (i=0)) _ _ base hb (by
    intro i hi
    have h0:i=0:=of_decide_eq_true hi
    subst i
    rw [bf,bs]
    change 0+2*bits.length+1≤2*bits.length+1
    omega)
  rw [bs,show 2*(2*bits.length+1)+2=4*bits.length+4 by omega] at hr
  have hi:Rewind.recording (cfg 0 ([]++frame bits++tail) 0 out) 0=
      (⟨(reusable close).start,![0,out.length,0],![frame bits++tail,out,[]]⟩ : Configuration 3 5):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  simp only [List.length_nil] at hr
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,by rw [rs,bs];omega⟩
  · rw [rf,bf]
    funext i;fin_cases i <;>rfl
  · rw [rf,bf,bs]
    funext i;fin_cases i <;>rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Fragment
