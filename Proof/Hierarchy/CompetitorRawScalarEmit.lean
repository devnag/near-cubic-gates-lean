import Proof.Hierarchy.CompetitorSignedResidue

/-! Strip one actual framed scalar into its raw fixed-width output stream. The
source and unary scratch heads are restored; the output head remains at
the next append cell. This is the scalar producer's physical record bridge. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawScalarEmit
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (state : Fin 4) (sourceMove targetMove counterMove : HeadMove)
    (targetWrite counterWrite : Option Bool) : Action 3 4 :=
  ⟨state,![none,targetWrite,counterWrite],![sourceMove,targetMove,counterMove]⟩
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val==3
  rule := fun state scanned => if state.val=0 then
      if scanned 0 then some (action 1 .right .stay .right none (some true))
      else some (action 2 .right .stay .stay none (some true))
    else if state.val=1 then some (action 0 .right .right .right (some (scanned 0)) (some true))
    else if state.val=2 then
      if scanned 2 then some (action 2 .left .stay .left none (some false))
      else some (action 3 .stay .stay .stay none none)
    else none
def scan (state : Fin 4) (source : List Bool) (position : ℕ) (out : List Bool) : Configuration 3 4 :=
  ⟨state,![position,out.length,position],![source,out,List.replicate position true]⟩
def reset (state : Fin 4) (source target : List Bool) (remaining erased : ℕ) : Configuration 3 4 :=
  ⟨state,![remaining,target.length,remaining-1],
    ![source,target,List.replicate remaining true++List.replicate erased false]⟩

theorem marker_step (pre tail out : List Bool) :
    step machine (scan 0 (pre++true::tail) pre.length out)=
      some (scan 1 (pre++true::tail) (pre.length+1) out) := by
  have hr := Streaming.read_append pre tail true
  simp [step,machine,scan,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,action,List.replicate_add]

theorem bit_step (pre tail out : List Bool) (bit : Bool) :
    step machine (scan 1 (pre++bit::tail) pre.length out)=
      some (scan 0 (pre++bit::tail) (pre.length+1) (out++[bit])) := by
  have hr := Streaming.read_append pre tail bit
  simp [step,machine,scan,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,action,Streaming.write_append,List.replicate_add]

theorem delimiter_step (pre tail out : List Bool) :
    step machine (scan 0 (pre++false::tail) pre.length out)=
      some (reset 2 (pre++false::tail) out (pre.length+1) 0) := by
  have hr := Streaming.read_append pre tail false
  simp [step,machine,scan,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,action,HeadMove.apply,reset]
  · funext i
    fin_cases i <;> simp [applyAction,action,reset,List.replicate_add]

theorem rewind_step (source target : List Bool) (remaining erased : ℕ) :
    step machine (reset 2 source target (remaining+1) erased)=
      some (reset 2 source target remaining (erased+1)) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_counter]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,action,Streaming.erase_counter]

theorem stop_step (source target : List Bool) (erased : ℕ) :
    step machine (reset 2 source target 0 erased)=some (reset 3 source target 0 erased) := by
  simp [step,machine,reset,Configuration.scanned,Streaming.read_zeros]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,action]

theorem reset_timed (source target : List Bool) (remaining erased : ℕ) :
    Timed machine (remaining+1) (reset 2 source target remaining erased)
      (reset 3 source target 0 (remaining+erased)) := by
  induction remaining generalizing erased with
  | zero => simpa using Timed.single (by rfl) (stop_step source target erased)
  | succ remaining ih =>
    have hp := (Timed.single (by rfl) (rewind_step source target remaining erased)).trans (ih (erased+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hp

theorem scan_timed (pre bits suffix out : List Bool) :
    Timed machine (2*bits.length+1) (scan 0 (pre++frame bits++suffix) pre.length out)
      (reset 2 (pre++frame bits++suffix) (out++bits) (pre.length+2*bits.length+1) 0) := by
  induction bits generalizing pre out with
  | nil => simpa [frame] using Timed.single (by rfl) (delimiter_step pre suffix out)
  | cons bit bits ih =>
    let source := pre++frame (bit::bits)++suffix
    have he : (pre++[true,bit])++frame bits++suffix=source := by simp [source,frame,List.append_assoc]
    have hi := ih (pre++[true,bit]) (out++[bit])
    rw [he] at hi
    have hfirst : Timed machine 1 (scan 0 source pre.length out)
        (scan 1 source (pre.length+1) out) := by
      simpa [source,frame,List.append_assoc] using Timed.single (by rfl)
        (marker_step pre (bit::frame bits++suffix) out)
    have hsecond : Timed machine 1 (scan 1 source (pre.length+1) out)
        (scan 0 source (pre.length+2) (out++[bit])) := by
      simpa [source,frame,List.append_assoc,Nat.add_assoc] using Timed.single (by rfl)
        (bit_step (pre++[true]) (frame bits++suffix) out bit)
    have htail : Timed machine (2*bits.length+1) (scan 0 source (pre.length+2) (out++[bit]))
        (reset 2 source (out++(bit::bits)) (pre.length+2*(bit::bits).length+1) 0) := by
      simpa [frame,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi
    have hall := hfirst.trans (hsecond.trans htail)
    have htime : 1+(1+(2*bits.length+1))=2*(bit::bits).length+1 := by simp; omega
    rw [htime] at hall
    exact hall

theorem append_run (bits suffix out : List Bool) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom machine (4*bits.length+3) (scan 0 (frame bits++suffix) 0 out)=some r ∧
      r.final=reset 3 (frame bits++suffix) (out++bits) 0 (2*bits.length+1) ∧
      r.steps=4*bits.length+3 := by
  have hscan := scan_timed [] bits suffix out
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hscan
  have hreset := reset_timed (frame bits++suffix) (out++bits) (2*bits.length+1) 0
  have hall := hscan.trans hreset
  have hcost : (2*bits.length+1)+(2*bits.length+1+1)=4*bits.length+3 := by omega
  rw [hcost] at hall
  obtain ⟨r,hr,hf,hs⟩ := hall.run (by rfl)
  exact ⟨r,hr,by simpa using hf,hs⟩

end NearCubicWires.RepairOrdinary.CompetitorRawScalarEmit
