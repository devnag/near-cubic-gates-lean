import Proof.Amplification.RecoveryDecodeStep

/-! Raw Encodable lists use a successor of a pair code. This actual ordinary
pass performs binary predecessor in place and records nonzeroness, then pays
the rewind. Zero inputs are detected without interpreting the wrapped word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryListPredecessor
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def borrowNext (a old : Bool) := old && !a
def result : List Bool → Bool → List Bool
  | [],_ => []
  | a::rest,old => xor a old :: result rest (borrowNext a old)
def finalBorrow : List Bool → Bool → Bool
  | [],old => old
  | a::rest,old => finalBorrow rest (borrowNext a old)

@[simp] theorem result_length (bits : List Bool) (old : Bool) :
    (result bits old).length=bits.length := by
  induction bits generalizing old with
  | nil => rfl
  | cons a rest ih => simp [result,ih]

theorem result_value (bits : List Bool) (old : Bool) :
    value (result bits old)+old.toNat=value bits+2^bits.length*(finalBorrow bits old).toNat := by
  induction bits generalizing old with
  | nil => simp [result,finalBorrow,value]
  | cons a rest ih =>
    have hi := ih (borrowNext a old)
    have hb : (xor a old).toNat+old.toNat=a.toNat+2*(borrowNext a old).toNat := by
      cases a <;> cases old <;> rfl
    simp only [result,finalBorrow,value,List.length_cons,pow_succ]
    nlinarith

theorem finalBorrow_eq (bits : List Bool) (old : Bool) :
    finalBorrow bits old=(old && decide (value bits=0)) := by
  induction bits generalizing old with
  | nil => simp [finalBorrow,value]
  | cons a rest ih =>
    rw [finalBorrow,ih]
    cases a <;> cases old <;> simp [borrowNext,value]

theorem predecessor_value (bits : List Bool) (h : value bits≠0) :
    value (result bits true)=value bits-1 := by
  have hr := result_value bits true
  simp only [finalBorrow_eq,h,decide_false,Bool.and_false,Bool.toNat_false,
    Bool.toNat_true,Nat.mul_zero,Nat.add_zero] at hr
  omega

def scanState (old : Bool) : Fin 5 := if old then 1 else 0
def bitState (old : Bool) : Fin 5 := if old then 3 else 2
def action (q : Fin 5) (move : HeadMove) (data flag : Option Bool) : Action 2 5 :=
  ⟨q,![data,flag],![move,.stay]⟩
def rawMachine : Machine 2 5 where
  descriptionBits := 0
  start := scanState true
  halted := fun q => q.val==4
  rule := fun q scanned =>
    if q.val<2 then
      if scanned 0 then some (action (bitState (q.val==1)) .right none none)
      else some (action 4 .stay none (some (!(q.val==1))))
    else if q.val<4 then
      some (action (scanState (borrowNext (scanned 0) (q.val==3))) .right
        (some (xor (scanned 0) (q.val==3))) none)
    else none

def cfg (q : Fin 5) (tape : List Bool) (position : Nat) (flag : Bool) : Configuration 2 5 :=
  ⟨q,![position,0],![tape,[flag]]⟩

theorem write_inside (pre tail : List Bool) (old new : Bool) :
    writeTapeBit (pre++old::tail) pre.length new=pre++new::tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [writeTapeBit] using congrArg (List.cons a) ih

theorem marker_step (pre rest : List Bool) (a old flag : Bool) :
    step rawMachine (cfg (scanState old) (pre++frame (a::rest)) pre.length flag)=
      some (cfg (bitState old) (pre++frame (a::rest)) (pre.length+1) flag) := by
  have hr : readTapeBit (pre++frame (a::rest)) pre.length=true := by
    simpa [frame] using Streaming.read_append pre (a::frame rest) true
  cases old <;> simp [step,rawMachine,scanState,bitState,cfg,Configuration.scanned,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem bit_step (pre rest : List Bool) (a old flag : Bool) :
    step rawMachine (cfg (bitState old) (pre++frame (a::rest)) (pre.length+1) flag)=
      some (cfg (scanState (borrowNext a old))
        ((pre++[true,xor a old])++frame rest) (pre.length+2) flag) := by
  have hr : readTapeBit (pre++frame (a::rest)) (pre.length+1)=a := by
    simpa [frame,List.append_assoc] using Streaming.read_append (pre++[true]) (frame rest) a
  have hw : writeTapeBit (pre++frame (a::rest)) (pre.length+1) (xor a old)=
      (pre++[true,xor a old])++frame rest := by
    simpa [frame,List.append_assoc] using write_inside (pre++[true]) (frame rest) a (xor a old)
  cases old <;> simp [step,rawMachine,bitState,cfg,Configuration.scanned,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> first
    | rfl
    | simpa [applyAction,action] using hw)

theorem stop_step (pre : List Bool) (old flag : Bool) :
    step rawMachine (cfg (scanState old) (pre++frame []) pre.length flag)=
      some (cfg 4 (pre++frame []) pre.length (!old)) := by
  have hr : readTapeBit (pre++frame []) pre.length=false := by
    simpa [frame] using Streaming.read_append pre [] false
  cases old <;> simp [step,rawMachine,scanState,cfg,Configuration.scanned,hr] <;>
    apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> rfl)

theorem scan_prefix (pre bits : List Bool) (old flag : Bool) :
    Timed rawMachine (2*bits.length+1)
      (cfg (scanState old) (pre++frame bits) pre.length flag)
      (cfg 4 (pre++frame (result bits old)) (pre.length+2*bits.length) (!(finalBorrow bits old))) := by
  induction bits generalizing pre old with
  | nil => simpa [result,finalBorrow] using Timed.single (by cases old <;> rfl) (stop_step pre old flag)
  | cons a rest ih =>
    have ht := ih (pre++[true,xor a old]) (borrowNext a old)
    have hb := bit_step pre rest a old flag
    have hp := Timed.step (by cases old <;> rfl) (marker_step pre rest a old flag)
      (Timed.step (by cases old <;> rfl) hb (by simpa using ht))
    have he : 2*rest.length+1+1+1=2*(a::rest).length+1 := by simp; omega
    rw [he] at hp
    have hpos : pre.length+2+2*rest.length=pre.length+2*(a::rest).length := by simp; omega
    rw [hpos] at hp
    exact hp

def machine := Rewind.machine rawMachine

theorem predecessor_ready (bits : List Bool) (oldFlag : Bool) (capacity : Nat) :
    ReadyRun machine (4*bits.length+4)
      ![frame bits,[oldFlag],List.replicate capacity false]
      ![frame (result bits true),[decide (value bits≠0)],
        List.replicate (max capacity (2*bits.length+1)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := (scan_prefix [] bits true oldFlag).run (by rfl)
  have hin : cfg (scanState true) ([]++frame bits) 0 oldFlag=
      initialConfiguration rawMachine ![frame bits,[oldFlag]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  simp only [List.length_nil] at hr
  rw [hin] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace rawMachine _ _ base hr capacity
  have he : 2*base.steps+2=4*bits.length+4 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hf,cfg,finalBorrow_eq] using ht 1
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryListPredecessor
