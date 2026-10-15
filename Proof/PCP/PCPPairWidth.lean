import Proof.PCP.PCPPairRun

/-! Produce the actual pair width from the two framed operand tapes.
Each payload uses two cells and each delimiter one, so writing one unary
mark per scanned framed cell produces exactly 2*(left.length+right.length+1).
The source payload bits need no arithmetic interpretation. -/
namespace NearCubicWires.RepairOrdinary.PCPPairWidth
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 5) (leftMove rightMove : HeadMove) : Action 3 5 :=
  ⟨next,![none,none,some true],![leftMove,rightMove,.right]⟩
def raw : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bits =>
    ![some (if bits 0 then action 1 .right .stay else action 2 .stay .stay),
      some (action 0 .right .stay),
      some (if bits 1 then action 3 .stay .right else action 4 .stay .stay),
      some (action 2 .stay .right),none] q
def scanState (left : Bool) : Fin 5 := if left then 0 else 2
def payloadState (left : Bool) : Fin 5 := if left then 1 else 3
def cfg (left : Bool) (state : Fin 5) (source other : List Bool)
    (pos otherPos : ℕ) (out : List Bool) : Configuration 3 5 :=
  ⟨state,if left then ![pos,otherPos,out.length] else ![otherPos,pos,out.length],
    if left then ![source,other,out] else ![other,source,out]⟩

theorem marker_step (left : Bool) (pre tail other out : List Bool) (otherPos : ℕ) :
    step raw (cfg left (scanState left) (pre++true::tail) other pre.length otherPos out)=some
      (cfg left (payloadState left) (pre++true::tail) other (pre.length+1) otherPos (out++[true])) := by
  cases left <;> simp [step,raw,cfg,scanState,payloadState,Configuration.scanned,Streaming.read_append]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem payload_step (left : Bool) (source other out : List Bool) (pos otherPos : ℕ) :
    step raw (cfg left (payloadState left) source other pos otherPos out)=some
      (cfg left (scanState left) source other (pos+1) otherPos (out++[true])) := by
  cases left <;> simp [step,raw,cfg,scanState,payloadState]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,action,Streaming.write_append]

theorem scan_prefix (left : Bool) (bits pre other out : List Bool) (otherPos : ℕ) :
    Timed raw (2*bits.length)
      (cfg left (scanState left) (pre++frame bits) other pre.length otherPos out)
      (cfg left (scanState left) (pre++frame bits) other (pre.length+2*bits.length)
        otherPos (out++List.replicate (2*bits.length) true)) := by
  induction bits generalizing pre out with
  | nil => simp only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.replicate_zero,List.append_nil]; exact Timed.refl _ _
  | cons bit bits ih =>
    have he : (pre++[true,bit])++frame bits=pre++frame (bit::bits) := by
      simp [frame,List.append_assoc]
    have ht := ih (pre++[true,bit]) (out++[true,true])
    rw [he] at ht
    have htail : Timed raw (2*bits.length)
        (cfg left (scanState left) (pre++frame (bit::bits)) other (pre.length+2) otherPos (out++[true,true]))
        (cfg left (scanState left) (pre++frame (bit::bits)) other (pre.length+2*(bit::bits).length)
          otherPos (out++List.replicate (2*(bit::bits).length) true)) := by
      convert ht using 1 <;> simp [List.replicate_add,List.append_assoc,Nat.mul_add,Nat.add_assoc,Nat.add_comm]
    have hpay := payload_step left (pre++frame (bit::bits)) other (out++[true]) (pre.length+1) otherPos
    rw [show pre.length+1+1=pre.length+2 by omega] at hpay
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hpay
    have hmark := marker_step left pre (bit::frame bits) other out otherPos
    have h0 : raw.halted (scanState left)=false := by cases left <;> rfl
    have h1 : raw.halted (payloadState left)=false := by cases left <;> rfl
    have h := (Timed.single h0 hmark).trans ((Timed.single h1 hpay).trans htail)
    convert h using 1 <;> simp only [frame,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

end NearCubicWires.RepairOrdinary.PCPPairWidth
