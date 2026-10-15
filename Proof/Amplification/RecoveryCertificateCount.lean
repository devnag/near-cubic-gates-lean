import Proof.Amplification.RecoveryCertificateWord
import Proof.Amplification.RecoveryTimedExecution
import Proof.PCP.VerifierDecodingUnary
import Proof.PCP.VerifierDecodingCompare

/-! Physical capped unary count parsing for the one flat NP certificate.
The retained query-derived cap is checked before every emitted count cell.
Success rewinds both local unary tapes while retaining the source cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateCount
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 5) (sourceMove localMove : HeadMove) (write : Option Bool := none) : Action 3 5 :=
  ⟨next,![none,write,none],![sourceMove,localMove,localMove]⟩
def machine : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun state => 3 ≤ state.val
  rule := fun state bits =>
    if state.val=0 then some (action (if bits 0 then 1 else 4) .right .stay)
    else if state.val=1 then
      if bits 0 then
        if bits 2 then some (action 0 .right .right (some true))
        else some (action 4 .right .stay)
      else some (action 2 .right .left)
    else if state.val=2 then
      some (if bits 2 then action 2 .stay .left else action 3 .stay .right)
    else none
def cfg (state : Fin 5) (source : List Bool) (pos count cap head : Nat) : Configuration 3 5 :=
  ⟨state,![pos,head,head],![source,CompareMachine.word count,CompareMachine.word cap]⟩
def scan (state : Fin 5) (source : List Bool) (pos count cap : Nat) := cfg state source pos count cap (count+1)

theorem marker_step (pre tail : List Bool) (count cap : Nat) (marker : Bool) :
    step machine (scan 0 (pre++marker::tail) pre.length count cap)=
      some (scan (if marker then 1 else 4) (pre++marker::tail) (pre.length+1) count cap) := by
  simp [step,machine,scan,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem true_step (pre tail : List Bool) (count cap : Nat) (hc : count<cap) :
    step machine (scan 1 (pre++true::tail) pre.length count cap)=
      some (scan 0 (pre++true::tail) (pre.length+1) (count+1) cap) := by
  simp [step,machine,scan,cfg,Configuration.scanned,Streaming.read_append,hc]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]
    have h := Streaming.write_append (CompareMachine.word count) true
    simpa only [CompareMachine.word,List.length_cons,List.length_replicate,
      List.replicate_add,List.replicate_one,List.cons_append] using h

theorem full_step (pre tail : List Bool) (cap : Nat) :
    step machine (scan 1 (pre++true::tail) pre.length cap cap)=
      some (scan 4 (pre++true::tail) (pre.length+1) cap cap) := by
  simp [step,machine,scan,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem false_step (pre tail : List Bool) (count cap : Nat) :
    step machine (scan 1 (pre++false::tail) pre.length count cap)=
      some (cfg 2 (pre++false::tail) (pre.length+1) count cap count) := by
  simp [step,machine,scan,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem true_prefix (n : Nat) (pre tail : List Bool) (count cap : Nat) (hc : count+n≤cap) :
    let source := pre++Streaming.marks (List.replicate n true)++tail
    Timed machine (2*n) (scan 0 source pre.length count cap)
      (scan 0 source (pre.length+2*n) (count+n) cap) := by
  induction n generalizing pre count with
  | zero => simpa [Streaming.marks] using Timed.refl machine (scan 0 (pre++tail) pre.length count cap)
  | succ n ih =>
    let source := pre++Streaming.marks (List.replicate (n+1) true)++tail
    have hs : (pre++[true,true])++Streaming.marks (List.replicate n true)++tail=source := by
      simp [source,List.replicate_succ,Streaming.marks,List.append_assoc]
    have ht := ih (pre++[true,true]) (count+1) (by omega)
    dsimp only at ht
    rw [hs] at ht
    have htail : Timed machine (2*n) (scan 0 source (pre.length+2) (count+1) cap)
        (scan 0 source (pre.length+2*(n+1)) (count+(n+1)) cap) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using ht
    have h1 : Timed machine (2*n+1) (scan 1 source (pre.length+1) count cap)
        (scan 0 source (pre.length+2*(n+1)) (count+(n+1)) cap) :=
      Timed.step (by rfl)
        (by simpa [source,List.replicate_succ,Streaming.marks,List.append_assoc] using
          true_step (pre++[true]) (Streaming.marks (List.replicate n true)++tail) count cap (by omega))
        htail
    have h0 := Timed.step (by rfl : machine.halted (0 : Fin 5)=false)
      (by simpa [source,List.replicate_succ,Streaming.marks,List.append_assoc] using
        marker_step pre (true::Streaming.marks (List.replicate n true)++tail) count cap true) h1
    simpa [source,List.replicate_succ,Streaming.marks,List.append_assoc,Nat.mul_add,Nat.add_assoc] using h0

theorem rewind_step (source : List Bool) (pos count cap head : Nat) (hh : head<cap) :
    step machine (cfg 2 source pos count cap (head+1))=some (cfg 2 source pos count cap head) := by
  simp [step,machine,cfg,Configuration.scanned,hh]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_stop (source : List Bool) (pos count cap : Nat) :
    step machine (cfg 2 source pos count cap 0)=some (cfg 3 source pos count cap 1) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_run (source : List Bool) (pos count cap head : Nat) (hh : head≤cap) :
    Timed machine (head+1) (cfg 2 source pos count cap head) (cfg 3 source pos count cap 1) := by
  induction head with
  | zero => exact Timed.single (by rfl) (rewind_stop source pos count cap)
  | succ head ih => exact Timed.step (by rfl) (rewind_step source pos count cap head (by omega)) (ih (by omega))

theorem parse_run (n cap : Nat) (pre fields : List Bool) (hn : n≤cap) :
    let source := pre++frame (List.replicate n true++false::fields)
    ∃ receipt : ExecutionReceipt 3 5,
      runFrom machine (3*n+3) (scan 0 source pre.length 0 cap)=some receipt ∧
      receipt.final=cfg 3 source (pre.length+2*n+2) n cap 1 ∧ receipt.steps=3*n+3 := by
  let source := pre++frame (List.replicate n true++false::fields)
  let before := pre++Streaming.marks (List.replicate n true)
  have hsource : before++true::false::frame fields=source := by
    simp [before,source,Streaming.frame_append,RepairOrdinary.frame,List.append_assoc]
  have hbefore : before.length=pre.length+2*n := by simp [before,Streaming.marks_length]
  have ht := rewind_run source (before.length+2) n cap n hn
  have h1 := Timed.step (by rfl : machine.halted (1 : Fin 5)=false)
    (by simpa [hsource,List.append_assoc] using false_step (before++[true]) (frame fields) n cap) ht
  have h0 := Timed.step (by rfl : machine.halted (0 : Fin 5)=false)
    (by simpa [hsource] using marker_step before (false::frame fields) n cap true) h1
  rw [hbefore] at h0
  have hp := true_prefix n pre (true::false::frame fields) 0 cap (by omega)
  dsimp only at hp
  rw [hsource] at hp
  simp only [Nat.zero_add] at hp
  have h := hp.trans h0
  have he : 2*n+(n+1+1+1)=3*n+3 := by omega
  rw [he] at h
  exact h.run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryCertificateCount
