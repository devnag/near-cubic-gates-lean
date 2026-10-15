import Proof.CaseAnalysis.RecoveryFixedContinue

/-! Restore the actual framed randomness field in place. The fixed scan
writes each data bit false, retains the frame markers and pays its rewind.
It covers width zero and needs no separately allocated zero-word template. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowRandomZero
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q scanned=>if q.val=0 then
    some (if scanned 0 then ⟨1,fun _=>none,fun _=>.right⟩ else ⟨2,fun _=>none,fun _=>.stay⟩)
    else if q.val=1 then some ⟨0,fun _=>some false,fun _=>.right⟩ else none

def cfg (q : Fin 3) (word : List Bool) (pos : ℕ) : Configuration 1 3:=⟨q,fun _=>pos,fun _=>word⟩

theorem mark_step (pre : List Bool) (bit : Bool) (tail : List Bool) :
    step raw (cfg 0 (pre++frame (bit::tail)) pre.length)=
      some (cfg 1 (pre++frame (bit::tail)) (pre.length+1)) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append,frame]
  rfl

theorem bit_step (pre : List Bool) (bit : Bool) (tail : List Bool) :
    step raw (cfg 1 (pre++frame (bit::tail)) (pre.length+1))=
      some (cfg 0 (pre++frame (false::tail)) (pre.length+2)) := by
  simp only [step,raw,cfg]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;rfl
  · funext i
    change writeTapeBit (pre++frame (bit::tail)) (pre.length+1) false=pre++frame (false::tail)
    have h:=BinaryIncrement.write_prefix (pre++[true]) (frame tail) bit false
    simpa only [frame,List.append_assoc,List.length_append,List.length_singleton,List.cons_append,List.nil_append] using h

theorem stop_step (pre : List Bool) :
    step raw (cfg 0 (pre++[false]) pre.length)=some (cfg 2 (pre++[false]) pre.length) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  rfl

theorem trace (pre bits : List Bool) :
    Timed raw (2*bits.length+1) (cfg 0 (pre++frame bits) pre.length)
      (cfg 2 (pre++frame (List.replicate bits.length false)) (pre.length+2*bits.length)) := by
  induction bits generalizing pre with
  | nil=>simpa only [List.length_nil,List.replicate_zero,frame,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using
      (Timed.single (by rfl) (stop_step pre))
  | cons bit bits ih=>
    have h:=((Timed.single (by rfl) (mark_step pre bit bits)).trans
      (Timed.single (by rfl) (bit_step pre bit bits))).trans (by
        simpa [frame,List.append_assoc] using ih (pre++[true,false]))
    convert h using 1 <;> simp [cfg,List.replicate_succ,frame,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def machine:=Rewind.machine raw

theorem ready (bits : List Bool) (cap : ℕ) (hc : 2*bits.length+1≤cap) :
    ClockJoin.ReadyRun machine (4*bits.length+4)
      ![frame bits,List.replicate cap false] ![frame (List.replicate bits.length false),List.replicate cap false] := by
  obtain ⟨base,br,bf,bs⟩:=(trace [] bits).run (by rfl)
  have br' : run raw (2*bits.length+1) (fun _=>frame bits)=some base := by
    simpa [run,initialConfiguration,cfg,raw] using br
  obtain ⟨r,rr,rt,rl,rh,rs,_⟩:=Rewind.Workspace.reset_workspace raw (2*bits.length+1) _ base br' cap
  have hb : 2*base.steps+2=4*bits.length+4:=by omega
  rw [hb] at rr
  refine ⟨r,?_,?_,rh,(rs.trans hb).le⟩
  · convert rr using 1
    congr 1
    funext i;fin_cases i <;> rfl
  · funext i;fin_cases i
    · change r.final.tapes 0=frame (List.replicate bits.length false)
      have h:=rt 0
      rw [bf] at h
      exact h
    · change r.final.tapes 1=List.replicate cap false
      have hfit : base.steps≤cap:=by omega
      rw [max_eq_left hfit] at rl
      exact rl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowRandomZero
