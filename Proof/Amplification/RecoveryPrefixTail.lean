import Proof.Amplification.RecoveryPrefixSentinel

/-! Actual local update of a sentinel-bearing committed prefix. The framed
field is scanned, its candidate bit written from the oracle answer, and a
new zero candidate and high true sentinel are physically installed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixTail
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 12) (move : HeadMove) (write : Option Bool := none) : Action 2 12 :=
  ⟨q,![write,none],![move,.stay]⟩
def raw : Machine 2 12 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==11
  rule := fun q bits =>
    if q.val=0 then some (if bits 0 then action 1 .right else action 2 .left)
    else if q.val=1 then some (action 0 .right)
    else if q.val=2 then some (action 3 .left (some false))
    else if q.val=3 then some (action 4 .left)
    else if q.val=4 then some (action 5 .right (some (!bits 1)))
    else if q.val=5 then some (action 6 .right)
    else if q.val=6 then some (action 7 .right)
    else if q.val=7 then some (action 8 .right (some true))
    else if q.val=8 then some (action 9 .right (some true))
    else if q.val=9 then some (action 11 .stay (some false))
    else none

def cfg (q : Fin 12) (tape : List Bool) (position : Nat) (answer : Bool) : Configuration 2 12 :=
  ⟨q,![position,0],![tape,[answer]]⟩

theorem read_offset (pre rest : List Bool) (j : Nat) :
    readTapeBit (pre++rest) (pre.length+j)=readTapeBit rest j := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega),Nat.add_sub_cancel_left]
theorem write_offset (pre rest : List Bool) (j : Nat) (b : Bool) :
    writeTapeBit (pre++rest) (pre.length+j) b=pre++writeTapeBit rest j b := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simpa only [List.cons_append,List.length_cons,Nat.succ_add,writeTapeBit] using congrArg (List.cons a) ih

theorem marker_step (pre rest : List Bool) (a answer : Bool) :
    step raw (cfg 0 (pre++frame (a::rest)) pre.length answer)=
      some (cfg 1 (pre++frame (a::rest)) (pre.length+1) answer) := by
  have hr : readTapeBit (pre++frame (a::rest)) pre.length=true := by
    simpa [frame] using Streaming.read_append pre (a::frame rest) true
  simp [step,raw,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem payload_step (pre rest : List Bool) (a answer : Bool) :
    step raw (cfg 1 (pre++frame (a::rest)) (pre.length+1) answer)=
      some (cfg 0 ((pre++[true,a])++frame rest) (pre.length+2) answer) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [applyAction,action,frame]

theorem scanned_at (pre rest : List Bool) (q : Fin 12) (j : Nat) (answer : Bool) :
    (cfg q (pre++rest) (pre.length+j) answer).scanned=![readTapeBit rest j,answer] := by
  funext i
  fin_cases i
  · exact read_offset pre rest j
  · rfl

theorem step_at (pre rest : List Bool) (q q' : Fin 12) (j : Nat) (answer : Bool)
    (move : HeadMove) (write : Option Bool)
    (hr : raw.rule q ![readTapeBit rest j,answer]=some (action q' move write)) :
    step raw (cfg q (pre++rest) (pre.length+j) answer)=
      some (cfg q' (pre++(match write with | none=>rest | some b=>writeTapeBit rest j b))
        (move.apply (pre.length+j)) answer) := by
  simp only [step,scanned_at]
  dsimp only [cfg]
  simp only [hr,Option.map_some,Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · cases write with
      | none => rfl
      | some b => exact write_offset pre rest j b
    · rfl

theorem tail_trace (pre : List Bool) (answer : Bool) :
    Timed raw 13 (cfg 0 (pre++frame [false,true]) pre.length answer)
      (cfg 11 (pre++frame [!answer,false,true]) (pre.length+6) answer) := by
  have h0 : step raw (cfg 0 (pre++[true,false,true,true,false]) (pre.length+0) answer)=
      some (cfg 1 (pre++[true,false,true,true,false]) (pre.length+1) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,false,true,true,false] 0 1 0 answer .right none (by rfl)
  have h1 : step raw (cfg 1 (pre++[true,false,true,true,false]) (pre.length+1) answer)=
      some (cfg 0 (pre++[true,false,true,true,false]) (pre.length+2) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,false,true,true,false] 1 0 1 answer .right none (by rfl)
  have h2 : step raw (cfg 0 (pre++[true,false,true,true,false]) (pre.length+2) answer)=
      some (cfg 1 (pre++[true,false,true,true,false]) (pre.length+3) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,false,true,true,false] 0 1 2 answer .right none (by rfl)
  have h3 : step raw (cfg 1 (pre++[true,false,true,true,false]) (pre.length+3) answer)=
      some (cfg 0 (pre++[true,false,true,true,false]) (pre.length+4) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,false,true,true,false] 1 0 3 answer .right none (by rfl)
  have h4 : step raw (cfg 0 (pre++[true,false,true,true,false]) (pre.length+4) answer)=
      some (cfg 2 (pre++[true,false,true,true,false]) (pre.length+3) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit,show pre.length+4-1=pre.length+3 by omega] using
      step_at pre [true,false,true,true,false] 0 2 4 answer .left none (by rfl)
  have h5 : step raw (cfg 2 (pre++[true,false,true,true,false]) (pre.length+3) answer)=
      some (cfg 3 (pre++[true,false,true,false,false]) (pre.length+2) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit,show pre.length+3-1=pre.length+2 by omega] using
      step_at pre [true,false,true,true,false] 2 3 3 answer .left (some (false)) (by rfl)
  have h6 : step raw (cfg 3 (pre++[true,false,true,false,false]) (pre.length+2) answer)=
      some (cfg 4 (pre++[true,false,true,false,false]) (pre.length+1) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit,show pre.length+2-1=pre.length+1 by omega] using
      step_at pre [true,false,true,false,false] 3 4 2 answer .left none (by rfl)
  have h7 : step raw (cfg 4 (pre++[true,false,true,false,false]) (pre.length+1) answer)=
      some (cfg 5 (pre++[true,!answer,true,false,false]) (pre.length+2) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,false,true,false,false] 4 5 1 answer .right (some (!answer)) (by rfl)
  have h8 : step raw (cfg 5 (pre++[true,!answer,true,false,false]) (pre.length+2) answer)=
      some (cfg 6 (pre++[true,!answer,true,false,false]) (pre.length+3) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,!answer,true,false,false] 5 6 2 answer .right none (by rfl)
  have h9 : step raw (cfg 6 (pre++[true,!answer,true,false,false]) (pre.length+3) answer)=
      some (cfg 7 (pre++[true,!answer,true,false,false]) (pre.length+4) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,!answer,true,false,false] 6 7 3 answer .right none (by rfl)
  have h10 : step raw (cfg 7 (pre++[true,!answer,true,false,false]) (pre.length+4) answer)=
      some (cfg 8 (pre++[true,!answer,true,false,true]) (pre.length+5) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,!answer,true,false,false] 7 8 4 answer .right (some (true)) (by rfl)
  have h11 : step raw (cfg 8 (pre++[true,!answer,true,false,true]) (pre.length+5) answer)=
      some (cfg 9 (pre++[true,!answer,true,false,true,true]) (pre.length+6) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,!answer,true,false,true] 8 9 5 answer .right (some (true)) (by rfl)
  have h12 : step raw (cfg 9 (pre++[true,!answer,true,false,true,true]) (pre.length+6) answer)=
      some (cfg 11 (pre++[true,!answer,true,false,true,true,false]) (pre.length+6) answer) := by
    simpa only [HeadMove.apply,Nat.add_sub_cancel,Nat.add_zero,Nat.add_assoc,writeTapeBit] using
      step_at pre [true,!answer,true,false,true,true] 9 11 6 answer .stay (some (false)) (by rfl)
  exact Timed.step (by rfl) h0 (Timed.step (by rfl) h1 (Timed.step (by rfl) h2 (Timed.step (by rfl) h3 (Timed.step (by rfl) h4 (Timed.step (by rfl) h5 (Timed.step (by rfl) h6 (Timed.step (by rfl) h7 (Timed.step (by rfl) h8 (Timed.step (by rfl) h9 (Timed.step (by rfl) h10 (Timed.step (by rfl) h11 (Timed.step (by rfl) h12 (Timed.refl _ _)))))))))))))

end NearCubicWires.RepairOrdinary.RecoveryPrefixTail
