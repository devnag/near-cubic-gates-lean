import Proof.PCP.PCPUnaryStackPop

/-! Physical return dispatch for the balanced DFS controller. A continuation
cell is [phase,true] above a false bottom marker. False phase changes to true
after the left child; true phase is popped after the right child. Halt codes
5/6/7 distinguish these actual branches without a supplied logical flag. -/
namespace NearCubicWires.RepairOrdinary.PCPContinuation
open LocalBitMultitape RecoveryExecution
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 8) (write : Option Bool) (move : HeadMove) : Action 1 8 :=
  ⟨q,fun _ => write,fun _ => move⟩
def machine : Machine 1 8 where
  descriptionBits := 0
  start := 0
  halted := fun q => 5≤q.val
  rule := fun q bits => if q.val=0 then some (action 1 none .left)
    else if q.val=1 then some (if bits 0 then action 2 none .left else action 6 none .right)
    else if q.val=2 then some (if bits 0 then action 4 (some false) .right else action 3 (some true) .right)
    else if q.val=3 then some (action 5 none .right)
    else if q.val=4 then some (action 7 (some false) .left) else none
def cfg (q : Fin 8) (stack : List Bool) (pos : ℕ) : Configuration 1 8 :=
  ⟨q,fun _ => pos,fun _ => stack⟩

theorem move_step (q next : Fin 8) (stack : List Bool) (pos : ℕ) (move : HeadMove)
    (hr : machine.rule q (fun _ => readTapeBit stack pos)=some (action next none move)) :
    step machine (cfg q stack pos)=some (cfg next stack (move.apply pos)) := by
  change Option.map (applyAction (cfg q stack pos))
    (machine.rule q (fun _ => readTapeBit stack pos))=_
  rw [hr]
  rfl

theorem write_step (q next : Fin 8) (pre suffix : List Bool) (old bit : Bool) (move : HeadMove)
    (hr : machine.rule q (fun _ => old)=some (action next (some bit) move)) :
    step machine (cfg q (pre++old::suffix) pre.length)=
      some (cfg next (pre++bit::suffix) (move.apply pre.length)) := by
  have hscan : (cfg q (pre++old::suffix) pre.length).scanned=fun _ => old := by
    funext i
    exact Streaming.read_append pre suffix old
  simp only [step,hscan,show (cfg q (pre++old::suffix) pre.length).control=q from rfl,hr]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact DimensionTrim.write_at pre suffix old bit

theorem enter (pre : List Bool) (b : Bool) (z : ℕ) :
    Timed machine 2 (cfg 0 (pre++b::true::List.replicate z false) (pre.length+2))
      (cfg 2 (pre++b::true::List.replicate z false) pre.length) := by
  let stack := pre++b::true::List.replicate z false
  have h1 := move_step 0 1 stack (pre.length+2) .left (by rfl)
  have hb : readTapeBit stack (pre.length+1)=true := by
    simpa only [stack,List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using
      Streaming.read_append (pre++[b]) (List.replicate z false) true
  have h2 := move_step 1 2 stack (pre.length+1) .left (by simp [machine,hb])
  simp only [HeadMove.apply,show pre.length+2-1=pre.length+1 by omega,Nat.add_sub_cancel] at h1 h2
  exact (Timed.single (by rfl : machine.halted (0 : Fin 8)=false) h1).trans
    (Timed.single (by rfl : machine.halted (1 : Fin 8)=false) h2)

theorem left_return (pre : List Bool) (z : ℕ) :
    Timed machine 4 (cfg 0 (pre++false::true::List.replicate z false) (pre.length+2))
      (cfg 5 (pre++true::true::List.replicate z false) (pre.length+2)) := by
  have h1 := write_step 2 3 pre (true::List.replicate z false) false true .right (by rfl)
  have h2 := move_step 3 5 (pre++true::true::List.replicate z false) (pre.length+1) .right (by rfl)
  have h := (enter pre false z).trans ((Timed.single (by rfl : machine.halted (2 : Fin 8)=false) h1).trans
    (Timed.single (by rfl : machine.halted (3 : Fin 8)=false) h2))
  simpa only [HeadMove.apply,Nat.add_assoc] using h

theorem right_return (pre : List Bool) (z : ℕ) :
    Timed machine 4 (cfg 0 (pre++true::true::List.replicate z false) (pre.length+2))
      (cfg 7 (pre++List.replicate (z+2) false) pre.length) := by
  have h1 := write_step 2 4 pre (true::List.replicate z false) true false .right (by rfl)
  have h2 := write_step 4 7 (pre++[false]) (List.replicate z false) true false .left (by rfl)
  simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append,
    HeadMove.apply,Nat.add_sub_cancel] at h1 h2
  have h := (enter pre true z).trans ((Timed.single (by rfl : machine.halted (2 : Fin 8)=false) h1).trans
    (Timed.single (by rfl : machine.halted (4 : Fin 8)=false) h2))
  have he : List.replicate (z+2) false=false::false::List.replicate z false := by
    rw [show z+2=2+z by omega,List.replicate_add]
    rfl
  simpa only [he] using h

theorem empty_return (z : ℕ) :
    Timed machine 2 (cfg 0 (List.replicate (z+1) false) 1)
      (cfg 6 (List.replicate (z+1) false) 1) := by
  have h1 := move_step 0 1 (List.replicate (z+1) false) 1 .left (by rfl)
  have h2 := move_step 1 6 (List.replicate (z+1) false) 0 .right
    (by simp [machine,Streaming.read_zeros])
  exact (Timed.single (by rfl : machine.halted (0 : Fin 8)=false) h1).trans
    (Timed.single (by rfl : machine.halted (1 : Fin 8)=false) h2)

end NearCubicWires.RepairOrdinary.PCPContinuation
