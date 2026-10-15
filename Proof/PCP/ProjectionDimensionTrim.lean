import Proof.MachineModel.ClockPaddingReady

/-! A positive binary field is scanned to its delimiter, then its trailing
zero pairs are erased backwards. No numeric value is expanded into unary. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.DimensionTrim
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 5) (write : Option Bool) (move : HeadMove) : Action 1 5 :=
  ⟨q,fun _ => write,fun _ => move⟩
def machine : Machine 1 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bits => if q.val=0 then
      some (if bits 0 then action 1 none .right else action 2 none .left)
    else if q.val=1 then some (action 0 none .right)
    else if q.val=2 then some (if bits 0 then action 4 none .right else action 3 none .left)
    else if q.val=3 then some (action 2 (some false) .left) else none
def cfg (q : Fin 5) (bits : List Bool) (pos : ℕ) : Configuration 1 5 :=
  ⟨q,fun _ => pos,fun _ => bits⟩

theorem move_step (q next : Fin 5) (bits : List Bool) (pos : ℕ) (move : HeadMove)
    (hr : machine.rule q (fun _ => readTapeBit bits pos)=some (action next none move)) :
    step machine (cfg q bits pos)=some (cfg next bits (move.apply pos)) := by
  change Option.map (applyAction (cfg q bits pos))
    (machine.rule q (fun _ => readTapeBit bits pos))=some (cfg next bits (move.apply pos))
  rw [hr]
  rfl

theorem write_at (pre suffix : List Bool) (old bit : Bool) :
    writeTapeBit (pre++old::suffix) pre.length bit=pre++bit::suffix := by
  induction pre with
  | nil => rfl
  | cons b bs ih => simpa only [List.cons_append,List.length_cons,writeTapeBit] using congrArg (List.cons b) ih

theorem erase_step (pre suffix : List Bool) :
    step machine (cfg 3 (pre++true::suffix) pre.length)=
      some (cfg 2 (pre++false::suffix) (pre.length-1)) := by
  simp only [step,machine,cfg,show (3 : Fin 5).val=3 by rfl]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact write_at pre suffix true false

theorem front (pre bits : List Bool) :
    Timed machine (2*bits.length) (cfg 0 (Streaming.marks pre++frame bits) (2*pre.length))
      (cfg 0 (Streaming.marks pre++frame bits) (2*(pre.length+bits.length))) := by
  induction bits generalizing pre with
  | nil => simpa using Timed.refl machine (cfg 0 (Streaming.marks pre++frame []) (2*pre.length))
  | cons b bs ih =>
    let source := Streaming.marks pre++frame (b::bs)
    have hm : readTapeBit source (2*pre.length)=true := by
      simpa only [source,frame,RepairOrdinary.frame,Streaming.marks_length] using
        Streaming.read_append (Streaming.marks pre) (b::frame bs) true
    have h1 := move_step 0 1 source (2*pre.length) .right (by simp [machine,hm])
    have h2 := move_step 1 0 source (2*pre.length+1) .right (by rfl)
    have htail := ih (pre++[b])
    have he : Streaming.marks (pre++[b])++frame bs=source := by
      simp [source,Streaming.marks,frame,RepairOrdinary.frame,List.append_assoc]
    rw [he] at htail
    have hp : (pre++[b]).length=pre.length+1 := by simp
    rw [hp] at htail
    have h := (Timed.single (by rfl : machine.halted (0 : Fin 5)=false) h1).trans
      ((Timed.single (by rfl : machine.halted (1 : Fin 5)=false) h2).trans htail)
    have htime : 1+(1+2*bs.length)=2*(b::bs).length := by simp; omega
    rw [htime] at h
    simpa only [HeadMove.apply,source,List.length_cons,Nat.mul_add,Nat.mul_one,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def backTape (pre : List Bool) (zeros erased : ℕ) :=
  Streaming.marks (pre++[true])++Streaming.marks (List.replicate zeros false)++
    List.replicate (2*erased+1) false

theorem back (pre : List Bool) (zeros erased : ℕ) :
    Timed machine (2*zeros+1)
      (cfg 2 (backTape pre zeros erased) (2*(pre.length+1+zeros)-1))
      (cfg 4 (backTape pre 0 (zeros+erased)) (2*(pre.length+1))) := by
  induction zeros generalizing erased with
  | zero =>
    let p := Streaming.marks pre++[true]
    have hs : backTape pre 0 erased=p++true::List.replicate (2*erased+1) false := by
      simp [backTape,p,Streaming.marks,List.append_assoc]
    have hl : p.length=2*pre.length+1 := by simp [p]
    have hb : readTapeBit (backTape pre 0 erased) (2*(pre.length+1)-1)=true := by
      rw [hs]
      have he : 2*(pre.length+1)-1=p.length := by omega
      rw [he]
      exact Streaming.read_append p _ true
    have h := move_step 2 4 (backTape pre 0 erased) (2*(pre.length+1)-1) .right
      (by simp [machine,hb])
    have he : HeadMove.right.apply (2*(pre.length+1)-1)=2*(pre.length+1) := by simp [HeadMove.apply]; omega
    rw [he] at h
    simpa using Timed.single (by rfl : machine.halted (2 : Fin 5)=false) h
  | succ zeros ih =>
    let p := Streaming.marks (pre++[true])++Streaming.marks (List.replicate zeros false)
    have hl : p.length=2*(pre.length+1+zeros) := by simp [p]; omega
    have hs : backTape pre (zeros+1) erased=p++true::false::List.replicate (2*erased+1) false := by
      rw [backTape,show zeros+1=zeros+1 by rfl,List.replicate_add]
      simp [p,Streaming.marks,List.append_assoc]
    have hb : readTapeBit (backTape pre (zeros+1) erased) (p.length+1)=false := by
      rw [hs]
      simpa only [List.length_append,List.length_singleton,List.append_assoc,List.cons_append,List.nil_append] using
        Streaming.read_append (p++[true]) (List.replicate (2*erased+1) false) false
    have h1 := move_step 2 3 (backTape pre (zeros+1) erased) (p.length+1) .left
      (by simp [machine,hb])
    have h2 := erase_step p (false::List.replicate (2*erased+1) false)
    rw [←hs] at h2
    have he : p++false::false::List.replicate (2*erased+1) false=backTape pre zeros (erased+1) := by
      change p++false::false::List.replicate (2*erased+1) false=p++List.replicate (2*(erased+1)+1) false
      have hh := (List.replicate_add 2 (2*erased+1) false).symm
      have hn : 2+(2*erased+1)=2*(erased+1)+1 := by omega
      rw [hn] at hh
      exact congrArg (fun xs => p++xs) hh
    rw [he] at h2
    simp only [HeadMove.apply,Nat.add_sub_cancel] at h1
    rw [hl] at h1 h2
    have htail := ih (erased+1)
    have h := (Timed.single (by rfl : machine.halted (2 : Fin 5)=false) h1).trans
      ((Timed.single (by rfl : machine.halted (3 : Fin 5)=false) h2).trans htail)
    have htime : 1+(1+(2*zeros+1))=2*(zeros+1)+1 := by omega
    have hpos : 2*(pre.length+1+zeros)+1=2*(pre.length+1+(zeros+1))-1 := by omega
    have hend : zeros+(erased+1)=zeros+1+erased := by omega
    rw [htime,hpos,hend] at h
    exact h

theorem trim_run (pre : List Bool) (zeros : ℕ) :
    ∃ r,run machine (2*(pre.length+1+zeros)+2*zeros+2)
      (fun _ => frame (pre++[true]++List.replicate zeros false))=some r ∧
      r.final=cfg 4 (backTape pre 0 zeros) (2*(pre.length+1)) ∧
      r.steps=2*(pre.length+1+zeros)+2*zeros+2 := by
  let bits := pre++[true]++List.replicate zeros false
  have hf := front [] bits
  simp only [Streaming.marks,List.flatMap_nil,List.nil_append,List.length_nil,Nat.mul_zero,Nat.zero_add] at hf
  have ht : frame bits=backTape pre zeros 0 := by
    have hz : frame (List.replicate zeros false)=Streaming.marks (List.replicate zeros false)++[false] := by
      simpa only [List.append_nil,frame,RepairOrdinary.frame] using Streaming.frame_append (List.replicate zeros false) []
    simp only [bits,Streaming.frame_append,backTape,Nat.mul_zero,Nat.zero_add,List.replicate_one,hz,Streaming.marks,List.flatMap_append,List.append_assoc]
  have hl : bits.length=pre.length+1+zeros := by simp [bits]; omega
  have hs : readTapeBit (frame bits) (2*bits.length)=false := by
    have he : frame bits=Streaming.marks bits++[false] := by
      simpa [frame,RepairOrdinary.frame] using Streaming.frame_append bits []
    rw [he]
    simpa only [Streaming.marks_length] using Streaming.read_append (Streaming.marks bits) [] false
  have hs0 := move_step 0 2 (frame bits) (2*bits.length) .left (by simp [machine,hs])
  have hb := back pre zeros 0
  rw [←ht,←hl] at hb
  have h := hf.trans ((Timed.single (by rfl : machine.halted (0 : Fin 5)=false) hs0).trans hb)
  obtain ⟨r,hr,hfinal,hsteps⟩ := h.run (by rfl)
  have htime : 2*bits.length+(1+(2*zeros+1))=2*(pre.length+1+zeros)+2*zeros+2 := by rw [hl]; omega
  rw [htime] at hr hsteps
  refine ⟨r,?_,?_,?_⟩
  · simpa only [run,initialConfiguration,machine,cfg,bits] using hr
  · simpa only [Nat.add_zero] using hfinal
  · exact hsteps

end NearCubicWires.RepairSource.ProjectionNormalization.DimensionTrim
