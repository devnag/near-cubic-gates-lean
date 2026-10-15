import Proof.MachineModel.OrdinaryTransitionArrayLoop

/-! Reset the framed tape coordinate by physically clearing each payload bit.
The marker scan and the local head return are both charged. -/
namespace NearCubicWires.RepairOrdinary.TransitionTapeZero
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
    some ⟨if bits 0 then 1 else 2,fun _ => none,fun _ => if bits 0 then .right else .stay⟩
    else if q.val=1 then some ⟨0,fun _ => some false,fun _ => .right⟩ else none
def cfg (q : Fin 3) (bits : List Bool) (pos : ℕ) : Configuration 1 3 :=
  ⟨q,fun _ => pos,fun _ => bits⟩

theorem marker_step (pre tail : List Bool) :
    step raw (cfg 0 (pre++true::tail) pre.length)=
      some (cfg 1 (pre++true::tail) (pre.length+1)) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  rfl
theorem bit_step (pre tail : List Bool) (bit : Bool) :
    step raw (cfg 1 (pre++bit::tail) pre.length)=
      some (cfg 0 (pre++false::tail) (pre.length+1)) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    exact BinaryIncrement.write_prefix pre tail bit false
theorem stop_step (pre : List Bool) :
    step raw (cfg 0 (pre++[false]) pre.length)=some (cfg 2 (pre++[false]) pre.length) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  rfl

theorem zero_prefix (pre bits : List Bool) :
    Timed raw (2*bits.length+1) (cfg 0 (pre++frame bits) pre.length)
      (cfg 2 (pre++frame (List.replicate bits.length false)) (pre.length+2*bits.length)) := by
  induction bits generalizing pre with
  | nil => simpa [frame] using Timed.single (by rfl : raw.halted (0 : Fin 3)=false) (stop_step pre)
  | cons b bs ih =>
    have h1 := Timed.single (by rfl : raw.halted (0 : Fin 3)=false) (marker_step pre (b::frame bs))
    have h2 := Timed.single (by rfl : raw.halted (1 : Fin 3)=false) (bit_step (pre++[true]) (frame bs) b)
    have h2' : Timed raw 1 (cfg 1 (pre++frame (b::bs)) (pre.length+1))
        (cfg 0 ((pre++[true,false])++frame bs) (pre++[true,false]).length) := by
      simpa [frame,List.append_assoc] using h2
    have hj := h1.trans (h2'.trans (ih (pre++[true,false])))
    have htime : 1+(1+(2*bs.length+1))=2*(bs.length+1)+1 := by omega
    have hpos : (pre++[true,false]).length+2*bs.length=pre.length+2*(bs.length+1) := by simp; omega
    rw [htime,hpos] at hj
    simpa [frame,List.replicate_succ,List.append_assoc] using hj

def machine : Machine 2 5 := Rewind.machine raw

theorem zero_ready (bits : List Bool) (cap : ℕ) (hc : 2*bits.length+1≤cap) :
    ReadyRun machine (4*bits.length+4)
      ![frame bits,List.replicate cap false]
      ![frame (List.replicate bits.length false),List.replicate cap false] := by
  obtain ⟨base,hb,hf,hs⟩ := (zero_prefix [] bits).run (by rfl)
  have hb' : run raw (2*bits.length+1) (fun _ => frame bits)=some base := hb
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb' cap
  have htime : 2*base.steps+2=4*bits.length+4 := by rw [hs]; omega
  rw [htime] at hr
  have hin : Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
      (fun _ : Fin 1 => frame bits) (fun _ => List.replicate cap false)=
      (![frame bits,List.replicate cap false] : Fin 2 → List Bool) := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨r,hr,?_,hh,hsteps.trans htime⟩
  funext i; fin_cases i
  · simpa [hf,cfg] using ht 0
  · simpa [hs,max_eq_left hc] using hcounter

end NearCubicWires.RepairOrdinary.TransitionTapeZero
