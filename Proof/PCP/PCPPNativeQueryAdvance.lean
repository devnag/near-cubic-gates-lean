import Proof.PCP.PCPPNativeQueryBody
import Proof.MachineModel.OrdinaryPartitionWorkspace

/-! Compute the next query base from its actual final copied-node position.
The shorter old base is overwritten/extended by real writes; both counters
become position+1 and both heads are physically reset. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryAdvance
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open StablePartition.Workspace (overlay overlay_write)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then
    some (if bits 0 then ⟨0,![none,some true],fun _ => .right⟩
      else ⟨1,fun _ => some true,fun _ => .stay⟩) else none
def cfg (count base pos : ℕ) : Configuration 2 2 :=
  ⟨0,fun _ => pos,![List.replicate count true,overlay (List.replicate pos true) (List.replicate base true)]⟩
def final (count : ℕ) : Configuration 2 2 :=
  ⟨1,fun _ => count,fun _ => List.replicate (count+1) true⟩

theorem overwrite (pos base : ℕ) :
    writeTapeBit (overlay (List.replicate pos true) (List.replicate base true)) pos true=
      overlay (List.replicate (pos+1) true) (List.replicate base true) := by
  have h := overlay_write (List.replicate pos true) (List.replicate base true) true
  simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using h
theorem overlay_done (count base : ℕ) (hb : base ≤ count) :
    overlay (List.replicate count true) (List.replicate base true)=List.replicate count true := by
  simp only [overlay,List.length_replicate,List.drop_replicate,Nat.sub_eq_zero_of_le hb,List.replicate_zero,List.append_nil]
theorem scan_step (count base pos : ℕ) (hp : pos < count) :
    step raw (cfg count base pos)=some (cfg count base (pos+1)) := by
  have h := ClockUnaryProduct.read_unary count pos
  simp [step,raw,cfg,Configuration.scanned,h,hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [applyAction,overwrite]
theorem append_step (count base : ℕ) (hb : base ≤ count) :
    step raw (cfg count base count)=some (final count) := by
  have h := ClockUnaryProduct.read_unary count count
  have hw : writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true := by
    have ha := Streaming.write_append (List.replicate count true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using ha
  simp [step,raw,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,final,overlay_done count base hb,hw]
theorem scan (count base pos remaining : ℕ) (hp : pos+remaining ≤ count) :
    Timed raw remaining (cfg count base pos) (cfg count base (pos+remaining)) := by
  induction remaining generalizing pos with
  | zero => simpa only [Nat.add_zero] using Timed.refl raw (cfg count base pos)
  | succ remaining ih =>
    have h := (Timed.single (by rfl) (scan_step count base pos (by omega))).trans (ih (pos+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
theorem raw_run (count base : ℕ) (hb : base ≤ count) :
    ∃ r,run raw (count+1) ![List.replicate count true,List.replicate base true]=some r ∧
      r.final=final count ∧ r.steps=count+1 := by
  have hs := scan count base 0 count (by omega)
  simp only [Nat.zero_add] at hs
  have hall := hs.trans (Timed.single (by rfl) (append_step count base hb))
  have hi : cfg count base 0=initialConfiguration raw ![List.replicate count true,List.replicate base true] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [cfg,initialConfiguration,overlay]
  rw [hi] at hall
  exact hall.run (by rfl)

def machine := Rewind.machine raw
theorem advance_ready (count base F : ℕ) (hb : base ≤ count) (hF : count+1 ≤ F) :
    ReadyRun machine (2*count+4) ![List.replicate count true,List.replicate base true,List.replicate F false]
      ![List.replicate (count+1) true,List.replicate (count+1) true,List.replicate F false] := by
  obtain ⟨a,ha,af,as⟩ := raw_run count base hb
  obtain ⟨r,hr,rt,log,hh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ a ha F
  have htime : 2*a.steps+2=2*count+4 := by omega
  rw [htime] at hr
  have hinput : (Fin.addCases (m := 2) (n := 1) (motive := fun _ : Fin 3 => List Bool)
      ![List.replicate count true,List.replicate base true] (fun _ => List.replicate F false))=
      ![List.replicate count true,List.replicate base true,List.replicate F false] := by
    funext i; fin_cases i <;> rfl
  rw [hinput] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · exact (rt 0).trans (by rw [af]; rfl)
  · exact (rt 1).trans (by rw [af]; rfl)
  · rw [as,max_eq_left hF] at log
    exact log

end NearCubicWires.RepairOrdinary.PCPPNativeQueryAdvance
