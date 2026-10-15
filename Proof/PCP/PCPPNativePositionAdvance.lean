import Proof.PCP.PCPPNativeNodeReusable

/-! Advance the actual raw current-node position by two and physically
return its cursor to zero. The reusable reset log is already present;
the live descriptor/source tapes are outside this two-tape operation. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativePositionAdvance
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
      some (if bits 0 then ⟨0,fun _ => none,fun _ => .right⟩
        else ⟨1,fun _ => some true,fun _ => .right⟩)
    else if q.val=1 then some ⟨2,fun _ => some true,fun _ => .stay⟩ else none
def cfg (q : Fin 3) (count pos : ℕ) : Configuration 1 3 :=
  ⟨q,fun _ => pos,fun _ => List.replicate count true⟩

theorem scan_step (count pos : ℕ) (hp : pos < count) :
    step raw (cfg 0 count pos)=some (cfg 0 count (pos+1)) := by
  have h := ClockUnaryProduct.read_unary count pos
  simp [step,raw,cfg,Configuration.scanned,h,hp]
  rfl

theorem append_step (count : ℕ) : step raw (cfg 0 count count)=some (cfg 1 (count+1) (count+1)) := by
  have h := ClockUnaryProduct.read_unary count count
  have hw : writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true := by
    have ha := Streaming.write_append (List.replicate count true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using ha
  simp [step,raw,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; simp [applyAction,hw]

theorem last_step (count : ℕ) : step raw (cfg 1 count count)=some (cfg 2 (count+1) count) := by
  have hw : writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true := by
    have ha := Streaming.write_append (List.replicate count true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using ha
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; simp [applyAction,hw]

theorem scan (count pos remaining : ℕ) (hp : pos+remaining ≤ count) :
    Timed raw remaining (cfg 0 count pos) (cfg 0 count (pos+remaining)) := by
  induction remaining generalizing pos with
  | zero => simpa only [Nat.add_zero] using Timed.refl raw (cfg 0 count pos)
  | succ remaining ih =>
    have hs := Timed.single (by rfl) (scan_step count pos (by omega))
    have ht := ih (pos+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans ht

theorem raw_run (count : ℕ) :
    ∃ r,run raw (count+2) (fun _ => List.replicate count true)=some r ∧
      r.final=cfg 2 (count+2) (count+1) ∧ r.steps=count+2 := by
  have hs := scan count 0 count (by omega)
  simp only [Nat.zero_add] at hs
  have ha := Timed.single (by rfl) (append_step count)
  have hb := Timed.single (by rfl) (last_step (count+1))
  exact ((hs.trans ha).trans hb).run (by rfl)

def machine := Rewind.machine raw
theorem advance_ready (count F : ℕ) (hF : count+2 ≤ F) :
    ReadyRun machine (2*count+6) ![List.replicate count true,List.replicate F false]
      ![List.replicate (count+2) true,List.replicate F false] := by
  obtain ⟨a,ha,af,as⟩ := raw_run count
  obtain ⟨r,hr,rt,log,hh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ a ha F
  have ht : 2*a.steps+2=2*count+6 := by omega
  rw [ht] at hr
  have inputEq : (Fin.addCases (m := 1) (n := 1) (motive := fun _ : Fin 2 => List Bool)
      (fun _ => List.replicate count true) (fun _ => List.replicate F false))=
      ![List.replicate count true,List.replicate F false] := by
    funext i; fin_cases i <;> rfl
  rw [inputEq] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · have h := rt 0
    rw [af] at h
    exact h
  · rw [as,max_eq_left hF] at log
    exact log

end NearCubicWires.RepairOrdinary.PCPPNativePositionAdvance
