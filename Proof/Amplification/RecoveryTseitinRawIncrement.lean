import Proof.Amplification.RecoveryTseitinNativeReuseErase

/-! Increment the actual raw unary node counter and physically restore its
head using the existing bounded rewind log. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinRawIncrement
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some (if bits 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>some true,fun _=>.stay⟩) else none
def cfg (q : Fin 2) (count pos : Nat) : Configuration 1 2 :=
  ⟨q,fun _=>pos,fun _=>List.replicate count true⟩
theorem scan_step (count pos : Nat) (hp : pos < count) :
    step raw (cfg 0 count pos)=some (cfg 0 count (pos+1)) := by
  have h:=ClockUnaryProduct.read_unary count pos
  simp [step,raw,cfg,Configuration.scanned,h,hp]
  rfl
theorem append_step (count : Nat) : step raw (cfg 0 count count)=some (cfg 1 (count+1) count) := by
  have h:=ClockUnaryProduct.read_unary count count
  have hw : writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true := by
    have ha:=Streaming.write_append (List.replicate count true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using ha
  simp [step,raw,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; simp [applyAction,hw]
theorem scan (count pos remaining : Nat) (hp : pos+remaining ≤ count) :
    Timed raw remaining (cfg 0 count pos) (cfg 0 count (pos+remaining)) := by
  induction remaining generalizing pos with
  | zero=>simpa only [Nat.add_zero] using Timed.refl raw (cfg 0 count pos)
  | succ remaining ih=>
    have h:=(Timed.single (by rfl) (scan_step count pos (by omega))).trans (ih (pos+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
theorem raw_run (count : Nat) :
    ∃ r,run raw (count+1) (fun _=>List.replicate count true)=some r ∧
      r.final=cfg 1 (count+1) count ∧ r.steps=count+1 := by
  have h:=scan count 0 count (by omega)
  simp only [Nat.zero_add] at h
  exact (h.trans (Timed.single (by rfl) (append_step count))).run (by rfl)
def machine:=Rewind.machine raw
theorem increment_ready (count cap : Nat) (hcap : count+1 ≤ cap) :
    ReadyRun machine (2*count+4) ![List.replicate count true,List.replicate cap false]
      ![List.replicate (count+1) true,List.replicate cap false] := by
  obtain ⟨a,ha,af,asteps⟩:=raw_run count
  obtain ⟨r,hr,rt,log,hh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ a ha cap
  have ht : 2*a.steps+2=2*count+4 := by omega
  rw [ht] at hr
  have hi : (Fin.addCases (m:=1) (n:=1) (motive:=fun _ : Fin 2=>List Bool)
      (fun _=>List.replicate count true) (fun _=>List.replicate cap false))=
      ![List.replicate count true,List.replicate cap false] := by funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · have h:=rt 0
    rw [af] at h
    exact h
  · rw [asteps,max_eq_left hcap] at log
    exact log

end NearCubicWires.RepairSource.RecoveryTseitinRawIncrement
