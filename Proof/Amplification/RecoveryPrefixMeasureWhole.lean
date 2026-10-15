import Proof.Amplification.RecoveryPrefixMeasure

/-! Cold whole measurement of the actual search request, including the
zero-length case and an executed all-head rewind. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixMeasure
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def request (payload total : Nat) := frame payload.bits++frame (List.replicate total true)
def mass (payload total : Nat) := payload.bits.length+2*total+4
def rawBudget (payload total : Nat) := 2*payload.bits.length+3*total+7

theorem frame_marks (bits : List Bool) : frame bits=Streaming.marks bits++[false] := by
  simpa only [List.append_nil,RepairOrdinary.frame] using Streaming.frame_append bits []

theorem whole_trace (payload total : Nat) :
    Timed raw (rawBudget payload total) (initialConfiguration raw ![request payload total,[],[]])
      (cfg 11 (request payload total) (2*payload.bits.length+1+2*total) (mass payload total) total) := by
  let source := request payload total
  have hp := payload_trace payload.bits [] (frame (List.replicate total true)) 4 0
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hp
  have hs := separator_step (Streaming.marks payload.bits) (frame (List.replicate total true)) (4+payload.bits.length) 0
  have hs' : step raw (cfg 5 source (2*payload.bits.length) (4+payload.bits.length) 0)=
      some (cfg 8 source (2*payload.bits.length+1) (4+payload.bits.length) 0) := by
    simpa only [Streaming.marks_length,source,request,frame_marks,List.append_assoc,List.singleton_append] using hs
  have hd := driver_trace total (frame payload.bits) [] (4+payload.bits.length) 0
  simp only [List.append_nil,frame_length,Nat.zero_add] at hd
  have hf := finish (frame payload.bits++Streaming.marks (List.replicate total true)) []
    (4+payload.bits.length+2*total) total
  have hf' : step raw (cfg 8 source (2*payload.bits.length+1+2*total)
      (4+payload.bits.length+2*total) total)=
      some (cfg 11 source (2*payload.bits.length+1+2*total) (4+payload.bits.length+2*total) total) := by
    simpa [source,request,frame_marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
  have whole := (boot_trace source).trans (hp.trans ((Timed.single (by rfl) hs').trans
    (hd.trans (Timed.single (by rfl) hf'))))
  have hc : 5+(2*payload.bits.length+(1+(3*total+1)))=rawBudget payload total := by simp [rawBudget]; omega
  rw [hc] at whole
  convert whole using 1
  congr 1
  dsimp [mass]
  omega

theorem raw_run (payload total : Nat) : ∃ r,
    run raw (rawBudget payload total) ![request payload total,[],[]]=some r ∧
      r.final.tapes=![request payload total,List.replicate (mass payload total) true,
        VerifierDecoding.CompareMachine.word total] ∧ r.steps=rawBudget payload total := by
  obtain ⟨r,hr,hf,hs⟩ := (whole_trace payload total).run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def machine := Rewind.machine raw
def budget (payload total : Nat) := 4*payload.bits.length+6*total+16

theorem measure_ready (payload total : Nat) :
    ClockJoin.ReadyRun machine (budget payload total) ![request payload total,[],[],[]]
      ![request payload total,List.replicate (mass payload total) true,
        VerifierDecoding.CompareMachine.word total,List.replicate (rawBudget payload total) false] := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run payload total
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw (rawBudget payload total)
    ![request payload total,[],[]] base hbase 0
  have he : 2*base.steps+2=budget payload total := by rw [hbs]; simp [rawBudget,budget]; omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,by omega⟩
  · convert hr using 2 <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt] using ht 0
    · simpa [hbt] using ht 1
    · simpa [hbt] using ht 2
    · simpa [hbs] using hcounter

theorem capacity_eq (payload total : Nat) :
    1073741824*(mass payload total+1)^2=RecoveryPrefix.workspace payload total := by
  simp [mass,RecoveryPrefix.workspace,Nat.add_assoc]

end NearCubicWires.RepairSource.RecoveryPrefixMeasure
