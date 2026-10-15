import Proof.Amplification.RecoveryPrefixTail

/-! Full sentinel-field advancement, including its complete forward scan
and a paid physical reset of every local head. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixTail
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem advance_trace (pre xs : List Bool) (answer : Bool) :
    Timed raw (2*xs.length+13)
      (cfg 0 (pre++frame (xs++[false,true])) pre.length answer)
      (cfg 11 (pre++frame (xs++[!answer,false,true])) (pre.length+2*xs.length+6) answer) := by
  induction xs generalizing pre with
  | nil => simpa using tail_trace pre answer
  | cons b xs ih =>
    have tail := ih (pre++[true,b])
    have ht : Timed raw (2*xs.length+13)
        (cfg 0 ((pre++[true,b])++frame (xs++[false,true])) (pre.length+2) answer)
        (cfg 11 (pre++frame ((b::xs)++[!answer,false,true]))
          (pre.length+2*(b::xs).length+6) answer) := by
      simpa [frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using tail
    have h := Timed.step (by rfl) (marker_step pre (xs++[false,true]) b answer)
      (Timed.step (by rfl) (payload_step pre (xs++[false,true]) b answer) ht)
    convert h using 1 <;> simp [Nat.mul_add,Nat.add_assoc]

noncomputable def machine := Rewind.machine raw

theorem advance_ready (xs : List Bool) (answer : Bool) (capacity : Nat) :
    ClockJoin.ReadyRun machine (4*xs.length+28)
      ![frame (xs++[false,true]),[answer],List.replicate capacity false]
      ![frame (xs++[!answer,false,true]),[answer],
        List.replicate (max capacity (2*xs.length+13)) false] := by
  obtain ⟨base,hr,hf,hs⟩ := (advance_trace [] xs answer).run (by rfl)
  have hin : cfg 0 ([]++frame (xs++[false,true])) 0 answer=
      initialConfiguration raw ![frame (xs++[false,true]),[answer]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  simp only [List.length_nil] at hr
  rw [hin] at hr
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hr capacity
  have he : 2*base.steps+2=4*xs.length+28 := by rw [hs]; omega
  rw [he] at hrun hsteps
  refine ⟨r,?_,?_,hh,hsteps.le⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hf,cfg] using ht 0
    · simpa [hf,cfg] using ht 1
    · simpa [hs] using hc

end NearCubicWires.RepairOrdinary.RecoveryPrefixTail
