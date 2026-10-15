import Proof.Amplification.RecoveryCap

/-! Complete linear-cap producer, including its cold entry and paid rewind
of all heads. Its source is the already produced width word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def startMid (n : Nat) : Configuration 2 6 := ⟨1,![1,1],![word (n+1),word 0]⟩

theorem entry_trace (n : Nat) : Timed raw 2
    (initialConfiguration raw ![word (n+1),[]]) (cfg n 0) := by
  have h0 : step raw (initialConfiguration raw ![word (n+1),[]])=some (startMid n) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  have h1 : step raw (startMid n)=some (cfg n 0) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)

theorem raw_run (n : Nat) :
    ∃ r,run raw (3*n+3) ![word (n+1),[]]=some r ∧
      r.final.tapes=![word (n+1),word (3*n)] ∧ r.steps=3*n+3 := by
  have h := (entry_trace n).trans (loop_trace n 0 n (by omega))
  have he : 2+(3*n+1)=3*n+3 := by omega
  rw [he] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by rfl)
  exact ⟨r,hr,by rw [hf]; rfl,hs⟩

def machine := Rewind.machine raw

theorem cap_ready (n : Nat) : ReadyRun machine (6*n+8) ![word (n+1),[],[]]
    ![word (n+1),word (3*n),List.replicate (3*n+3) false] := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run n
  obtain ⟨r,hr,ht,hcounter,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw (3*n+3)
    ![word (n+1),[]] base hbase 0
  have he : 2*base.steps+2=6*n+8 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,hh,hs.trans he⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · simpa [hbt] using ht 0
    · simpa [hbt] using ht 1
    · simpa [hbs] using hcounter

end NearCubicWires.RepairOrdinary.RecoveryColdCap
