import Proof.CaseAnalysis.ScheduleLoopDriver

/-! The literal finite schedule, using the checked ordinary iteration and
the existing repeat controller. Only actual indices 1,...,n are executed. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Loop
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def best (width : Nat → Nat) (n : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => if width (j+1) ≤ n/2 then 2^(j+1) else best width n j

theorem best_bound (width : Nat → Nat) (n j : Nat) : best width n j ≤ 2^j := by
  induction j with
  | zero => simp [best]
  | succ j ih =>
    dsimp only [best]
    split_ifs
    · exact le_rfl
    · exact ih.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem best_meaning (width : Nat → Nat) (n j : Nat) :
    best width n j =
      if Nat.findGreatest (fun s => 1 ≤ s ∧ width s ≤ n/2) j = 0 then 0
      else 2^(Nat.findGreatest (fun s => 1 ≤ s ∧ width s ≤ n/2) j) := by
  induction j with
  | zero => simp [best]
  | succ j ih =>
    rw [best,Nat.findGreatest_succ]
    by_cases h : width (j+1) ≤ n/2
    · simp [h]
    · simpa only [h,not_false_eq_true,↓reduceIte,and_false] using ih

theorem best_selected (width : Nat → Nat) (n : Nat) :
    best width n n = if CloseoutLanguage.selectedIndex width n = 0 then 0
      else 2^(CloseoutLanguage.selectedIndex width n) := best_meaning width n n

def input (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (C n j : Nat) :=
  Step.bank sources k D C (j+1) n (best (CloseoutLanguage.widthAt sources k clock copies D) n j)

def machine (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) :=
  RepeatMachine.machine (Step.machine sources k D copies clock) (fun _ _ => true)

theorem step_budget (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (C s n : Nat)
    (hs : s ≤ C) (hn : n ≤ C) (hN : 2^s ≤ C)
    (hcost : Test.budget sources k D copies clock s n ≤ C) :
    Step.budget sources k D copies clock C s n ≤ 16*C+64 := by
  unfold Step.budget Step.prefixBudget Step.suffixBudget
  omega

theorem loop_run (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (C n : Nat) (hD : 1 ≤ D)
    (hn : n+3 ≤ C) (hN : 2^n+3 ≤ C)
    (hcost : ∀ s, s ≤ n → Test.budget sources k D copies clock s n+1 ≤ C) :
    ∃ r, runFrom (machine sources k D copies clock) (n*(16*C+67)+3)
      (RepeatMachine.cfg 0
        (initialConfiguration (Step.machine sources k D copies clock) (input sources k D copies clock C n 0)) n 1) = some r ∧
      r.steps ≤ n*(16*C+67)+3 ∧
      r.final = RepeatMachine.cfg 3
        (initialConfiguration (Step.machine sources k D copies clock) (input sources k D copies clock C n n)) n 1 := by
  have supplier (j : Nat) (hj : j < n) :
      ClockJoin.ReadyRun (Step.machine sources k D copies clock) (16*C+64)
        (input sources k D copies clock C n j) (input sources k D copies clock C n (j+1)) := by
    have hs : j+1 ≤ n := by omega
    have hp : 2^(j+1) ≤ 2^n := Nat.pow_le_pow_right (by decide) hs
    have hb := (best_bound (CloseoutLanguage.widthAt sources k clock copies D) n j).trans
      (Nat.pow_le_pow_right (by decide) (show j ≤ n by omega))
    have hstep := Step.step_run sources k D copies clock C (j+1) n
      (best (CloseoutLanguage.widthAt sources k clock copies D) n j)
      hD (by omega) (by omega) (by omega) (by omega) (hcost (j+1) hs)
    have hbudget := step_budget sources k D copies clock C (j+1) n
      (by omega) (by omega) (by omega) (by have := hcost (j+1) hs; omega)
    simpa only [input,best,Step.nextBest] using ClockJoin.enlarge _ _ _ _ _ hstep hbudget
  have hr := LoopDriver.run (Step.machine sources k D copies clock)
    (input sources k D copies clock C n) n (16*C+64) supplier n 0 (by omega)
  have he : n*(16*C+64+2)+n+3 = n*(16*C+67)+3 := by ring
  simpa only [Nat.zero_add,he,machine] using hr

end
end NearCubicWires.RepairSource.CloseoutSchedule.Loop
