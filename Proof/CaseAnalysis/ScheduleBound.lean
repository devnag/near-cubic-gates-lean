import Proof.CaseAnalysis.ScheduleRun

/-! One fixed all-length cold schedule with a paper C.12 resource bound.
Every capacity cell, metadata write, sweep and candidate run is included. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def coefficient (A B : Nat) := CloseoutCapacity.coefficient A B+18*2^B+120

theorem budget_bound (A B : Nat) (bits : List Bool) :
    budget A B bits ≤ coefficient A B*(2^bits.length+1)^(A+1) := by
  let n := bits.length
  let x : Nat := 2^n+1
  let P := x^(A+1)
  let C := CloseoutCapacity.capacity A B n
  have hx : 1 ≤ x := Nat.succ_pos _
  have hxP : x ≤ P := Nat.le_self_pow (by omega) _
  have hP : 1 ≤ P := hx.trans hxP
  have hn : n ≤ x := by have := Nat.lt_two_pow_self (n := n); dsimp [x]; omega
  have hC : C ≤ 2^B*x^A := by
    have he : C = 2^B*(2^n)^A := by
      dsimp only [C,CloseoutCapacity.capacity]
      rw [pow_add,Nat.mul_comm A n,pow_mul]
      ring
    rw [he]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [x]; omega) _)
  have hnC : n*C ≤ 2^B*P := by
    calc
      _ ≤ x*(2^B*x^A) := Nat.mul_le_mul hn hC
      _ = _ := by dsimp [P]; rw [pow_succ]; ring
  have hCP : C ≤ 2^B*P := hC.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have hcap := CloseoutCapacity.budget_bound A B bits
  change CloseoutCapacity.budget A B bits ≤ CloseoutCapacity.coefficient A B*P at hcap
  change budget A B bits ≤ coefficient A B*P
  unfold budget prepareBudget coefficient
  change CloseoutCapacity.budget A B bits+1+(8*n+30)+1+(2*C+4)+1+(n*(16*C+67)+7) ≤ _
  nlinarith

theorem exists_schedule (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) :
    ∃ A B : Nat, ∀ bits : List Bool, ∃ out,
      ClockJoin.ReadyRun (machine sources k D copies clock A B)
        (coefficient A B*(2^bits.length+1)^(A+1))
        (input (Step.workTapes sources k D) bits) out ∧
      out (extra (Step.workTapes sources k D) 0) = frame bits ∧
      out (port (Step.workTapes sources k D) 2) =
        ZeroPadding.pad (CloseoutCapacity.capacity A B bits.length)
          (List.replicate
            (if CloseoutLanguage.selectedIndex (CloseoutLanguage.widthAt sources k clock copies D) bits.length = 0
             then 0 else 2^(CloseoutLanguage.selectedIndex (CloseoutLanguage.widthAt sources k clock copies D) bits.length)) true) := by
  obtain ⟨A,B,hcapacity⟩ := schedule_capacity sources k D copies clock hD
  refine ⟨A,B,?_⟩
  intro bits
  obtain ⟨hn,hN,hcost⟩ := hcapacity bits.length
  obtain ⟨out,hr,hx,hs⟩ := schedule_run sources k D copies clock A B bits hD hn hN hcost
  rw [Loop.best_selected] at hs
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (budget_bound A B bits),hx,hs⟩

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
