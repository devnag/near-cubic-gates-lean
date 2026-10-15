import Proof.CaseAnalysis.ScheduleGuardedRun

/-! One complete all-length recovery schedule returns the retained address,
the exact semantic finite-branch flag and the actual ordinary refuter request.
All fixed-onset printing and framing are included in the C.12 bound. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Guarded
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def coefficient (A B onset : Nat):=Cold.coefficient A B+6*onset+41

theorem budget_bound (A B onset n N : Nat) (hN : N≤2^n) :
    Cold.coefficient A B*(2^n+1)^(A+1)+1+(6*onset+18)+1+(6*N+15)≤
      coefficient A B onset*(2^n+1)^(A+1):=by
  have hp:1≤(2^n+1)^(A+1):=Nat.one_le_pow _ _ (by omega)
  have hn:N≤(2^n+1)^(A+1):=
    (hN.trans (by omega)).trans (Nat.le_self_pow (by omega) _)
  have hc:=Nat.mul_le_mul_left (6*onset+35) hp
  unfold coefficient
  nlinarith

theorem exists_guarded (sources : EightSources) (k D copies onset : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (hD : 1≤D) (ho : 1≤onset) :
    ∃ A B : Nat,∀ bits : List Bool,∃ out,
      ClockJoin.ReadyRun (machine (Cold.machine sources k D copies clock A B) onset)
        (coefficient A B onset*(2^bits.length+1)^(A+1))
        (input (Step.workTapes sources k D) bits) out ∧
      out (old (Step.workTapes sources k D) (Cold.extra (Step.workTapes sources k D) 0))=frame bits ∧
      out (fresh (Step.workTapes sources k D) 4)=
        [decide (1≤CloseoutLanguage.selectedIndex (CloseoutLanguage.widthAt sources k clock copies D) bits.length ∧
          onset≤2^(CloseoutLanguage.selectedIndex (CloseoutLanguage.widthAt sources k clock copies D) bits.length))] ∧
      out (fresh (Step.workTapes sources k D) 8)=frame
        (List.replicate (Framed.selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length) true):=by
  obtain ⟨A,B,hrun⟩:=Cold.exists_schedule sources k D copies clock hD
  refine ⟨A,B,?_⟩
  intro bits
  let width:=CloseoutLanguage.widthAt sources k clock copies D
  let N:=Framed.selectedLength width bits.length
  obtain ⟨native,hr,hx,hN⟩:=hrun bits
  obtain ⟨out,hout,haddress,hflag,hword⟩:=continuation_run
    (Cold.machine sources k D copies clock A B) bits onset
    (CloseoutCapacity.capacity A B bits.length) N native hr hx hN
  refine ⟨out,ClockJoin.enlarge _ _ _ _ _ hout
    (budget_bound A B onset bits.length N (Framed.selectedLength_bound width bits.length)),haddress,?_,hword⟩
  rw [hflag]
  simp only [N,selected_guard width bits.length onset ho]
  rfl

end
end NearCubicWires.RepairSource.CloseoutSchedule.Guarded
