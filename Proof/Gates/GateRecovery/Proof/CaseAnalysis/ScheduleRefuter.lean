import Proof.Gates.GateRecovery.Bundle
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleOrdinary
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.ScheduleBounds

namespace GR

/-! The actual ordinary schedule feeds the same selected source refuter.
The existing compositor pays both word handoffs and resets. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Refuter
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem compose_bound (a d b e n N : Nat) (hN : N ≤ 2^n) :
    16*(a*(2^n+1)^d+b*(N+2)^e+1) ≤
      16*(a+b*2^e+1)*(2^n+1)^(d+e+1) := by
  let x : Nat := 2^n+1
  let P := x^(d+e+1)
  have hx : 1 ≤ x := Nat.succ_pos _
  have hP : 1 ≤ P := Nat.one_le_pow _ _ hx
  have hd : x^d ≤ P := Nat.pow_le_pow_right hx (by omega)
  have he : (N+2)^e ≤ 2^e*P := by
    calc
      _ ≤ (2*x)^e := Nat.pow_le_pow_left (by dsimp [x]; omega) _
      _ = 2^e*x^e := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by omega))
  have ha := Nat.mul_le_mul_left a hd
  have hb := Nat.mul_le_mul_left b he
  change 16*(a*x^d+b*(N+2)^e+1) ≤ 16*(a+b*2^e+1)*P
  nlinarith

theorem selected_runs (sources : GateEightSources) (k D copies ext : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (hD : 1 ≤ D) (hcopies : 1 ≤ copies)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n => n^(k+2))) :
    ∃ C E onset : Nat, ∃ p : OrdinaryOracleProgram,
      ∀ bits : List Bool, onset ≤ bits.length →
        let N := Framed.selectedLength (CloseoutLanguage.widthAt sources k clock copies ext D) bits.length
        OrdinaryOracleRuns RecoveryOracle.correctedSat p bits
          (List.ofFn ((sources.hierarchy (fun n => n^(k+2)) clock).output M N))
          (C*(2^bits.length+1)^E) ∧
        (M.accepts N ((sources.hierarchy (fun n => n^(k+2)) clock).output M N) ↔
          (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.timedView.accepts N
            ((sources.hierarchy (fun n => n^(k+2)) clock).output M N) = false) := by
  obtain ⟨a,d,schedule,hschedule⟩ := Ordinary.exists_program sources k D copies ext clock hD
  obtain ⟨b,e,start,refuter,_hb,_he,hrefuter⟩ := RecoveryRefuterReplay.polynomial_runs
    (sources.hierarchy (fun n => n^(k+2)) clock) clock M hM
  obtain ⟨onset,honset⟩ := CloseoutLanguage.schedule_onset sources k clock copies ext D
    (max 1 start) hcopies (Nat.le_max_left _ _)
  refine ⟨16*(a+b*2^e+1),d+e+1,onset,OrdinaryOracleCompose.compose schedule refuter,?_⟩
  intro bits hbits
  let width := CloseoutLanguage.widthAt sources k clock copies ext D
  let s := CloseoutLanguage.selectedIndex width bits.length
  let N := Framed.selectedLength width bits.length
  obtain ⟨hs,_,_⟩ := honset bits.length hbits
  have hpos : 1 ≤ s := (Nat.le_max_left _ _).trans hs
  have hstart : start ≤ N := by
    have hzero : s ≠ 0 := by omega
    have hpow : s < 2^s := Nat.lt_two_pow_self
    have hstart := (Nat.le_max_right 1 start).trans hs
    dsimp only [N,Framed.selectedLength]
    rw [if_neg hzero]
    change start ≤ 2^s
    exact hstart.trans hpow.le
  obtain ⟨hr,hconflict⟩ := hrefuter N hstart
  exact ⟨(OrdinaryOracleCompose.compose_runs (hschedule bits) hr).enlarge
      (compose_bound a d b e bits.length N (Framed.selectedLength_bound width bits.length)),hconflict⟩

end
end NearCubicWires.RepairSource.CloseoutSchedule.Refuter

end GR
