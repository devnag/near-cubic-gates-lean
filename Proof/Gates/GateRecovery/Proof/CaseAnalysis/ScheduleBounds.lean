import Proof.Gates.GateRecovery.Bundle
import Proof.CaseAnalysis.NativeWidthStep
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.Language

namespace GR

/-! Actual fixed-copy core widths and the finite largest-index schedule.
All constants are fixed before the final language input length. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem clause_step (degree q q' jump : Nat) (h : q' ≤ q+jump) :
    clauseWidth degree q' ≤ clauseWidth degree q+degree*natBitLength (jump+1) := by
  apply Nat.clog_le_of_le_pow
  calc
    (q'+2)^degree ≤ ((jump+1)*(q+2))^degree := Nat.pow_le_pow_left (by nlinarith) _
    _ ≤ (2^natBitLength (jump+1)*(q+2))^degree := by
      gcongr
      exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (jump+1)).le
    _ = 2^(natBitLength (jump+1)*degree)*(q+2)^degree := by rw [mul_pow,pow_mul]
    _ ≤ 2^(natBitLength (jump+1)*degree)*2^clauseWidth degree q :=
      Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
    _ = _ := by rw [←pow_add]; congr 1; ring

theorem clause_linear (degree q : Nat) : clauseWidth degree q ≤ degree*(q+1) := by
  have h : q+2 ≤ 2^(q+1) := Nat.succ_le_of_lt (Nat.lt_two_pow_self : q+1 < 2^(q+1))
  apply Nat.clog_le_of_le_pow
  have hp:=Nat.pow_le_pow_left h degree
  simpa only [←pow_mul,Nat.mul_comm] using hp

theorem core_step (copies ext degree q q' jump : Nat) (h : q' ≤ q+jump) :
    coreWidth copies ext degree q' ≤ coreWidth copies ext degree q+
      copies*(jump+degree*natBitLength (jump+1)) := by
  have hc:=clause_step degree q q' jump h
  unfold coreWidth
  nlinarith

theorem core_lower (copies ext degree q : Nat) (hc : 1 ≤ copies) : q ≤ coreWidth copies ext degree q := by
  have hm:=Nat.mul_le_mul_right (q+clauseWidth degree q+(ext+1)) hc
  unfold coreWidth
  omega

theorem core_upper (copies ext degree q : Nat) (hq : 1 ≤ q) :
    coreWidth copies ext degree q ≤ copies*(2*degree+ext+2)*q := by
  have hr:=clause_linear degree q
  have h : q+clauseWidth degree q+(ext+1) ≤ (2*degree+ext+2)*q := by nlinarith
  exact (Nat.mul_le_mul_left copies h).trans_eq (by ring)

def widthJump (sources : GateEightSources) (_k copies degree : Nat) :=
  let j:=sources.width.jump
  copies*(j+degree*natBitLength (j+1))

theorem widthAt_lower (sources : GateEightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (copies ext degree s : Nat) (hc : 1 ≤ copies) :
    s+1 ≤ widthAt sources k clock copies ext degree s :=
  (sources.width.lower s).trans (core_lower copies ext degree _ hc)

theorem widthAt_step (sources : GateEightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (copies ext degree s : Nat) :
    widthAt sources k clock copies ext degree (s+1) ≤ widthAt sources k clock copies ext degree s+
      widthJump sources k copies degree :=
  core_step copies ext degree _ _ _ (sources.width.step s)

theorem selected_ge (width : Nat→Nat) (s n : Nat) (hs : 1 ≤ s) (hn : 2*width s+s ≤ n) :
    s ≤ selectedIndex width n :=
  Nat.le_findGreatest (by omega) ⟨hs,by omega⟩

theorem selected_lt (width : Nat→Nat) (lower : ∀ s, s+1 ≤ width s) (n : Nat) (hn : 1 ≤ n) :
    selectedIndex width n < n := by
  have hs:=selectedIndex_le width n
  by_contra h
  have he : selectedIndex width n=n := by omega
  have hf:=selectedIndex_fits width n (by omega)
  have hl:=lower (selectedIndex width n)
  omega

theorem selected_fraction (width : Nat→Nat) (jump : Nat)
    (lower : ∀ s, s+1 ≤ width s) (step : ∀ s, width (s+1) ≤ width s+jump)
    (n : Nat) (hn : 6*jump+6 ≤ n) (hs : selectedIndex width n ≠ 0) :
    n/3 ≤ width (selectedIndex width n) ∧ width (selectedIndex width n) ≤ n/2 := by
  have hf:=selectedIndex_fits width n hs
  have hlt:=selected_lt width lower n (by omega)
  have hnext:=Nat.findGreatest_is_greatest
    (P:=fun s=>1 ≤ s ∧ width s ≤ n/2) (n:=n) (k:=selectedIndex width n+1)
    (Nat.lt_succ_self _) (by omega)
  have hcross : n/2 < width (selectedIndex width n+1) := by
    by_contra h
    exact hnext ⟨by omega,by omega⟩
  have hj:=step (selectedIndex width n)
  exact ⟨by omega,hf.2⟩

theorem schedule_onset (sources : GateEightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (copies ext degree s0 : Nat)
    (hc : 1 ≤ copies) (hs0 : 1 ≤ s0) :
    ∃ onset, ∀ n, onset ≤ n →
      let width:=widthAt sources k clock copies ext degree
      let s:=selectedIndex width n
      s0 ≤ s ∧ n/3 ≤ width s ∧ width s ≤ n/2 := by
  let width:=widthAt sources k clock copies ext degree
  refine ⟨max (2*width s0+s0) (6*widthJump sources k copies degree+6),?_⟩
  intro n hn
  have hs:=selected_ge width s0 n hs0 ((Nat.le_max_left _ _).trans hn)
  have hf:=selected_fraction width (widthJump sources k copies degree)
    (fun s=>widthAt_lower sources k clock copies ext degree s hc)
    (widthAt_step sources k clock copies ext degree) n ((Nat.le_max_right _ _).trans hn) (by omega)
  exact ⟨hs,hf⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage

end GR
