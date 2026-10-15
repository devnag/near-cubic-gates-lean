import Proof.PCP.PCPPNativeQueryAdvance
import Proof.PCP.PCPPNativeClauseBody

/-! Advance the actual clause-loop counters by executing the existing unary
overwrite caller three times. The last temporary is explicitly returned for
the enclosing paid erase; no next-counter tape is supplied. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseCounter
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mainSlots : Fin 3→Fin 4 := ![0,1,3]
def lastSlots : Fin 3→Fin 4 := ![0,2,3]
noncomputable def first := RecoveryFocus.machine mainSlots PCPPNativeQueryAdvance.machine
noncomputable def last := RecoveryFocus.machine lastSlots PCPPNativeQueryAdvance.machine
noncomputable def machine := Composition.machine (Composition.machine first first) last
def data (base accumulator temporary F : ℕ) : Fin 4→List Bool :=
  ![List.replicate base true,List.replicate accumulator true,
    List.replicate temporary true,List.replicate F false]

theorem main_run (base accumulator F : ℕ) (ha : accumulator≤base) (hF : base+1≤F) :
    ReadyRun first (2*base+4) (data base accumulator 0 F) (data (base+1) (base+1) 0 F) := by
  have h := (PCPPNativeQueryAdvance.advance_ready base accumulator F ha hF).focus
    mainSlots (by decide) (data base accumulator 0 F) (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq mainSlots (by decide) _ (data (base+1) (base+1) 0 F) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h0:=hi 0; have h1:=hi 1; have h3:=hi 2;
        fin_cases i <;> simp_all [mainSlots,data])] at h
  exact h

theorem last_run (base accumulator F : ℕ) (hF : base+1≤F) :
    ReadyRun last (2*base+4) (data base accumulator 0 F) (data (base+1) accumulator (base+1) F) := by
  have h := (PCPPNativeQueryAdvance.advance_ready base 0 F (Nat.zero_le _) hF).focus
    lastSlots (by decide) (data base accumulator 0 F) (by intro j; fin_cases j <;> rfl)
  rw [HierarchyWidth.install_eq lastSlots (by decide) _ (data (base+1) accumulator (base+1) F) _
    (by intro j; fin_cases j <;> rfl)
    (by intro i hi; have h0:=hi 0; have h2:=hi 1; have h3:=hi 2;
        fin_cases i <;> simp_all [lastSlots,data])] at h
  exact h

private theorem bounded {t s b : ℕ} {m : Machine t s} {a z : Fin t→List Bool}
    (h : ReadyRun m b a z) : ClockJoin.ReadyRun m b a z := by
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem counter_run (base accumulator F : ℕ) (ha : accumulator≤base) (hF : base+3≤F) :
    ClockJoin.ReadyRun machine (6*base+20) (data base accumulator 0 F)
      (data (base+3) (base+2) (base+3) F) := by
  have a:=bounded (main_run base accumulator F ha (by omega))
  have b:=bounded (main_run (base+1) (base+1) F (by omega) (by omega))
  have c:=bounded (last_run (base+2) (base+2) F (by omega))
  have h:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ a b) c
  have ht : (2*base+4)+1+(2*(base+1)+4)+1+(2*(base+2)+4)=6*base+20 := by omega
  rw [ht] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPPNativeClauseCounter
