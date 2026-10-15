import Proof.Hierarchy.CompetitorSameBucketZeroPrepareSpace

/-! Exact zero-grid scalar copies on the allocated19 layout. The existing
append cursor and both physical U counters are preserved by every copy. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroCopyFields
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlot : Fin 6 → Fin 19 := ![3,3,1,2,2,2]
def targetSlot : Fin 6 → Fin 19 := ![6,7,8,9,10,11]
def slots (j : Fin 6) : Fin 4 → Fin 19 := ![sourceSlot j,targetSlot j,12,14]
theorem slots_injective (j : Fin 6) : Function.Injective (slots j) := by fin_cases j <;> decide
noncomputable def machine (j : Fin 6) := RecoveryFocus.machine (slots j) RecoveryRootRound.copyMachine
def copied (j : Fin 6) (cap : ℕ) (bits : List Bool) (ambient : Fin 19 → List Bool) :=
  Function.update ambient (targetSlot j) (ZeroPadding.pad cap (frame bits))
def cfg {s : ℕ} (q : Fin s) (heads : Fin 19 → ℕ) (tapes : Fin 19 → List Bool) : Configuration 19 s := ⟨q,heads,tapes⟩

theorem copy_run (j : Fin 6) (cap : ℕ) (bits : List Bool) (heads : Fin 19 → ℕ) (ambient : Fin 19 → List Bool)
    (hc : 4*bits.length+3≤cap) (hh : ∀ k,heads (slots j k)=0)
    (hs : ambient (sourceSlot j)=frame bits) (ht : ambient (targetSlot j)=List.replicate cap false)
    (h12 : ambient 12=List.replicate cap false) (h14 : ambient 14=List.replicate cap false) :
    ∃ actual,runFrom (machine j) (8*bits.length+8) (cfg (machine j).start heads ambient)=some actual ∧
      actual.final.heads=heads ∧ actual.final.tapes=copied j cap bits ambient ∧ actual.steps≤8*bits.length+8 := by
  obtain ⟨base,hb,bt,bh,bs⟩:=CompetitorSameBucketColdFrameCopy.copy_ready bits cap hc
  have ready : ClockJoin.ReadyRun RecoveryRootRound.copyMachine (8*bits.length+8)
      (CompetitorSameBucketColdFrameCopy.input bits cap) (CompetitorSameBucketColdFrameCopy.output bits cap) :=
    ⟨base,hb,bt,bh,bs.le⟩
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run (slots j) (slots_injective j)
    _ _ _ ready heads ambient hh (by intro k; fin_cases k; exact hs; exact ht; exact h12; exact h14)
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  funext i
  by_cases htarget : i=targetSlot j
  · subst i
    rw [copied,Function.update_self]
    exact install_slot (slots j) (slots_injective j) _ _ 1
  rw [copied,Function.update_of_ne htarget]
  by_cases hsource : i=sourceSlot j
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 0).trans hs.symm
  by_cases hc1 : i=12
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 2).trans h12.symm
  by_cases hc2 : i=14
  · subst i
    exact (install_slot (slots j) (slots_injective j) _ _ 3).trans h14.symm
  apply install_other
  intro k hk
  fin_cases k
  · exact hsource hk.symm
  · exact htarget hk.symm
  · exact hc1 hk.symm
  · exact hc2 hk.symm

theorem copied_other (j : Fin 6) (cap : ℕ) (bits : List Bool) (ambient : Fin 19 → List Bool)
    (i : Fin 19) (hi : i≠targetSlot j) : copied j cap bits ambient i=ambient i := Function.update_of_ne hi _ _

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroCopyFields
