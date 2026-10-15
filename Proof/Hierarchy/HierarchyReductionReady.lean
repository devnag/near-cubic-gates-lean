import Proof.Hierarchy.HierarchyReductionTime

/-! The actual padded-word execution is available directly at the proved
quasilinear fuel, with no cost-realization premise for a later consumer. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ordinaryBudget (k C Cpad : ℕ) (code x : List Bool) :=
  runtimeCoefficient k C Cpad code*(x.length+1)*PCPResourceLedger.q x.length^2

theorem ordinary_run (k C Cpad : ℕ) (code x : List Bool) (hpad : k+3≤Cpad) :
    ∃ r,run (machine k C Cpad code) (ordinaryBudget k C Cpad code x) (input k x)=some r ∧
      r.final.tapes (extra k 13)=HierarchyPadding.rawInput k C Cpad code x ∧
      r.final.tapes (xTape k)=frame x ∧ (∀ i,r.final.heads i=0) ∧
      r.steps ≤ ordinaryBudget k C Cpad code x := by
  obtain ⟨r,hr,ho,hx,hh,hs⟩ := reduction_run k C Cpad code x hpad
  have hb : budget k C Cpad code x≤ordinaryBudget k C Cpad code x := budget_bound k C Cpad code x
  have hm := run_moreFuel (machine k C Cpad code) (budget k C Cpad code x)
    (ordinaryBudget k C Cpad code x-budget k C Cpad code x) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,ho,hx,hh,hs.trans hb⟩

end NearCubicWires.RepairOrdinary.HierarchyReduction
