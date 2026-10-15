import Proof.PCP.PCPPairPrep

/-! One whole ordinary pair call from two framed operands and blank scratch.
No supplied width, normalized operand, comparison flag or arithmetic result. -/
namespace NearCubicWires.RepairOrdinary.PCPPairCold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (left right : List Bool) : ℕ :=
  PCPPair.budget left right+10*PCPPair.width left right+13

theorem pair_run (left right : List Bool) :
    ∃ out : Fin 35 → List Bool,
      ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      out 26=frame (binary (PCPPair.width left right) (Nat.pair (value left) (value right))) := by
  obtain ⟨out,hpair,hout⟩ := PCPPair.pair_run left right
  have hp := CompetitorRationalProducts.bounded_focus pairSlots pair_injective
    _ _ _ hpair (prepared left right) (prepared_pair left right)
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ (prepare_run left right) hp
  refine ⟨install pairSlots (prepared left right) out,?_,?_⟩
  · convert hwhole using 1
    · rfl
    · unfold budget
      omega
  · exact (install_slot pairSlots pair_injective _ _ 26).trans hout

theorem budget_quadratic (left right : List Bool) :
    budget left right ≤ 1024*(left.length+right.length+1)^2 := by
  unfold budget PCPPair.budget PCPPair.width
  have h : 1 ≤ left.length+right.length+1 := by omega
  nlinarith [sq_nonneg (left.length+right.length : ℤ)]

end NearCubicWires.RepairOrdinary.PCPPairCold
