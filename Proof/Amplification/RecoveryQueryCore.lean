import Proof.Amplification.RecoveryQueryPrefix

/-! Whole nine-node ordinary query-spine execution.  This prepared parent
retains the three source fields and controller allocation tapes; the enclosing
kernel supplies its physical erase, literal prints and preserved-field copies. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem core_run (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (hcap : capacity payload committed count ≤ cap) :
    ∃ out : Fin 357→List Bool,
      ClockJoin.ReadyRun machine (9*cap) (prepared cap flat payload committed count original) out ∧
      out (bank 8 26)=ZeroPadding.pad cap (frame (code flat payload committed count).bits) ∧
      (∀ i : Fin 357,i.val<5 → out i=original i) ∧ Bounded cap out := by
  obtain ⟨outs,hprefix,hfields,hbounded⟩ := prefix_run cap flat payload committed count original hcap 8 (by decide)
  obtain ⟨hbudget,hleft,hright⟩ := cell_capacity flat payload committed count 8
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc : 1 ≤ cap := by unfold capacity at hcap; omega
  obtain ⟨last,hr,hfield,hout⟩ := cell_run 8 cap (lefts flat payload committed count 8)
    (rights flat payload committed count 8) (stage cap flat payload committed count original outs 8)
    (cell_input cap flat payload committed count original outs 8 hc hfields)
    (hbudget.trans hcap) (hleft.trans hcap) (hright.trans hcap)
  have whole := finish_path hprefix hr
  have htime : 8*cap+RecoveryQueryCell.budget (operations 8) (lefts flat payload committed count 8)
      (rights flat payload committed count 8)+1 ≤ 9*cap := by
    have hb := hbudget.trans hcap
    omega
  refine ⟨_,ClockJoin.enlarge _ _ _ _ _ whole htime,?_,?_,install_bounded 8 cap _ _ hbounded hout⟩
  · have hv : RecoveryQueryCell.result (operations 8) (lefts flat payload committed count 8)
        (rights flat payload committed count 8)=code flat payload committed count :=
      (node_result flat payload committed count 8).trans (exact_code flat payload committed count)
    rw [hv] at hfield
    exact (install_slot _ (cell_injective 8) _ _ 26).trans hfield
  · intro i hi
    rw [install_small 8 _ _ i hi]
    exact stage_small cap flat payload committed count original outs 8 i hi

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
