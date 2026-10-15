import Proof.Amplification.RecoveryTseitinPrefix

/-! Whole six-node ordinary query-spine execution.  This prepared parent
retains the three source fields and controller allocation tapes; the enclosing
kernel supplies its physical erase, literal prints and preserved-field copies. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem core_run (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (hcap : capacity ls ≤ cap) :
    ∃ out : Fin 239→List Bool,
      ClockJoin.ReadyRun machine (6*cap) (prepared cap ls original) out ∧
      out (bank 5 26)=ZeroPadding.pad cap (frame (Encodable.encode (clause ls)).bits) ∧
      (∀ i : Fin 239,i.val<5 → out i=original i) ∧ Bounded cap out := by
  obtain ⟨outs,hprefix,hfields,hbounded⟩ := prefix_run cap ls original hcap 5 (by decide)
  obtain ⟨hbudget,hleft,hright⟩ := cell_capacity ls 5
  have hc : 1 ≤ cap := by unfold capacity at hcap; omega
  obtain ⟨last,hr,hfield,hout⟩ := cell_run 5 cap (lefts ls 5)
    (rights ls 5) (stage cap ls original outs 5)
    (cell_input cap ls original outs 5 hc hfields)
    (hbudget.trans hcap) (hleft.trans hcap) (hright.trans hcap)
  have whole := finish_path hprefix hr
  have htime : 5*cap+RecoveryQueryCell.budget (operations 5) (lefts ls 5)
      (rights ls 5)+1 ≤ 6*cap := by
    have hb := hbudget.trans hcap
    omega
  refine ⟨_,ClockJoin.enlarge _ _ _ _ _ whole htime,?_,?_,install_bounded 5 cap _ _ hbounded hout⟩
  · have hv : RecoveryQueryCell.result (operations 5) (lefts ls 5)
        (rights ls 5)=Encodable.encode (clause ls) :=
      (node_result ls 5).trans (exact_code ls)
    rw [hv] at hfield
    exact (install_slot _ (cell_injective 5) _ _ 26).trans hfield
  · intro i hi
    rw [install_small 5 _ _ i hi]
    exact stage_small cap ls original outs 5 i hi

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
