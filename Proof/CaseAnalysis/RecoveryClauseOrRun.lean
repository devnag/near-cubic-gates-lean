import Proof.CaseAnalysis.RecoveryClauseOrState

/-! Complete paid original OR node, returning the reusable clause bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
open LocalBitMultitape RepairRepresentation RecoveryRootRound RecoveryBoundedClauseState
open RecoveryBoundedLiteralDock (slots slots_injective)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem node_run (H : Fin 71→ℕ) (A : Fin 71→List Bool) (node left right W C L : ℕ)
    (out pre source refs : List Bool) (h : State H A node left right C L out pre source refs)
    (hn : node ≤ W) (hl : left ≤ W) (hr : right ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let result:=graph left right out
    ∃ r,runFrom machine (literalBudget W C) ⟨machine.start,H,A⟩=some r ∧
      r.steps ≤ literalBudget W C ∧ r.final.heads=heads H result ∧ r.final.tapes=data A node C result ∧
      State r.final.heads r.final.tapes (node+1) node right C L result pre source refs := by
  let result:=graph left right out
  have hnC : node+1 ≤ C := by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedLiteralNode.node_run 3 (fun j=>H (slots j)) (fun j=>A (slots j))
    left right node W C out h.gateH h.gateA h.restoreH h.restoreA hl hr hC hnC
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective (RecoveryBoundedLiteralNode.machine 3)
    _ H A _ (by intro j;rfl) (by intro j;rfl) p pr
  have rH : r.final.heads=heads H result := by
    funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      exact (projected_heads H result j).symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h20 : i≠20:=fun he=>hi ⟨20,he.symm⟩
      simp only [heads,Function.update_of_ne h20]
  have rA : r.final.tapes=data A node C result := by
    have he : install slots A (RecoveryBoundedLiteralNode.output (fun j=>A (slots j)) 3 node C result)=r.final.tapes := by
      apply HierarchyWidth.install_eq slots slots_injective
      · intro j;rw [rt j,pt];rfl
      · intro i hi;exact (rkeep i hi).2
    exact he.symm.trans (node_data A node C result)
  have hb : RecoveryBoundedLiteralNode.budget 3 left right node C ≤ literalBudget W C := by
    have hg:=RecoveryBoundedLiteralNode.budget_bound 3 left right node W C hl hr hC
    unfold literalBudget
    omega
  have more:=runFrom_moreFuel machine _ (literalBudget W C-RecoveryBoundedLiteralNode.budget 3 left right node C) _ r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans (ps.trans hb),rH,rA,?_⟩
  rw [rH,rA]
  exact node_state H A node left right C L out pre source refs result h

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseOr
