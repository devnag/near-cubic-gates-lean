import Proof.Amplification.RecoveryQueryState

/-! Execute the first k actual query nodes, retaining the produced fields
needed by the remaining finite graph. Every call return is included. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_run (cap : Nat) (flat : Bool) (payload committed count : Nat)
    (original : Fin 357→List Bool) (hcap : capacity payload committed count ≤ cap)
    (n : Nat) (hn : n<9) :
    ∃ outs : Fin 9→Fin 39→List Bool,
      Path 0 ⟨n,hn⟩ (n*cap) (prepared cap flat payload committed count original)
        (stage cap flat payload committed count original outs n) ∧
      Fields cap flat payload committed count n outs ∧
      Bounded cap (stage cap flat payload committed count original outs n) := by
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc : 1 ≤ cap := by unfold capacity at hcap; omega
  induction n with
  | zero =>
    refine ⟨fun _ _=>[],?_,?_,?_⟩
    · have he : (⟨0,hn⟩ : Fin 9)=0 := Fin.ext rfl
      rw [he,Nat.zero_mul]
      exact Path.refl _ _
    · intro j hj
      omega
    · exact prepared_bounded cap flat payload committed count original hcap
  | succ n ih =>
    obtain ⟨outs,hpath,hfields,hbounded⟩ := ih (by omega)
    let k : Fin 9 := ⟨n,by omega⟩
    obtain ⟨hbudget,hleft,hright⟩ := cell_capacity flat payload committed count k
    obtain ⟨out,hr,hfield,hout⟩ := cell_run k cap (lefts flat payload committed count k)
      (rights flat payload committed count k) (stage cap flat payload committed count original outs n)
      (cell_input cap flat payload committed count original outs k hc hfields)
      (hbudget.trans hcap) (hleft.trans hcap) (hright.trans hcap)
    rw [node_result] at hfield
    have hnext : ∀ q scanned,next k q scanned=some ⟨n+1,hn⟩ := by
      intro q scanned
      simp [next,k,show n≠8 by omega,Nat.mod_eq_of_lt hn]
    have hcall := ready_path k ⟨n+1,hn⟩ _ _ _ hr hnext
    have htotal := (hpath.trans hcall).enlarge (show n*cap+
        (RecoveryQueryCell.budget (operations k) (lefts flat payload committed count k)
          (rights flat payload committed count k)+1) ≤ (n+1)*cap by
      have hb := hbudget.trans hcap
      rw [Nat.add_mul,Nat.one_mul]
      omega)
    refine ⟨Function.update outs k out,?_,fields_update cap flat payload committed count outs k out hfields hfield,?_⟩
    · change Path 0 ⟨n+1,hn⟩ ((n+1)*cap) _
        (stage cap flat payload committed count original (Function.update outs k out) (k.val+1))
      rw [update_successor]
      exact htotal
    · change Bounded cap (stage cap flat payload committed count original (Function.update outs k out) (k.val+1))
      rw [update_successor]
      exact install_bounded k cap _ _ hbounded hout

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel
