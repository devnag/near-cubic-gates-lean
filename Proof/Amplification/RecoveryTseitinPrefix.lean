import Proof.Amplification.RecoveryTseitinState

/-! Execute the first k actual query nodes, retaining the produced fields
needed by the remaining finite graph. Every call return is included. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_run (cap : Nat) (ls : Literals)
    (original : Fin 239→List Bool) (hcap : capacity ls ≤ cap)
    (n : Nat) (hn : n<6) :
    ∃ outs : Fin 6→Fin 39→List Bool,
      Path 0 ⟨n,hn⟩ (n*cap) (prepared cap ls original)
        (stage cap ls original outs n) ∧
      Fields cap ls n outs ∧
      Bounded cap (stage cap ls original outs n) := by
  have hc : 1 ≤ cap := by unfold capacity at hcap; omega
  induction n with
  | zero =>
    refine ⟨fun _ _=>[],?_,?_,?_⟩
    · have he : (⟨0,hn⟩ : Fin 6)=0 := Fin.ext rfl
      rw [he,Nat.zero_mul]
      exact Path.refl _ _
    · intro j hj
      omega
    · exact prepared_bounded cap ls original hcap
  | succ n ih =>
    obtain ⟨outs,hpath,hfields,hbounded⟩ := ih (by omega)
    let k : Fin 6 := ⟨n,by omega⟩
    obtain ⟨hbudget,hleft,hright⟩ := cell_capacity ls k
    obtain ⟨out,hr,hfield,hout⟩ := cell_run k cap (lefts ls k)
      (rights ls k) (stage cap ls original outs n)
      (cell_input cap ls original outs k hc hfields)
      (hbudget.trans hcap) (hleft.trans hcap) (hright.trans hcap)
    rw [node_result] at hfield
    have hnext : ∀ q scanned,next k q scanned=some ⟨n+1,hn⟩ := by
      intro q scanned
      simp [next,k,show n≠5 by omega,Nat.mod_eq_of_lt hn]
    have hcall := ready_path k ⟨n+1,hn⟩ _ _ _ hr hnext
    have htotal := (hpath.trans hcall).enlarge (show n*cap+
        (RecoveryQueryCell.budget (operations k) (lefts ls k)
          (rights ls k)+1) ≤ (n+1)*cap by
      have hb := hbudget.trans hcap
      rw [Nat.add_mul,Nat.one_mul]
      omega)
    refine ⟨Function.update outs k out,?_,fields_update cap ls outs k out hfields hfield,?_⟩
    · change Path 0 ⟨n+1,hn⟩ ((n+1)*cap) _
        (stage cap ls original (Function.update outs k out) (k.val+1))
      rw [update_successor]
      exact htotal
    · change Bounded cap (stage cap ls original (Function.update outs k out) (k.val+1))
      rw [update_successor]
      exact install_bounded k cap _ _ hbounded hout

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
