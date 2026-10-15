import Proof.PCP.PCPPNativeHierarchyInput

/-! Literal hierarchy requests enter the same retained stream executor with
the original source-fixed separated bound; loading the oracle is linear. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : RepairSource.ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem original_budget {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) (oracle : List Bool) :
    budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits oracle=
      HierarchyStreamCost.framedBudget source H Cpad r+4*oracle.length+6 := by
  rw [HierarchyStreams.framed_budget_eq source H Cpad hpad r]
  unfold budget PCPPNativeInputFields.budget HierarchySourceInput.hierarchyInput
  simp only [RepairSource.frame]
  omega

theorem original_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad)
    (r : InputRequest) (oracle : List Bool) :
    ∃ result,run (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source+4*oracle.length+6)
      (input source k (HierarchySourceInput.hierarchyInput H r) oracle)=some result ∧
      result.steps ≤ HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source+4*oracle.length+6 ∧
      HierarchyStreams.Fields source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
        (List.ofFn r.2) (H.time r.1).bits (projected source k result.final) ∧
      (∀ j : Fin 4,j.val≠1 → result.final.heads (loadSlots source k j)=0 ∧
        result.final.tapes (loadSlots source k j)=PCPPNativeInputFields.output
          (HierarchySourceInput.hierarchyInput H r) oracle j) := by
  obtain ⟨result,hr,rs,hfields,hret⟩ := raw_run source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
    (List.ofFn r.2) (H.time r.1).bits oracle hpad
  have hb := HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  have he := original_budget source H Cpad hpad r oracle
  rw [he] at hr rs
  have more := run_moreFuel (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    ((HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
      (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source+4*oracle.length+6)-
        (HierarchyStreamCost.framedBudget source H Cpad r+4*oracle.length+6)) _ result hr
  rw [Nat.add_sub_of_le (by omega)] at more
  exact ⟨result,more,by omega,hfields,hret⟩

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
