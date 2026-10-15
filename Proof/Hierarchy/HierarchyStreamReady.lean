import Proof.Hierarchy.HierarchyStreamScalars
import Proof.Hierarchy.HierarchyStreamCost

/-! The same-source stream prefix on literal hierarchy requests, with its
separated budget and exact request/width/query transport. The outer framing
allowance is recorded once for the eventual whole ordinary constructor. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem hierarchy_dimensions {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    request k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyEncode.encode H Cpad r ∧
    R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyProjection.width source H Cpad r.1 ∧
    Q source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyProjection.queries source H Cpad r.1 := by
  have he := HierarchySourceInput.encoded_request H Cpad hpad r
  refine ⟨he,?_,?_⟩
  · dsimp only [R,request]
    rw [he]
    rfl
  · dsimp only [Q,request]
    rw [he]
    rfl

theorem framed_budget_eq {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    HierarchyStreamCost.framedBudget source H Cpad r=
      4*(HierarchySourceInput.hierarchyInput H r).length+3+
        budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) := by
  obtain ⟨he,hR,hQ⟩ := hierarchy_dimensions source H Cpad hpad r
  dsimp only [HierarchyStreamCost.framedBudget,HierarchySourceInput.constructorBudget,budget]
  rw [he,hR,hQ]
  omega

theorem hierarchy_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    ∃ receipt,run (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source)
      (SourceHandoff.sourceTapes (HierarchySourceInput.hierarchyInput H r))=some receipt ∧
      receipt.steps ≤ HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source ∧
      Fields source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
        (H.time r.1).bits receipt.final := by
  obtain ⟨receipt,hr,hs,hf⟩ := scalar_run source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
    (List.ofFn r.2) (H.time r.1).bits hpad
  have he := framed_budget_eq source H Cpad hpad r
  have hb := HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  have hraw : budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) ≤
      HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
        (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source := by omega
  have hm := run_moreFuel (machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    (HierarchyStreamCost.coefficient source H Cpad*(r.1+1)^HierarchyStreamCost.inputExponent source*
      (natBitLength (H.time r.1)+1)^HierarchyStreamCost.logExponent source-
      budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)) _ receipt hr
  rw [Nat.add_sub_of_le hraw] at hm
  exact ⟨receipt,hm,hs.trans hraw,hf⟩

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
