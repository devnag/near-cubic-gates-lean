import Proof.CaseAnalysis.WitnessBoundedFamilyBudget

/-! Choose the actual cold preprocessing degree before the hierarchy.
Only its coefficient changes when the hierarchy's linear input scale is fixed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace BudgetTools

theorem degree_before_scale {f g : ℕ→ℕ} (hf:SourcePoly f) (hg:SourcePoly g) :
    ∃ degree,∀ J,∃ coefficient,∀ N,
      f (J*(N+2))+g N≤coefficient*(N+1)^degree := by
  obtain ⟨e,K,hf⟩:=hf
  obtain ⟨d,L,hg⟩:=hg
  refine ⟨Nat.max e d,fun J=>⟨K*(2*J+1)^e+L,fun N=>?_⟩⟩
  have hscale:J*(N+2)+1≤(2*J+1)*(N+1):=by nlinarith
  have hfirst: f (J*(N+2))≤(K*(2*J+1)^e)*(N+1)^e:=by
    have hp:=Nat.mul_le_mul_left K (Nat.pow_le_pow_left hscale e)
    simpa only [Nat.mul_pow,Nat.mul_assoc] using (hf (J*(N+2))).trans hp
  have he:(N+1)^e≤(N+1)^(Nat.max e d):=Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_left _ _)
  have hd:(N+1)^d≤(N+1)^(Nat.max e d):=Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right _ _)
  have first:=hfirst.trans (Nat.mul_le_mul_left _ he)
  have second:=(hg N).trans (Nat.mul_le_mul_left L hd)
  nlinarith

end BudgetTools
namespace BoundedFamily
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem degree_before_hierarchy (a : PointwisePCPPAlgorithm)
    (cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ) (hD:1≤D)
    (hcut:2^a.minimumArity≤cutoff)
    (hbudget:∀ N,FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)≤K*(N+1)^E) :
    ∃ degree,∀ {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
      (_ : H.coefficient≤Cpad) (hpad:k+3≤Cpad),
      ∃ coefficient,∀ (r : InputRequest) (bits : List Bool),
        budget source a k H.coefficient Cpad cutoff D G copies E K symDen thrDen delta
          (VerifierEncoding.code H.verifier) r.2 bits hpad≤coefficient*(r.1+1)^degree := by
  obtain ⟨degree,hd⟩:=BudgetTools.degree_before_scale
    (ColdNative.bound_polynomial source a D G copies cutoff delta hD)
    (outer_polynomial source a G D copies E K symDen thrDen delta)
  refine ⟨degree,fun H Cpad hcoeff hpad=>?_⟩
  obtain ⟨coefficient,hc⟩:=hd (HierarchyBudget.coefficient source H Cpad)
  exact ⟨coefficient,fun r bits=>(budget_le source a H Cpad cutoff D G copies E K symDen thrDen delta
    hcoeff hpad hcut hbudget r bits).trans (hc r.1)⟩

end BoundedFamily
end
end NearCubicWires.RepairOrdinary.CloseoutWitness
