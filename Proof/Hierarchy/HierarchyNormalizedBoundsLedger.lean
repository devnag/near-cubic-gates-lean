import Proof.Hierarchy.HierarchyNormalizedBoundsMass

/-! Exact accounting for query, clause-list and outer serialization, with
the three executed joins. The source/normalization prefix stays separate. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
open RepairOrdinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def serializerCoefficient : ℕ :=
  1000000000000+PCPClauseList.coefficient+1000000000000000000000*wordCoefficient^12+3

theorem serialization_bound (k CH Cpad : ℕ) (code x : List Bool) :
    HierarchyNormalized.budget source k CH Cpad code x ≤ 
      HierarchyStreams.budget source k CH Cpad code x+
        serializerCoefficient*(resource source k CH Cpad code x+1)^60 := by
  let M := resource source k CH Cpad code x
  have h12 : (M+1)^12 ≤ (M+1)^60 := pow_le_pow_right₀ (by omega) (by omega)
  have h13 : (M+1)^13 ≤ (M+1)^60 := pow_le_pow_right₀ (by omega) (by omega)
  have hone : 1 ≤ (M+1)^60 := Nat.one_le_pow 60 _ (by omega)
  have hqm := query_mass source k CH Cpad code x
  have hcm := clause_mass source k CH Cpad code x
  have hquery : PCPTraversal.budget (mass (HierarchyQuery.fields source k CH Cpad code x)) ≤ 
      1000000000000*(M+1)^60 := by
    unfold PCPTraversal.budget
    exact (by gcongr : 1000000000000*(mass (HierarchyQuery.fields source k CH Cpad code x)+1)^12 ≤ 
      1000000000000*(M+1)^12).trans (Nat.mul_le_mul_left _ h12)
  have hc := PCPClauseList.budget_bound (HierarchyClauses.groups source k CH Cpad code x)
    (PCPTripleNative.group_three _)
  have hclause : PCPClauseList.budget (HierarchyClauses.groups source k CH Cpad code x) ≤ 
      PCPClauseList.coefficient*(M+1)^60 :=
    hc.trans ((by gcongr : PCPClauseList.coefficient*
      ((PCPTripleLoop.stream (HierarchyClauses.groups source k CH Cpad code x)).length+1)^13 ≤ 
      PCPClauseList.coefficient*(M+1)^13).trans (Nat.mul_le_mul_left _ h13))
  have hw := word_size source k CH Cpad code x
  have hp := Nat.pow_le_pow_left hw 12
  rw [mul_pow,←pow_mul] at hp
  have houter : PCPOuter.budget (wordSize source k CH Cpad code x) ≤ 
      (1000000000000000000000*wordCoefficient^12)*(M+1)^60 := by
    have ho := (PCPOuter.budget_polynomial (wordSize source k CH Cpad code x)).trans
      (Nat.mul_le_mul_left 1000000000000000000000 hp)
    simpa only [Nat.mul_assoc] using ho
  have htotal : PCPTraversal.budget (mass (HierarchyQuery.fields source k CH Cpad code x))+
      PCPClauseList.budget (HierarchyClauses.groups source k CH Cpad code x)+
      PCPOuter.budget (wordSize source k CH Cpad code x)+3 ≤ serializerCoefficient*(M+1)^60 := by
    calc
      _ ≤ 1000000000000*(M+1)^60+PCPClauseList.coefficient*(M+1)^60+
        (1000000000000000000000*wordCoefficient^12)*(M+1)^60+3*(M+1)^60 := by omega
      _=serializerCoefficient*(M+1)^60 := by unfold serializerCoefficient; ring
  change ((HierarchyStreams.budget source k CH Cpad code x+1+
    PCPTraversal.budget (mass (HierarchyQuery.fields source k CH Cpad code x)))+1+
    PCPClauseList.budget (HierarchyClauses.groups source k CH Cpad code x))+1+
    PCPOuter.budget (wordSize source k CH Cpad code x) ≤
      HierarchyStreams.budget source k CH Cpad code x+serializerCoefficient*(M+1)^60
  omega

def framedBudget {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2))) (Cpad : ℕ) (r : InputRequest) :=
  4*(HierarchySourceInput.hierarchyInput H r).length+3+
    HierarchyNormalized.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)

theorem framed_serialization_bound {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    framedBudget source H Cpad r ≤ HierarchyStreamCost.framedBudget source H Cpad r+
      serializerCoefficient*(Streams.resource (source.output (HierarchyEncode.encode H Cpad r))
        (HierarchyProjection.width source H Cpad r.1) (HierarchyProjection.queries source H Cpad r.1)+1)^60 := by
  have hb := serialization_bound source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) (List.ofFn r.2)
  obtain ⟨he,hR,hQ⟩ := HierarchyStreams.hierarchy_dimensions source H Cpad hpad r
  dsimp only [resource] at hb
  rw [he,hR,hQ] at hb
  rw [HierarchyStreams.framed_budget_eq source H Cpad hpad r]
  unfold framedBudget
  omega

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalizedBounds
