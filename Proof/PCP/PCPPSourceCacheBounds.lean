import Proof.PCP.PCPPSourceCachePrepare

/-! A fixed polynomial pays the one faithful PCPP call and complete shared
cache setup. The original native emitter and row loops retain separate costs. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def totalDegree (a : PointwisePCPPAlgorithm) := max (PCPPRequestRuntime.sourceDegree a) (degree a+1)
def coefficient (a : PointwisePCPPAlgorithm) := PCPPRequestRuntime.sourceCoefficient a+
  PCPPQueryCold.coefficient (degree a) (PCPPQueryCachedBounds.coefficient a)+1
def totalBudget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  coefficient a*(PCPPRequestRuntime.sourceParameter r.circuit)^(totalDegree a)

private theorem sum_bound (M L e f I J : ℕ) (hM : 1 ≤ M) (hL : L ≤ M) :
    I*M^e+1+J*L^f ≤ (I+J+1)*M^(max e f) := by
  have he:=Nat.pow_le_pow_right hM (show e ≤ max e f from Nat.le_max_left _ _)
  have hf:=(Nat.pow_le_pow_left hL f).trans
    (Nat.pow_le_pow_right hM (show f ≤ max e f from Nat.le_max_right _ _))
  have hi:=Nat.mul_le_mul_left I he
  have hj:=Nat.mul_le_mul_left J hf
  have hone : 1 ≤ M^(max e f) := Nat.one_le_pow _ _ hM
  nlinarith

theorem charge_bound (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    PCPPRequestRuntime.sourceCoefficient a*
      (PCPPRequestRuntime.sourceParameter request.circuit)^(PCPPRequestRuntime.sourceDegree a)+1+
      setupBudget a request ≤ totalBudget a request := by
  exact sum_bound _ _ _ _ _ _
    (by unfold PCPPRequestRuntime.sourceParameter; omega)
    (by unfold PCPPRequestRuntime.sourceParameter; omega)

theorem budget_bound (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    budget a request ≤ totalBudget a request := by
  have hs:=PCPPRequestRuntime.source_bound a request
  have hc:=charge_bound a request
  unfold budget
  omega

theorem coefficient_pos (a : PointwisePCPPAlgorithm) : 0 < coefficient a := by
  unfold coefficient
  omega

theorem polynomial_run (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    ∃ r,run (machine a) (totalBudget a request) (input a request)=some r ∧
      (∀ j : Fin 19,r.final.tapes (cacheSlots a j)=
        PCPPQueryIndexPadding.clauseData (pcppOutput request (a.output request)) request.arity 0
          (PCPPQueryCachedBounds.capacity a (request.circuit.size+request.arity)) [] j) ∧
      (∀ j : Fin 19,r.final.heads (cacheSlots a j)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes (sizeSlot a)=List.replicate request.circuit.size true ∧
      r.final.heads (sizeSlot a)=0 ∧ r.steps ≤ totalBudget a request := by
  obtain ⟨r,hr,ht,hh,hs,hsh,hb⟩:=prepare_run a request
  have hm:=runFrom_moreFuel (machine a) (budget a request)
    (totalBudget a request-budget a request) _ r hr
  rw [Nat.add_sub_of_le (budget_bound a request)] at hm
  exact ⟨r,hm,ht,hh,hs,hsh,hb.trans (charge_bound a request)⟩

end NearCubicWires.RepairOrdinary.PCPPSourceCache
