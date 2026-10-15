import Proof.CaseAnalysis.RecoveryGraphBudget

/-! The unchanged ordinary cold serializer has a source-fixed polynomial
budget. All capacities and bytes are charged by the same executed producer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization PaddedRunnerBudgetClosure
open RecoveryTseitinNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem power_sourcePoly {value : ℕ→ℕ} (hv : SourcePoly value) (D C : ℕ) :
    SourcePoly (fun n=>PCPSerializerCapacity.Power.budget D C (value n)) := by
  have hcost : SourcePoly (fun n=>2*C+2+D*(6*C*(value n+2)^(D+1)+7)) :=
    (polyDominated_const (2*C+2)).add
      ((((sourcePoly_pow (hv.add (polyDominated_const 2)) (D+1)).const_mul (6*C)).add
        (polyDominated_const 7)).const_mul D)
  refine PolyDominated.mono (((hv.const_mul 2).add (polyDominated_const 9)).add hcost) fun n=>?_
  exact Nat.add_le_add_left (DimensionPower.cost_bound D C (value n+1) D le_rfl) _

theorem cold_sourcePoly {arity count : ℕ→ℕ}
    (ha : SourcePoly arity) (hc : SourcePoly count) :
    SourcePoly (fun n=>Cold.budget (arity n) (count n)) := by
  have hsum := ha.add hc
  have hcapacity : SourcePoly (fun n=>Reuse.capacity (arity n) (count n)) :=
    (sourcePoly_pow (hsum.add (polyDominated_const 1)) 3).const_mul 2199023255552
  have hdrivers : SourcePoly (fun n=>Cold.driversBudget (arity n) (count n)) :=
    (((((hsum.const_mul 2).add (polyDominated_const 6)).add (polyDominated_const 1)).add
      (power_sourcePoly hsum 3 2199023255552)).add (polyDominated_const 1)).add
      ((hc.const_mul 10).add (polyDominated_const 13))
  have htaut : SourcePoly (fun n=>RecoveryTseitinTautology.Cold.budget (arity n)) :=
    PolyDominated.mono ((sourcePoly_pow (ha.add (polyDominated_const 1)) 3).const_mul 4294967296)
      (fun n=>RecoveryTseitinTautology.Cold.budget_bound (arity n))
  have hprefix : SourcePoly (fun n=>Cold.prefixBudget (arity n) (count n)) :=
    (hdrivers.add (polyDominated_const 1)).add
      ((htaut.const_mul 2).add (polyDominated_const 2))
  have hassertion : SourcePoly (fun n=>Assertion.budget (Reuse.capacity (arity n) (count n))) :=
    (polyDominated_const (2*Assertion.bits.length+2+1)).add
      ((hcapacity.const_mul 4).add (polyDominated_const 7))
  have hformula : SourcePoly (fun n=>Formula.budget (arity n) (count n)) :=
    ((((hc.mul (((hcapacity.const_mul 6).add (polyDominated_const 12)).add
      (polyDominated_const 2))).add hc).add (polyDominated_const 3)).add
      (polyDominated_const 1)).add hassertion
  exact (((((hprefix.add (polyDominated_const 1)).add
    ((hcapacity.const_mul 2).add (polyDominated_const 4))).add (polyDominated_const 1)).add
      (polyDominated_const 1)).add (polyDominated_const 1)).add hformula

theorem serialize_sourcePoly {arity : ℕ→ℕ} (c : ∀ n,BooleanCircuit (arity n))
    (ha : SourcePoly arity) (hc : SourcePoly (fun n=>(c n).nodes.length)) :
    SourcePoly (fun n=>Serialize.budget (c n)) := by
  have hf := cold_sourcePoly ha hc
  exact PolyDominated.mono (((hf.const_mul 6).add (polyDominated_const 8)).add
    ((sourcePoly_pow (hf.add (polyDominated_const 1)) 12).const_mul 1000000000064))
    (fun n=>serialize_budget (c n))

theorem original_sourcePoly {arity backing : ℕ→ℕ} (c : ∀ n,BooleanCircuit (arity n))
    (ha : SourcePoly arity) (hc : SourcePoly (fun n=>(c n).nodes.length))
    (hb : SourcePoly backing)
    (ho : ∀ n,(c n).output.val+1 ≤ backing n)
    (hi : ∀ n,arity n+1 ≤ backing n) :
    SourcePoly (fun n=>RecoveryBoundedGraphSerialize.budget (backing n) (c n)) := by
  exact PolyDominated.mono
    (((((hb.add (polyDominated_const 2)).const_mul 16).add
      ((serialize_sourcePoly c ha hc).const_mul 2)).add (polyDominated_const 3)))
    (fun n=>RecoveryBoundedGraphSerialize.budget_le (backing n) (c n) (ho n) (hi n))

/-- A caller may use its physically generated coarse W; no exact structural
size or originalWorkspace evaluator is required by this resource application. -/
theorem original_workspace_sourcePoly {arity width support : ℕ→ℕ}
    (c : ∀ n,BooleanCircuit (arity n)) (hw : SourcePoly width) (hs : SourcePoly support)
    (ha : ∀ n,arity n ≤ width n) (hc : ∀ n,(c n).nodes.length ≤ width n) :
    SourcePoly (fun n=>RecoveryBoundedGraphSerialize.budget
      (32*support n+10000000000*(width n+1)^6+64) (c n)) := by
  exact original_sourcePoly c (PolyDominated.mono hw ha) (PolyDominated.mono hw hc)
    (CloseoutRecoveryWorkspacePolynomial.row_workspace hs hw)
    (fun n=>(serializer_fits (c n) (width n) (support n) (ha n) (hc n)).2.1)
    (fun n=>(serializer_fits (c n) (width n) (support n) (ha n) (hc n)).2.2)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
