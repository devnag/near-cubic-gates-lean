import Proof.CaseAnalysis.CommonProgramSuppliers

/-! The entire fixed common program has one polynomial bound in 2^n,
including zero, the original source recovery, and paid query clear. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def polynomial (p : Parameters) (c : Constants) (x : ℕ):=
  c.prefixC*(x+1)^c.prefixE+
  (c.recoveryC*(2^p.Bw+1)^c.recoveryE)*(x+1)^(p.Aw*c.recoveryE)+
  (CloseoutCapacity.coefficient p.Aq p.Bq+2*2^p.Bq+5)*(x+1)^(p.Aq+1)+
  oneCoefficient p*(x+1)^oneExponent p+c.twoC*(x+1)^c.twoE+10

theorem budget_polynomial (p : Parameters) (c : Constants) (bits : List Bool) :
    runBudget p c bits ≤ polynomial p c (2^bits.length):=by
  have hr:=CloseoutCommonQueryClear.recovery_bound c.recoveryC c.recoveryE p.Aw p.Bw bits.length
  have hc:=CloseoutCommonQueryClear.budget_bound p.Aq p.Bq bits
  unfold runBudget polynomial
  omega

theorem exists_budget (p : Parameters) (c : Constants) :
    ∃ C E : ℕ,∀ bits : List Bool,runBudget p c bits ≤ C*(2^bits.length+1)^E:=by
  have term (C E : ℕ) : SourcePoly (fun x=>C*(x+1)^E):=
    (sourcePoly_pow (sourcePoly_id.add (polyDominated_const 1)) E).const_mul C
  have h : SourcePoly (polynomial p c):=
    (((((term c.prefixC c.prefixE).add
      (term (c.recoveryC*(2^p.Bw+1)^c.recoveryE) (p.Aw*c.recoveryE))).add
      (term (CloseoutCapacity.coefficient p.Aq p.Bq+2*2^p.Bq+5) (p.Aq+1))).add
      (term (oneCoefficient p) (oneExponent p))).add (term c.twoC c.twoE)).add (polyDominated_const 10)
  obtain ⟨E,C,hC⟩:=h
  exact ⟨C,E,fun bits=>(budget_polynomial p c bits).trans (hC (2^bits.length))⟩

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
