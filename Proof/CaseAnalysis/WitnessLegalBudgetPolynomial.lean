import Proof.CaseAnalysis.WitnessBudgetFast

/-! Literal legal-policy budgets are polynomial in their actual short
parameters and the actual clause count. No exponential metadata is hidden. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
open PaddedRunnerBudgetClosure BudgetTools RepairSource ProjectionNormalization CloseoutSchedule
open RecoveryWitnessPolicy CloseoutWitnessPolicy RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem gate {f : ℕ→ℕ} (hf:SourcePoly f) : SourcePoly (fun n=>GateDescription.budget (f n)) := by
  have hp:=polynomial_cost hf 1 1
  dsimp only [GateDescription.budget,DescriptionHorner.budget,WilliamsUnaryProduct.budget]
  fast_budget_poly

theorem description {R q W : ℕ→ℕ} (hr:SourcePoly R) (hq:SourcePoly q) (hw:SourcePoly W) (sym : Bool) :
    SourcePoly (fun n=>DescriptionPolicy.budget sym (R n) (q n) (W n)) := by
  have hgq:=gate hq
  have hgw:=gate hw
  cases sym <;>
    dsimp [DescriptionPolicy.budget,BaseDescription.budget,BaseDescription.value,
      BaseDescription.factor,BaseDescription.offset,RestrictedDescription.budget,
      RestrictedDescription.height,RestrictedDescription.factorInput,RestrictedDescription.factor,
      normalizedGateDescriptionCap,WilliamsUnaryProduct.budget] <;> fast_budget_poly

theorem mode {R : ℕ→ℕ} (hr:SourcePoly R) (e den : ℕ) :
    SourcePoly (fun n=>ModeWire.budget e den (R n)) := by
  have hp:SourcePoly (fun n=>DimensionPower.cost 1 (R n) 3):=power_cost hr 1 3
  have hd:SourcePoly (fun n=>DimensionPower.cost den (logScale (R n)) e):=
    power_cost (sourcePoly_logScale hr) den e
  have hc:SourcePoly (fun n=>DimensionPolynomial.budget 1 1 (R n+1)):=polynomial_cost (hr.add (polyDominated_const 1)) 1 1
  dsimp only [ModeWire.budget,ModeDimensions.budget,ModeDivide.budget,Clause.budget,Clog.budget]
  fast_budget_poly

theorem xor_terms {q : ℕ→ℕ} (hq:SourcePoly q) (delta : ℚ) (copies : ℕ) :
    SourcePoly (fun n=>xorTermBound delta (q n) copies) := by
  simp only [naturalTermBound_exact,naturalTermBound]
  fast_budget_poly

theorem terms {q cb : ℕ→ℕ} (hq:SourcePoly q) (hcb:SourcePoly cb)
    (hc:SourcePoly (fun n=>2^(cb n))) (delta : ℚ) (copies : ℕ) :
    SourcePoly (fun n=>TermPolicy.budget delta copies (q n) (cb n)) := by
  have hj:=xor_terms hq delta copies
  have hp:=power_cost hq (termNumerator delta copies) 1
  have hd:=power_cost hj 2 1
  dsimp only [TermPolicy.budget,TermCeil.budget,TermCeil.numerator,TermMultiply.budget,
    CloseoutCapacity.Power.budget,MatrixScorePower.budget,MatrixUnaryTemplate.budget,WilliamsUnaryProduct.budget]
  fast_budget_poly

theorem mass {T b : ℕ→ℕ} (ht:SourcePoly T) (hb:SourcePoly b) :
    SourcePoly (fun n=>MassCold.budget (T n) (b n)) := by
  have hw:SourcePoly (fun n=>CompetitorSumWidth.width (T n) (b n)):=
    (ht.add (polyDominated_const 1)).mul (hb.add (polyDominated_const 1))
  have hp:=power_cost (hw.add (polyDominated_const 1)) 2 1
  have hd:=power_cost (hw.add (polyDominated_const 1)) 4096 2
  dsimp only [MassCold.budget,MassPolicy.budget,MassWidth.budget,MassDimensions.budget,
    CompetitorSumFold.bootstrapBudget,CompetitorReusableDecision.capacity,WilliamsUnaryProduct.budget]
  fast_budget_poly

theorem legal {R q cb b : ℕ→ℕ} (hr:SourcePoly R) (hq:SourcePoly q) (hcb:SourcePoly cb)
    (hb:SourcePoly b) (hc:SourcePoly (fun n=>2^(cb n))) (e den copies : ℕ) (delta : ℚ) (sym : Bool) :
    SourcePoly (fun n=>LegalTemplate.budget e den delta copies sym (R n) (q n) (cb n) (b n)) := by
  have hw:SourcePoly (fun n=>LegalPolicy.W e den (R n)):=
    div (sourcePoly_pow hr 3) (fun n=>den*logScale (R n)^e)
  have ht:SourcePoly (fun n=>LegalPolicy.T delta copies (q n) (cb n)):=
    (hc.const_mul 2).mul (xor_terms hq delta copies)
  have hm:=mode hr e den
  have hterms:=terms hq hcb hc delta copies
  have hdescription:=description hr hq hw sym
  have hmass:=mass ht hb
  dsimp only [LegalTemplate.budget,LegalPolicy.budget]
  fast_budget_poly

end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
