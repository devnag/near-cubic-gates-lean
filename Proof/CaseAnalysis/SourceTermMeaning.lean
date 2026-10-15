import Proof.CaseAnalysis.SourceTerms

/-! Exact semantic and resource transport at the honest term-list boundary. -/
namespace NearCubicWires.RepairSource.CloseoutSourceTerms
open SourceInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Circuit : CanonicalWitnessCodec.CircuitFamily} {n size : Nat}
  {family : SizedFunctionFamily} (evaluate : Circuit n→BoolFunction n)
  (terms : List (LegalCircuitTerm Circuit n)) (sum : UnitIntervalCircuitSum family n size)
  (meaning : terms.map (fun term=>(term.coefficient,evaluate term.circuit))=sum.terms)
include meaning

theorem term_count : terms.length=sum.terms.length := by
  have h:=congrArg List.length meaning
  simpa only [List.length_map] using h

theorem coefficients : terms.map (·.coefficient)=sum.terms.map (·.1) := by
  have h:=congrArg (fun ts : List (ℚ×BoolFunction n)=>ts.map (·.1)) meaning
  simpa only [List.map_map,Function.comp_def] using h

theorem term_member (term : LegalCircuitTerm Circuit n) (ht : term ∈ terms) :
    (term.coefficient,evaluate term.circuit) ∈ sum.terms := by
  rw [←meaning]
  exact List.mem_map_of_mem ht

theorem value (input : BitInput n) :
    (terms.map fun term=>(term.coefficient : ℝ)*bitAsReal (evaluate term.circuit input)).sum=
      sum.value input := by
  unfold UnitIntervalCircuitSum.value
  rw [←meaning]
  simp only [List.sum_eq_foldl,List.foldl_map]

theorem mass : (((terms.map fun term=>|term.coefficient|).sum : ℚ) : ℝ)=sum.coefficientMass := by
  have hm : (((terms.map fun term=>|term.coefficient|).sum : ℚ) : ℝ)=
      (terms.map fun term=>|(term.coefficient : ℝ)|).sum := by
    push_cast
    simp only [List.map_map,Function.comp_def,Rat.cast_abs]
  rw [hm]
  unfold UnitIntervalCircuitSum.coefficientMass
  rw [←meaning]
  simp only [List.sum_eq_foldl,List.foldl_map]

end NearCubicWires.RepairSource.CloseoutSourceTerms
