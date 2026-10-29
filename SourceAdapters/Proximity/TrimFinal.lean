import SourceAdapters.Proximity.TrimVerifierPolynomial
import SourceAdapters.Proximity.TrimAddressPolynomial

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the fixed trimming join, discharged by two actual
ordinary machines on the raw request word with one fixed quartic clock.
The source hypotheses and the target encodings are unchanged. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Adapters.Joins

theorem trimVerifier_join : NearCubicGates.Adapters.Joins.TrimVerifier := by
  let K := 40010 + 2 * (verifierCoefficient + addressCoefficient)
  refine ⟨K, 4, by dsimp [K]; omega, ?_, ?_⟩
  · exact ⟨verifierWordFunction.enlargeBudget (fun r =>
      Nat.mul_le_mul_right (((trimRequestWord r).length + 1) ^ 4) (by dsimp [K]; omega))⟩
  · exact ⟨addressWordFunction.enlargeBudget (fun r =>
      Nat.mul_le_mul_right (((trimRequestWord r).length + 1) ^ 4) (by dsimp [K]; omega))⟩

end NearCubicGates.Adapters.Proximity.Trim
