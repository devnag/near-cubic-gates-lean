import Proof.CaseAnalysis.CaseTwoLive
import Proof.CaseAnalysis.CaseTwoHardness

/-! The recovery branch supplies the exact canonical description consumed
by Case2. The selected source length is absorbed into its final dyadic cost. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
open SourceInterfaces RepairSource OuterPCPRecovery RecoveryScheduleEnvelope
open CanonicalSATSelfReduction BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem recovered_description {M : TimedDecisionMachine} {T : ℕ→ℕ} {n : ℕ}
    (pcp : ProjectionPCP M T) (degree : ℕ) (input : BitInput n)
    (small : RecoveryChoice.SmallOracle pcp degree input) :
    recoveredPrefix (descriptionWidth (pcp.nativeWidth n) (oracleSizeBound degree (pcp.nativeWidth n)))
      (boundedOracleRecoveryFormula pcp input (oracleSizeBound degree (pcp.nativeWidth n)))=
      canonicalBoundedCircuitDescription (oracleSizeBound degree (pcp.nativeWidth n))
        (RecoveryChoice.oracleSelector pcp degree input small).circuit := by
  have h:=RecoveryChoice.oracle_prefix pcp degree input small
    (descriptionWidth (pcp.nativeWidth n) (oracleSizeBound degree (pcp.nativeWidth n))) le_rfl
  rw [List.take_of_length_le (by simp only [List.length_ofFn];exact le_rfl)] at h
  exact h.trans (listOfFn_canonicalDescriptionInput _ _)

theorem selected_budget (C E M n : ℕ) (hM : M ≤ 2^n) :
    C*(M+2^n+1)^E ≤ (C*2^E)*(2^n+1)^E := by
  calc
    _ ≤ C*(2*(2^n+1))^E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [mul_pow];ring

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Selected
