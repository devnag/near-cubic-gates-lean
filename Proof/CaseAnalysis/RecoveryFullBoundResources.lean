import Proof.CaseAnalysis.RecoveryFullBound
import Proof.Circuits.PaddedRunnerBudgetClosure

/-! One loose fixed-degree polynomial pays the complete cold oracle-cap
producer, including the actual marker rewrite, copy and head restoration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFullBound
open LocalBitMultitape RepairSource RecoveryScheduleEnvelope
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def degree (d : ℕ) := 2*exponent d+2
def coefficient (d : ℕ) := DimensionPolynomial.coefficient (exponent d) 1+11

theorem budget_bound (d R : ℕ) : budget d R≤coefficient d*(R+2)^degree d := by
  have hb:=DimensionPolynomial.budget_bound (exponent d) 1 R
  have hv:=power_value d R
  have hf : oracleSizeBound d R≤(R+1)^exponent d := by
    dsimp only [DimensionPolynomial.value,Nat.one_mul] at hv
    omega
  have hp : oracleSizeBound d R≤(R+2)^degree d :=
    (hf.trans (Nat.pow_le_pow_left (by omega) (exponent d))).trans
      (Nat.pow_le_pow_right (by omega) (by unfold degree;omega))
  have hone : 1≤(R+2)^degree d := Nat.one_le_pow _ _ (by omega)
  change _≤DimensionPolynomial.coefficient (exponent d) 1*(R+2)^degree d at hb
  unfold budget coefficient
  nlinarith

theorem budget_polynomial (d : ℕ) {f : ℕ→ℕ} (hf : SourcePoly f) :
    SourcePoly (fun n=>budget d (f n)) :=
  ((sourcePoly_pow (hf.add (polyDominated_const 2)) (degree d)).const_mul (coefficient d)).mono
    (fun n=>budget_bound d (f n))

theorem bounded_cold_run (d R : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine d) (coefficient d*(R+2)^degree d) (input d R) out ∧
      out (sourceSlot d)=List.replicate R true ∧
      out (rawSlot d)=List.replicate (oracleSizeBound d R) true ∧
      out (compareSlot d)=CompareMachine.word (oracleSizeBound d R) := by
  obtain ⟨out,hr,hR,hB,hC⟩:=cold_run d R
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (budget_bound d R),hR,hB,hC⟩

end
end NearCubicWires.RepairOrdinary.RecoveryFullBound
