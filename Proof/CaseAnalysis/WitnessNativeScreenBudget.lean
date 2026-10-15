import Proof.CaseAnalysis.WitnessSourcePolicyBudget

/-! The native size screen is paid even on rejection. Its actual stream,
counter and cap programs have one polynomial in their measured parameter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open PCPPNativeResourceCost
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bound (G Z : ℕ):=1024*Z^3+1+counterCoefficient*Z^12+1+
  (DimensionPolynomial.coefficient (OracleCap.degree G) 1*(Z+2)^(2*OracleCap.degree G+2)+4*Z+18)

theorem budget_le (G : ℕ) (p : RawProjectionPCP) (R Q : ℕ) (hR:p.width≤R) (hQ:p.queries≤Q)
    (oracle : BooleanCircuit R) : budget G p R Q oracle.size≤bound G (sourceParameter oracle p Q) := by
  let Z:=sourceParameter oracle p Q
  have hRZ:R≤Z:=by dsimp only [Z,sourceParameter];omega
  have hsZ:oracle.size≤Z:=by dsimp only [Z,sourceParameter];omega
  have hz:p.word.length+R+Q+1≤Z:=by dsimp only [Z,sourceParameter];omega
  have stream:Streams.budget p R Q≤1024*Z^3:=
    (Streams.budget_bound p R Q hR hQ).trans (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hz 3))
  have counters:PCPPNativeColdCounters.budget p R Q oracle.size≤counterCoefficient*Z^12:=by
    have h:=source_counter_budget oracle p Q hR hQ
    unfold PCPPNativeCounterNodes.budget at h
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans h)
  have cap:=DimensionPolynomial.budget_bound (OracleCap.degree G) 1 R
  have poly:=Nat.mul_le_mul_left (DimensionPolynomial.coefficient (OracleCap.degree G) 1)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hRZ 2) (2*OracleCap.degree G+2))
  have cap_le:=cap.trans poly
  have hmin:=Nat.min_le_left (oracle.size+1) (DimensionPolynomial.value (OracleCap.degree G) 1 R)
  change budget G p R Q oracle.size≤bound G Z
  unfold budget NativeMeasured.budget OracleCap.budget OracleCap.Core.budget bound
  omega

theorem bound_mono (G : ℕ) {X Y : ℕ} (h:X≤Y) : bound G X≤bound G Y := by
  unfold bound
  gcongr

theorem bound_polynomial (G : ℕ) {Z : ℕ→ℕ} (hz:SourcePoly Z) : SourcePoly (fun n=>bound G (Z n)) := by
  dsimp only [bound]
  fast_budget_poly

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
