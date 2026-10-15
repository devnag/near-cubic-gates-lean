import Proof.CaseAnalysis.WitnessResourcePolynomial
import Proof.CaseAnalysis.SourceCounts
import Proof.CaseAnalysis.ScheduleBounds

/-! The actual oracle-dependent family policy and its source-fixed code-size
envelope. The larger clause count below is used only to bound encoding size;
the accepted rational guard still uses the actual source clause count. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open SourceInterfaces RepairRepresentation RepairOrdinary CanonicalWitnessCodec
open CloseoutWitness ComponentwiseCircuitRestriction RecoveryWitnessPolicy
open CloseoutWitnessResources PolynomialSchedule
open ValidatorLeafWidthCore
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def limits (oracleArity oracleSize core clauses r copies W : Nat) (delta : ℚ) : RecoveryWitnessLimits :=
  let n:=core+r+1
  let J:=xorTermBound delta n copies
  let B:=CloseoutXor.cap delta n copies
  let D:=2*clauses
  let A:=CloseoutSampledWitness.massCap delta copies
  {oracleArity:=oracleArity,oracleSizeCap:=oracleSize,sumArity:=core,
   symmetric:=Average.limits core J B D A W
     (restrictedSymmetricDescriptionCap core n (2^symmetricDescriptionCap n W) W),
   threshold:=Average.limits core J B D A W
     (restrictedThresholdDescriptionCap core n (2^thresholdDescriptionCap n W) (thresholdDescriptionCap n W)),
   symmetricArity:=rfl,thresholdArity:=rfl}

theorem actual_symmetric (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity)
    (oracleArity oracleSize r copies W : Nat) (delta : ℚ) :
    (limits oracleArity oracleSize request.arity (2^(a.output request).clauseBits) r copies W delta).symmetric=
      CloseoutSampledWitness.symmetricLimits a request r copies W delta := rfl

theorem actual_threshold (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity)
    (oracleArity oracleSize r copies W : Nat) (delta : ℚ) :
    (limits oracleArity oracleSize request.arity (2^(a.output request).clauseBits) r copies W delta).threshold=
      CloseoutSampledWitness.thresholdLimits a request r copies W delta := rfl

theorem parameter_mono_count (oracleArity oracleSize core r copies W : Nat) (delta : ℚ)
    {M M' : Nat} (h : M ≤ M') :
    recoveryWitnessCodeParameter (limits oracleArity oracleSize core M r copies W delta) ≤
      recoveryWitnessCodeParameter (limits oracleArity oracleSize core M' r copies W delta) := by
  have hj : (2*M)*xorTermBound delta (core+r+1) copies ≤
      (2*M')*xorTermBound delta (core+r+1) copies := by gcongr
  have hb : natBitLength (CloseoutXor.cap delta (core+r+1) copies*max 1 (2*M)) ≤
      natBitLength (CloseoutXor.cap delta (core+r+1) copies*max 1 (2*M')) := by
    apply natBitLength_mono
    gcongr
  unfold recoveryWitnessCodeParameter limits Average.limits
  dsimp only
  omega

theorem parameter_polynomial (oracleArity oracleSize core clauses r W : Nat→Nat)
    (copies : Nat) (delta : ℚ)
    (ho : PolynomiallyBounded oracleArity) (hs : PolynomiallyBounded oracleSize)
    (hc : PolynomiallyBounded core) (hm : PolynomiallyBounded clauses)
    (hr : PolynomiallyBounded r) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>recoveryWitnessCodeParameter
      (limits (oracleArity q) (oracleSize q) (core q) (clauses q) (r q) copies (W q) delta)) := by
  have h1:=polynomiallyBounded_constant 1
  have hn:=polynomiallyBounded_add (polynomiallyBounded_add hc hr) h1
  have hJ:=polynomiallyBounded_comp (xor_terms_polynomial delta copies) hn
  have hB:=polynomiallyBounded_mul
    (polynomiallyBounded_mul (polynomiallyBounded_constant 32) (polynomiallyBounded_add hn h1))
    (polynomiallyBounded_constant (delta.den^(3*copies+2)))
  have hD:=polynomiallyBounded_mul (polynomiallyBounded_constant 2) hm
  have hterm:=polynomiallyBounded_mul hD hJ
  have hbits:=bits_polynomial (polynomiallyBounded_mul hB (polynomiallyBounded_max h1 hD))
  exact recoveryWitnessCodeParameter_polynomiallyBounded _ ho hs hc
    hterm hbits hW (restricted_symmetric_polynomial hc hn hW)
    hterm hbits hW (restricted_threshold_polynomial hc hn hW)

def envelope (a : PointwisePCPPAlgorithm) (queryCoefficient queryDegree oracleDegree degree copies : Nat)
    (W : Nat→Nat) (delta : ℚ) (q : Nat) : RecoveryWitnessLimits :=
  limits q (RecoveryScheduleEnvelope.oracleSizeBound oracleDegree q) (max q a.minimumArity)
    (CloseoutSourceCounts.shortBound a queryCoefficient queryDegree oracleDegree q)
    (CloseoutLanguage.clauseWidth degree q) copies (W q) delta

theorem envelope_polynomial (a : PointwisePCPPAlgorithm)
    (queryCoefficient queryDegree oracleDegree degree copies : Nat)
    (W : Nat→Nat) (delta : ℚ) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun q=>recoveryWitnessCodeParameter
      (envelope a queryCoefficient queryDegree oracleDegree degree copies W delta q)) := by
  have hr : PolynomiallyBounded (CloseoutLanguage.clauseWidth degree) :=
    polynomiallyBounded_mono (CloseoutLanguage.clause_linear degree)
      (polynomiallyBounded_mul (polynomiallyBounded_constant degree)
        (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)))
  exact parameter_polynomial _ _ _ _ _ _ copies delta polynomiallyBounded_id
    (RecoveryScheduleEnvelope.oracleSizeBound_polynomiallyBounded oracleDegree)
    (polynomiallyBounded_max polynomiallyBounded_id (polynomiallyBounded_constant a.minimumArity))
    (CloseoutSourceCounts.shortBound_polynomial a queryCoefficient queryDegree oracleDegree) hr hW

end
end NearCubicWires.RepairSource.CloseoutWitnessPolicy
