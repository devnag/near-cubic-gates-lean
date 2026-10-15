import Proof.CaseAnalysis.WitnessFamilyResourcesCosts
import Proof.CaseAnalysis.WitnessLegalPolicyRun
import Proof.CaseAnalysis.MassThresholdWidth
import Proof.CaseAnalysis.WitnessCorePolicy

/-! The actual coefficient and term caps have one fixed-source polynomial
envelope in the guarded public input length. No hierarchy clock occurs in
the parameters of this construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open SourceInterfaces RepairSource RepairRepresentation CloseoutWitnessPolicy PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def countBound (coefficient degree N : ℕ) := coefficient*(N+1)^degree
def coreBound (D N : ℕ) := (D+1)*(N+1)
def coefficientCap (delta : ℚ) (copies D R cb : ℕ) :=
  CloseoutXor.cap delta (CorePolicy.q0 D R) copies*max 1 (2*2^cb)
def termCap (delta : ℚ) (copies D R cb : ℕ) := LegalPolicy.T delta copies (CorePolicy.q0 D R) cb
def coefficientBound (delta : ℚ) (copies D c d N : ℕ) :=
  (64*delta.den^(3*copies+2))*(coreBound D N+1)*countBound c d N
def termBound (delta : ℚ) (copies D c d N : ℕ) :=
  (2*countBound c d N)*(termNumerator delta copies*coreBound D N+termDenominator delta copies)
def scale (delta : ℚ) (copies D c d N : ℕ) :=
  N+2+countBound c d N+coefficientBound delta copies D c d N+
    termBound delta copies D c d N+CloseoutMassThreshold.literalWidth delta copies

theorem core_bound (D R N : ℕ) (h : R ≤ N) : CorePolicy.q0 D R ≤ coreBound D N := by
  have hc:=CloseoutLanguage.clause_linear D R
  unfold CorePolicy.q0 coreBound
  nlinarith

theorem policy_bounds (delta : ℚ) (copies D c d R N cb V : ℕ)
    (hR : R ≤ N) (hV : V ≤ countBound c d N) (hM : 2^cb ≤ countBound c d N) :
    N+1 ≤ scale delta copies D c d N ∧ V ≤ scale delta copies D c d N ∧
      coefficientCap delta copies D R cb ≤ scale delta copies D c d N ∧
      termCap delta copies D R cb ≤ scale delta copies D c d N ∧
      CloseoutMassThreshold.literalWidth delta copies ≤ scale delta copies D c d N := by
  have hq:=core_bound D R N hR
  have hcoef:coefficientCap delta copies D R cb ≤ coefficientBound delta copies D c d N := by
    unfold coefficientCap coefficientBound
    rw [actual_coefficient_cap]
    gcongr
  have hterm:xorTermBound delta (CorePolicy.q0 D R) copies ≤
      termNumerator delta copies*coreBound D N+termDenominator delta copies := by
    rw [naturalTermBound_exact]
    unfold naturalTermBound
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans (by gcongr))
  have ht:termCap delta copies D R cb ≤ termBound delta copies D c d N := by
    unfold termCap LegalPolicy.T termBound
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) hterm
  unfold scale
  omega

theorem coefficient_positive (delta : ℚ) (copies D R cb : ℕ) :
    0 < coefficientCap delta copies D R cb := by
  unfold coefficientCap
  rw [actual_coefficient_cap]
  positivity

theorem scale_polynomial (delta : ℚ) (copies D c d : ℕ) : SourcePoly (scale delta copies D c d) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v) := polyDominated_const v
  have hn:=sourcePoly_id.add (hc 1)
  have hcount:SourcePoly (countBound c d) := (sourcePoly_pow hn d).const_mul c
  have hcore:SourcePoly (coreBound D) := hn.const_mul (D+1)
  have hco:SourcePoly (coefficientBound delta copies D c d) :=
    ((hcore.add (hc 1)).const_mul (64*delta.den^(3*copies+2))).mul hcount
  have hterm:SourcePoly (termBound delta copies D c d) :=
    (hcount.const_mul 2).mul ((hcore.const_mul (termNumerator delta copies)).add
      (hc (termDenominator delta copies)))
  exact ((((sourcePoly_id.add (hc 2)).add hcount).add hco).add hterm).add
    (hc (CloseoutMassThreshold.literalWidth delta copies))

def countCoefficient (a : PointwisePCPPAlgorithm) (qc qd od : ℕ) :=
  (CloseoutSourceCounts.shortBound_polynomial a qc qd od).choose
def countDegree (a : PointwisePCPPAlgorithm) (qc qd od : ℕ) :=
  (CloseoutSourceCounts.shortBound_polynomial a qc qd od).choose_spec.choose
def sourceScale (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ) (delta : ℚ) (copies : ℕ) :=
  scale delta copies D (countCoefficient a qc qd od) (countDegree a qc qd od)

theorem counts_bound (a : PointwisePCPPAlgorithm) (qc qd od R N : ℕ) (hR : R ≤ N) :
    CloseoutSourceCounts.shortBound a qc qd od R ≤
      countBound (countCoefficient a qc qd od) (countDegree a qc qd od) N := by
  have h:∀ R,CloseoutSourceCounts.shortBound a qc qd od R ≤
      countCoefficient a qc qd od*(R+1)^countDegree a qc qd od :=
    (CloseoutSourceCounts.shortBound_polynomial a qc qd od).choose_spec.choose_spec.2
  exact (h R).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem source_scale_polynomial (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) : SourcePoly (sourceScale a qc qd od D delta copies) :=
  scale_polynomial delta copies D _ _

theorem source_envelope (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) :
    ∃ K E,1 ≤ K ∧ ∀ N,capacity (sourceScale a qc qd od D delta copies N) ≤ K*(N+1)^E := by
  have h:=((sourcePoly_pow ((source_scale_polynomial a qc qd od D delta copies).add
    (polyDominated_const 2)) 26).const_mul 100000000000000000000000000000000)
  obtain ⟨E,K,hbound⟩:=h
  refine ⟨K+1,E,by omega,fun N=>(hbound N).trans ?_⟩
  exact Nat.mul_le_mul_right _ (by omega)

theorem source_bounds (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) {n R Q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin Q→Fin n→ProjectedRandomBit R) (formula : ThreeCNF Q)
    (N : ℕ) (hR : R ≤ N) (hQ : Q ≤ qc*(R+1)^qd)
    (ho : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound od R) :
    let p:=a.output (PCPPSubstitution.sourceRequest a oracle projections formula)
    let S:=sourceScale a qc qd od D delta copies N
    N+1 ≤ S ∧ p.systematicBits+p.auxiliaryBits ≤ S ∧
      coefficientCap delta copies D R p.clauseBits ≤ S ∧
      termCap delta copies D R p.clauseBits ≤ S ∧
      CloseoutMassThreshold.literalWidth delta copies ≤ S := by
  obtain ⟨hv,hm⟩:=CloseoutSourceCounts.short_counts a oracle projections formula qc qd od hQ ho
  have hs:=counts_bound a qc qd od R N hR
  exact policy_bounds delta copies D _ _ R N _ _ hR (hv.trans hs) (hm.trans hs)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
