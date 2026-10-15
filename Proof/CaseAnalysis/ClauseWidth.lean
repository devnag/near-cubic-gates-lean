import Proof.CaseAnalysis.SourceCounts

/-! One source-fixed clause width for every bounded oracle at the selected
native width. Its exponent is chosen before the hierarchy clock. -/
namespace NearCubicWires.RepairSource.CloseoutSourceCounts
open SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem clause_degree (a : PointwisePCPPAlgorithm)
    (queryCoefficient queryDegree oracleDegree : Nat) :
    ∃ degree onset : Nat, 1 ≤ degree ∧ ∀ q, onset ≤ q →
      shortBound a queryCoefficient queryDegree oracleDegree q ≤ (q+2)^degree ∧
      ∀ bits, 2^bits ≤ shortBound a queryCoefficient queryDegree oracleDegree q →
        bits ≤ Nat.clog 2 ((q+2)^degree) := by
  obtain ⟨C,e,_hC,hbound⟩ :=
    shortBound_polynomial a queryCoefficient queryDegree oracleDegree
  refine ⟨e+1,C,by omega,?_⟩
  intro q hq
  have hpoly : shortBound a queryCoefficient queryDegree oracleDegree q ≤ (q+2)^(e+1) := by
    calc
      _ ≤ C*(q+1)^e := hbound q
      _ ≤ (q+2)*(q+2)^e := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) e)
      _ = _ := by rw [pow_succ]; ring
  refine ⟨hpoly,?_⟩
  intro bits hbits
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  exact hbits.trans (hpoly.trans (Nat.le_pow_clog (by decide) _))

end NearCubicWires.RepairSource.CloseoutSourceCounts
