import Proof.Hierarchy.CompetitorSumEntry
import Proof.CaseAnalysis.WitnessGcdPolicy

/-! One source-policy accumulator width serves every accepted sum. The
guard supplies its actual count bound; the coefficient mass remains exact. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
open CompetitorValidity CompetitorSumWidth
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def magnitude (q : ℚ) : Estimate:=⟨q.num.natAbs,0,q.den⟩
def records (qs : List ℚ):=qs.map magnitude

theorem magnitude_value (q : ℚ) : (magnitude q).value=|q|:=by
  simpa only [CompetitorThresholdDecision.numerator,Rat.num_abs_eq_abs_num,
    Int.natAbs_abs,Rat.den_abs_eq_den,magnitude,Estimate.value,Nat.cast_zero,sub_zero] using
    CompetitorThresholdDecision.threshold_fraction |q| (abs_nonneg q)

theorem magnitude_valid (q : ℚ) (b : ℕ) (hb : 1 ≤ b)
    (hn : natBitLength q.num.natAbs ≤ b) (hd : natBitLength q.den ≤ b) :
    (magnitude q).Valid b:=
  ⟨(GcdGuard.bits_iff b _ hb).mp hn,Nat.two_pow_pos _,(GcdGuard.bits_iff b _ hb).mp hd,q.pos⟩

theorem policy_trace (T b : ℕ) (xs : List Estimate) (hn : xs.length ≤ T)
    (hv : ∀ a∈xs,a.Valid b) : Trace (width T b) zero xs:=by
  apply trace_from_bound T b 0 zero xs (by omega) _ hv
  constructor <;> simp [zero]

theorem rational_trace (T b : ℕ) (qs : List ℚ) (hb : 1 ≤ b) (hn : qs.length ≤ T)
    (hv : ∀ q∈qs,natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b) :
    Trace (width T b) zero (records qs) ∧
      ((records qs).map Estimate.value).sum=(qs.map (fun q=>|q|)).sum:=by
  constructor
  · apply policy_trace T b (records qs) (by simpa [records] using hn)
    intro a ha
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ha
    exact magnitude_valid q b hb (hv q hq).1 (hv q hq).2
  · simp only [records,List.map_map,Function.comp_def,magnitude_value]

end NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
