import Proof.CaseAnalysis.WitnessCountedReject
import Proof.CaseAnalysis.WitnessTermRoundReject

/-! Total bookkeeping for the counted term proof uses the original
accepted coefficient. Rejected words contribute only a dummy zero to the
unused proof suffix; the physical rejecting loop never adds that value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermChoice
open CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def coefficient (b : ℕ) (bits : List Bool) : Option ℚ := by
  classical
  exact (decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))).filter
    (fun q=>decide (PairHeader.valid bits ∧ natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b))
def rational (b : ℕ) (bits : List Bool) : ℚ := (coefficient b bits).getD 0

theorem coefficient_some (b : ℕ) (bits : List Bool) (q : ℚ) :
    coefficient b bits=some q ↔ PairHeader.valid bits ∧
      decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
      natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b := by
  simp only [coefficient,Option.filter_eq_some_iff,decide_eq_true_eq]
  tauto

theorem coefficient_isSome (b : ℕ) (bits : List Bool) :
    (coefficient b bits).isSome=true ↔ PairHeader.valid bits ∧
      ∃ q,decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
        natBitLength q.num.natAbs ≤ b ∧ natBitLength q.den ≤ b := by
  rw [Option.isSome_iff_exists]
  simp only [coefficient_some]
  tauto

theorem rational_eq (b : ℕ) (bits : List Bool) (q : ℚ)
    (hq : coefficient b bits=some q) : rational b bits=q := by
  simp only [rational,hq,Option.getD_some]

theorem rational_capped (b : ℕ) (bits : List Bool) (hb : 1 ≤ b) :
    natBitLength (rational b bits).num.natAbs ≤ b ∧ natBitLength (rational b bits).den ≤ b := by
  cases h : coefficient b bits with
  | none =>
    simp only [rational,h,Option.getD_none]
    norm_num [natBitLength]
    exact hb
  | some q =>
    rw [rational_eq b bits q h]
    exact (coefficient_some b bits q).mp h |>.2.2

theorem trace (T b : ℕ) (words : List (List Bool)) (hb : 1 ≤ b) (hk : words.length ≤ T) :
    CompetitorSumWidth.Trace (CompetitorSumWidth.width T b) CompetitorSumWidth.zero
      (Mass.records (words.map (rational b))) := by
  apply (Mass.rational_trace T b (words.map (rational b)) hb (by simpa only [List.length_map] using hk) ?_).1
  intro q hq
  obtain ⟨bits,_hbits,rfl⟩ := List.mem_map.mp hq
  exact rational_capped b bits hb

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermChoice
