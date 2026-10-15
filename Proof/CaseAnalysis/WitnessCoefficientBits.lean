import Proof.CaseAnalysis.WitnessCoefficientCapSeam
import Proof.PCP.ProjectionDimensionDyadic
import Proof.PCP.ProjectionDimensionPolynomial

/-! The exact coefficient policy needs the bit length of its cap, not the
numeric power of two. Reuse the checked dyadic shift and fixed polynomial
producer; the remaining clause-bit addition is performed once per source. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def factor (delta : ℚ) (copies : ℕ):=64*delta.den^(3*copies+2)
theorem factor_positive (delta : ℚ) (copies : ℕ) : 0<factor delta copies:=by
  exact Nat.mul_pos (by decide) (Nat.pow_pos delta.pos)

theorem exact_bits (delta : ℚ) (copies q0 clauseBits : ℕ) :
    natBitLength (CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits))=
      clauseBits+natBitLength (DimensionPolynomial.value 1 (factor delta copies) q0):=by
  rw [CloseoutWitnessPolicy.actual_coefficient_cap]
  have hpos:0<factor delta copies*(q0+1):=Nat.mul_pos (factor_positive delta copies) (by omega)
  simpa only [DimensionPolynomial.value,pow_one,factor,Nat.mul_comm] using
    DimensionDyadic.bitLength_shift (factor delta copies*(q0+1)) clauseBits hpos

theorem factor_run (delta : ℚ) (copies q0 : ℕ) : ∃ output,
    ClockJoin.ReadyRun (DimensionPolynomial.machine 1 (factor delta copies))
      (DimensionPolynomial.budget 1 (factor delta copies) q0)
      (DimensionPolynomial.input 1 q0) output ∧
      output ⟨0,by simp [DimensionPolynomial.tapes]⟩=List.replicate q0 true ∧
      output (DimensionPolynomial.widthSlot 1)=
        VerifierDecoding.CompareMachine.word
          (natBitLength (factor delta copies*(q0+1))):=by
  obtain ⟨output,h,hi,_,_,hw⟩:=DimensionPolynomial.polynomial_run 1 (factor delta copies) q0
    (factor_positive delta copies)
  exact ⟨output,h,hi,by simpa only [DimensionPolynomial.value,pow_one] using hw⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientBits
