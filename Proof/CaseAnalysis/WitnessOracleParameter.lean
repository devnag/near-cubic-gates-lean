import Proof.CaseAnalysis.WitnessNativePipelineBudget
import Proof.PCP.PCPPNativeCanonicalBounds

/-! Every decoded guessed oracle, including one later rejected for size,
has at most N nodes. Its native descriptor is therefore uniformly short. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem decoded_size (R N : ℕ) (raw : List Bool) (oracle : BooleanCircuit R)
    (hN:2≤N) (hraw:16*raw.length≤N) (hd:decodeBooleanCircuit R (value raw)=some oracle) : oracle.size≤N := by
  have checks:=DAGChecks.checks_of_typed oracle raw (encodeBooleanCircuit_of_decode hd).symm
  obtain ⟨c,_hc,decoded,count,_out,_desc⟩:=DAGChecks.typed_of_checks R raw checks
  have eq:c=oracle:=Option.some.inj (decoded.symm.trans hd)
  subst c
  exact count.le.trans (DAGBounds.guarded_fields N raw hN hraw).1

def parameterBound (L R Q N : ℕ):=L+R+Q+N+39*(R+N+5)^2+1

theorem parameter_le (p : RawProjectionPCP) (R Q N : ℕ) (raw : List Bool)
    (oracle : BooleanCircuit R) (hN:2≤N) (hraw:16*raw.length≤N)
    (hd:decodeBooleanCircuit R (value raw)=some oracle) :
    PCPPNativeResourceCost.sourceParameter oracle p Q≤parameterBound p.word.length R Q N := by
  have hs:=decoded_size R N raw oracle hN hraw hd
  have length: (PCPPNative.descriptor oracle).length≤39*(R+N+5)^2:=
    (PCPPNative.descriptor_length_bound oracle).trans
      (Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left (by omega) 2))
  unfold PCPPNativeResourceCost.sourceParameter parameterBound
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
