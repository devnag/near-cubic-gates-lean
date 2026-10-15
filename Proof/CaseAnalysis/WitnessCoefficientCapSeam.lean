import Proof.CaseAnalysis.WitnessSourceSize

/-! The actual PCPP clause count is a positive power of two. Its exact
coefficient cap therefore needs no zero/max branch in the once-per-source
physical policy producer. The paper's cap is unchanged. -/
namespace NearCubicWires.RepairSource.CloseoutWitnessPolicy
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem actual_coefficient_cap (delta : ℚ) (copies q0 clauseBits : Nat) :
    CloseoutXor.cap delta q0 copies*max 1 (2*2^clauseBits)=
      (64*delta.den^(3*copies+2))*(q0+1)*2^clauseBits:=by
  have hm:0<2^clauseBits:=Nat.two_pow_pos _
  rw [max_eq_right (by omega : 1≤2*2^clauseBits)]
  unfold CloseoutXor.cap
  ring

end NearCubicWires.RepairSource.CloseoutWitnessPolicy
