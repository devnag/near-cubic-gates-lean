import Proof.CaseAnalysis.CaseOneEvaluationBound
import Proof.MachineModel.OrdinaryAmplifierReplayBounds

/-! The existing Case1 amplifier constructor and its paid replay/reset fit
C.12 directly when the input and generated arities fit the final address.
Only a sufficient fixed power is retained; no sharp replay cost is needed. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem amplifier_budget_bound {c d : Nat} (amplifier : OrdinaryScheduleAmplifier c d)
    (request : AmplifierRequest) (target : Nat) (htarget : 1 ≤ target)
    (hin : request.inputArity ≤ target)
    (hout : (amplifier.output request.inputArity request.function).arity ≤ target) :
    RecoveryCaseOneAmplifier.budget amplifier request ≤
      65536 * (2^target + 1)^(2 * max 1 amplifier.constructionExponent) := by
  let K := max 1 amplifier.constructionExponent
  let u : Nat := 2^target + 1
  let W := u^K
  let b := 2^(amplifier.constructionExponent * max 1 request.inputArity)
  let f := (amplifier.output request.inputArity request.function).function
  let n := (amplifier.output request.inputArity request.function).arity
  have hK : 1 ≤ K := Nat.le_max_left _ _
  have hu : 1 ≤ u := Nat.le_add_left 1 _
  have huW : u ≤ W := Nat.le_self_pow (by omega) _
  have hW : 1 ≤ W := Nat.one_le_pow _ _ hu
  have hW2 : 1 ≤ W^2 := Nat.one_le_pow _ _ hW
  have hm : max 1 request.inputArity ≤ target := max_le htarget hin
  have hb : b ≤ W := by
    calc
      b ≤ 2^(amplifier.constructionExponent * target) :=
        Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_left amplifier.constructionExponent hm)
      _ = (2^target)^amplifier.constructionExponent := by
        rw [← pow_mul, Nat.mul_comm amplifier.constructionExponent target]
      _ ≤ u^amplifier.constructionExponent :=
        Nat.pow_le_pow_left (Nat.le_add_right _ 1) _
      _ ≤ W := Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  have hn : n ≤ target := hout
  have hpow : 2^n ≤ 2^target := Nat.pow_le_pow_right (by decide) hn
  have hnpow : n + 1 ≤ 2^n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hbits : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hs : (frame n.bits ++ boolFunctionTable f).length ≤ 3 * W := by
    have hlen := GeneratedAmplifier.table_length f
    simp only [List.length_append, frame_length]
    change (boolFunctionTable f).length = 2^n at hlen
    unfold u at huW
    omega
  have hs5 : b + 0 + (frame n.bits ++ boolFunctionTable f).length + 1 ≤ 5 * W := by
    omega
  have hd := AmplifierReplay.budget_bound b 0 n (boolFunctionTable f)
    (GeneratedAmplifier.table_length f)
  have hd5 := hd.trans (Nat.mul_le_mul_left 1024 (Nat.pow_le_pow_left hs5 2))
  have hwhole : RecoveryCaseOneAmplifier.budget amplifier request ≤ 65536 * W^2 := by
    change 2 * AmplifierReplay.Dock.budget b n (boolFunctionTable f) + 2 ≤ _
    nlinarith
  simpa only [W, u, K, ← pow_mul, Nat.mul_comm] using hwhole

end
end NearCubicWires.RepairSource.CloseoutCaseOne
