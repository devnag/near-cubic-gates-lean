import Proof.Amplification.RecoveryCaseOnePaddedBitRun
import Proof.MachineModel.GeneratedAmplifierEvaluator

/-! C.12's sufficient envelope for the whole padded Case1 evaluator. Reuse
the original complete-table runtime bound; all crop, field-copy and reset
costs are included. No parameter magnitude or supplied scratch is omitted. -/
namespace NearCubicWires.RepairSource.CloseoutCaseOne
open RepairOrdinary SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem padded_evaluation_bound {n target : Nat} (f : BoolFunction n)
    (hn : n ≤ target) (address : BitInput target) :
    RecoveryCaseOnePaddedEvaluation.budget f hn address ≤ 4096 * (2^n + 1)^2 := by
  let u : Nat := 2^n + 1
  have hu : 1 ≤ u := Nat.le_add_left 1 _
  have hn2 : n + 1 ≤ 2^n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hnu : n + 1 ≤ u := hn2.trans (by unfold u; omega)
  have hnU : n ≤ u := by omega
  have hbits : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have h1 : 1 ≤ u^2 := Nat.one_le_pow _ _ hu
  have huu : u ≤ u^2 := Nat.le_self_pow (by decide) _
  have hm : n * n.bits.length ≤ u^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hnU (hbits.trans hnU)
  have ha : GeneratedAmplifier.Arity.budget n ≤ 64 * u^2 := by
    unfold GeneratedAmplifier.Arity.budget MatrixUnaryTemplate.budget
    nlinarith
  have hschema : (frame n.bits ++ boolFunctionTable f).length ≤ 3 * u := by
    simp only [List.length_append, frame_length, GeneratedAmplifier.table_length]
    unfold u
    omega
  let low := RecoveryCaseOnePaddedEvaluation.low hn address
  have hpayload : (GeneratedAmplifier.payload f low).length ≤ 5 * u := by
    rw [GeneratedAmplifier.payload_length]
    unfold u
    omega
  have hr : GeneratedAmplifier.Runtime.budget f low ≤ 1024 * u^2 := by
    calc
      _ ≤ 128 * (GeneratedAmplifier.payload f low).length * (n + 1) + 128 :=
        GeneratedAmplifier.runtime_bound f low
      _ ≤ 128 * (5 * u) * u + 128 := by gcongr
      _ ≤ _ := by nlinarith
  change RecoveryCaseOnePaddedEvaluation.budget f hn address ≤ 4096 * u^2
  unfold RecoveryCaseOnePaddedEvaluation.budget RecoveryCaseOneCropPrepare.budget
    RecoveryCaseOneArchive.budget RecoveryCaseOneGeneratedArity.budget
    GeneratedAmplifier.Prepared.budget RecoveryCaseOneEvaluation.budget
    RecoveryCaseOneEvaluationPayload.framedBudget RecoveryCaseOneEvaluationPayload.budget
    RecoveryCaseOneEvaluator.budget RecoveryCaseOneEvaluator.resetBudget
    RecoveryCaseOneEvaluation.schema
  simp only [List.length_append, frame_length, List.length_ofFn]
  simp only [List.length_append, frame_length] at hschema
  simp only [low] at hr
  nlinarith

end
end NearCubicWires.RepairSource.CloseoutCaseOne
