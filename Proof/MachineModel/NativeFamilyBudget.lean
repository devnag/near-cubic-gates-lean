import Proof.MachineModel.NativeFamily

/-! The actual family execution pays its raw reads additively and only
one native table-capacity factor per polynomial. No C-sized cost is squared. -/
namespace NearCubicWires.ExtIncidence.NativeFamilyBudget
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem optional_eq (B C Q w : ℕ) (ms : List (List ℕ)) :
    BankCount.optionalBudget B C Q w ms=BankCount.positiveBudget B C Q w ms+2:=by
  have hz : BankZero.budget B C ≤ BankCount.positiveBudget B C Q w ms:=by
    unfold BankZero.budget BankCount.positiveBudget BankExecution.budget BankCount.budget
      CountIndexClean.budget CountIndex.budget CloseoutRowsBankPolynomial.budget
      CloseoutRowsBankClear.budget cost
    simp only [List.map_nil,List.sum_nil]
    omega
  exact congrArg (fun x=>x+2) (max_eq_left hz)

theorem round_eq {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (ms : List (List ℕ)) :
    NativeRound.budget gs Q w ms=cost gs.length ms+CountIndex.budget w ms.length+
      (40*Q+12)*NativeMeasured.capacity gs Q w+103*Q+37:=by
  unfold NativeRound.budget EstimatorBankCycle.budget
  rw [optional_eq]
  unfold BankCount.positiveBudget BankExecution.budget BankCount.budget CountIndexClean.budget
    CloseoutRowsBankPolynomial.budget CloseoutRowsBankClear.budget CloseoutRowsDegreeLoop.budget
  ring

theorem round_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (ms : List (List (Fin gs.length))) (hQ : 1 ≤ Q) (hw : ms.length ≤ 2^w) :
    NativeRound.budget gs Q w (rawIndices ms) ≤
      (gs.length+2)*(NativeFamily.rawWord ms).length+
        (40*Q+13)*NativeMeasured.capacity gs Q w+103*Q+37:=by
  have raw:=cost_le gs.length (rawIndices ms)
  have count:=CountIndex.fits n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q)
    w gs.length Q ms.length hQ hw
  change CountIndex.budget w ms.length+1 ≤ NativeMeasured.capacity gs Q w at count
  rw [round_eq]
  simp only [rawIndices,List.length_map]
  change cost gs.length (rawIndices ms)+CountIndex.budget w ms.length+
    (40*Q+12)*NativeMeasured.capacity gs Q w+103*Q+37 ≤ _
  dsimp only [NativeFamily.rawWord]
  nlinarith

theorem family_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w D : ℕ)
    (ps : List (List (List (Fin gs.length)))) (hQ : 1 ≤ Q)
    (hw : ∀ ms∈ps,ms.length ≤ 2^w) (hd : ∀ ms∈ps,(NativeFamily.rawWord ms).length ≤ D) :
    NativeFamily.budget gs Q w ps ≤ ps.length*((gs.length+2)*D+
      (40*Q+13)*NativeMeasured.capacity gs Q w+103*Q+40)+3:=by
  have each : NativeFamily.cost gs Q w ps ≤ (gs.length+2)*D+
      (40*Q+13)*NativeMeasured.capacity gs Q w+103*Q+37:=by
    induction ps with
    | nil=>exact Nat.zero_le _
    | cons ms ps ih=>
      apply max_le
      · have h:=round_bound gs Q w ms hQ (hw _ (by simp))
        have d:=Nat.mul_le_mul_left (gs.length+2) (hd ms (by simp))
        omega
      · exact ih (fun p hp=>hw p (by simp [hp])) (fun p hp=>hd p (by simp [hp]))
  unfold NativeFamily.budget
  exact Nat.add_le_add_right (Nat.mul_le_mul_left ps.length (by omega)) 3

end NearCubicWires.ExtIncidence.NativeFamilyBudget
