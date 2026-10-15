import Proof.MachineModel.ClosureRadixNative
import Proof.MachineModel.NativeOutputBound

/-! The actual family execution pays its raw reads additively and only
one native table-capacity factor per polynomial. No C-sized cost is squared. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeFamilyBudget
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem optional_eq (B C Q w : ℕ) (ms : List (List ℕ)) :
    P1CompactBankCount.optionalBudget B C Q w ms=P1CompactBankCount.positiveBudget B C Q w ms+2:=by
  have hz : BankZero.budget B C ≤ P1CompactBankCount.positiveBudget B C Q w ms:=by
    unfold BankZero.budget P1CompactBankCount.positiveBudget BankExecution.budget P1CompactBankCount.budget
      CountIndexClean.budget CountIndex.budget P1CompactCloseoutRowsBankPolynomial.budget
      CloseoutRowsBankClear.budget cost
    simp only [List.map_nil,List.sum_nil]
    omega
  exact congrArg (fun x=>x+2) (max_eq_left hz)

theorem round_eq {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (ms : List (List ℕ)) :
    P1CompactNativeRound.budget gs Q w ms=cost gs.length ms+CountIndex.budget w ms.length+
      (40*Q+12)*P1CompactNativeMeasured.capacity gs Q w+103*Q+37:=by
  unfold P1CompactNativeRound.budget P1CompactEstimatorBankCycle.budget
  rw [optional_eq]
  unfold P1CompactBankCount.positiveBudget BankExecution.budget P1CompactBankCount.budget CountIndexClean.budget
    P1CompactCloseoutRowsBankPolynomial.budget CloseoutRowsBankClear.budget P1CompactCloseoutRowsDegreeLoop.budget
  ring

theorem round_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ)
    (ms : List (List (Fin gs.length))) (hQ : 1 ≤ Q) (hw : ms.length ≤ 2^w) :
    P1CompactNativeRound.budget gs Q w (rawIndices ms) ≤
      (gs.length+2)*(P1CompactNativeFamily.rawWord ms).length+
        (40*Q+13)*P1CompactNativeMeasured.capacity gs Q w+103*Q+37:=by
  have raw:=cost_le gs.length (rawIndices ms)
  have count:=CountIndex.fits n (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q)
    w gs.length Q ms.length hQ hw
  change CountIndex.budget w ms.length+1 ≤ P1CompactNativeMeasured.capacity gs Q w at count
  rw [round_eq]
  simp only [rawIndices,List.length_map]
  change cost gs.length (rawIndices ms)+CountIndex.budget w ms.length+
    (40*Q+12)*P1CompactNativeMeasured.capacity gs Q w+103*Q+37 ≤ _
  dsimp only [P1CompactNativeFamily.rawWord]
  nlinarith

theorem family_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w D : ℕ)
    (ps : List (List (List (Fin gs.length)))) (hQ : 1 ≤ Q)
    (hw : ∀ ms∈ps,ms.length ≤ 2^w) (hd : ∀ ms∈ps,(P1CompactNativeFamily.rawWord ms).length ≤ D) :
    P1CompactNativeFamily.budget gs Q w ps ≤ ps.length*((gs.length+2)*D+
      (40*Q+13)*P1CompactNativeMeasured.capacity gs Q w+103*Q+40)+3:=by
  have each : P1CompactNativeFamily.cost gs Q w ps ≤ (gs.length+2)*D+
      (40*Q+13)*P1CompactNativeMeasured.capacity gs Q w+103*Q+37:=by
    induction ps with
    | nil=>exact Nat.zero_le _
    | cons ms ps ih=>
      apply max_le
      · have h:=round_bound gs Q w ms hQ (hw _ (by simp))
        have d:=Nat.mul_le_mul_left (gs.length+2) (hd ms (by simp))
        omega
      · exact ih (fun p hp=>hw p (by simp [hp])) (fun p hp=>hd p (by simp [hp]))
  unfold P1CompactNativeFamily.budget
  exact Nat.add_le_add_right (Nat.mul_le_mul_left ps.length (by omega)) 3

end NearCubicWires.ExtIncidence.P1CompactNativeFamilyBudget

/-! The whole appended cut family fits a physically constructible multiple
of the retained native capacity and the two existing loop counters. -/
namespace NearCubicWires.ExtIncidence.P1CompactNativeOutputBound
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def allowance (C Q N : ℕ):=C*(Q+1)*(N+1)*256

theorem capacity_positive {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q w : ℕ) (hQ : 1 ≤ Q) :
    1 ≤ P1CompactNativeMeasured.capacity gs Q w:=by
  have h:=CountIndex.fits n (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q)
    w gs.length Q 0 hQ (Nat.zero_le _)
  change CountIndex.budget w 0+1 ≤ P1CompactNativeMeasured.capacity gs Q w at h
  omega

theorem polynomial_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ)
    (ms : List (List (Fin gs.length))) [_masks : P1MaskDegree gs (rawRows ms)] (hw : ms.length < 2^w) (hQ : 1 ≤ Q) :
    (P1CompactNativeFamily.emit gs Q w ms).length ≤ 256*(Q+1)*P1CompactNativeMeasured.capacity gs Q w:=by
  by_cases he : ms=[]
  · subst ms
    simp [P1CompactNativeFamily.emit,rawRows,P1CompactCloseoutRowsPacketOptional.cuts_nil]
  let rows:=rawRows ms
  have hl : ∀ row∈rows,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  have len : rows.length=ms.length:=by simp only [rows,rawRows,List.length_map]
  obtain ⟨result,run,rh,_rt,_clear,rs⟩:=P1CompactCloseoutRowsBankPolynomial.polynomial_run gs
    (P1CompactNativeWidth.width gs Q) (P1CompactNativeAllocation.capacity gs Q) Q w rows [] hl
    (by rw [len];exact List.length_pos_iff.mpr he) (by rw [len];exact hw)
    (by unfold P1CompactNativeWidth.width;omega) (by unfold P1CompactNativeWidth.width;omega) le_rfl
  have bound:=SelectiveReset.prefix_head (prefix_of_run P1CompactCloseoutRowsBankPolynomial.machine _ _ result run).1 31
  have hstart : (P1CompactCloseoutRowsBankPolynomial.entry gs (P1CompactNativeWidth.width gs Q)
      (P1CompactNativeAllocation.capacity gs Q) Q w
      (P1CompactCloseoutRowsPreparationBounds.capacity (l+r) (P1CompactNativeWidth.width gs Q)
        (P1CompactNativeAllocation.capacity gs Q) w gs.length Q) rows []).heads 31=0:=by
    rw [P1CompactBankFields.heads]
    rfl
  have hend : result.final.heads 31=(P1CompactNativeFamily.emit gs Q w ms).length:=by
    rw [rh]
    change ([]++P1CompactNativeFamily.emit gs Q w ms).length=_
    rw [List.nil_append]
  rw [hstart,hend] at bound
  have hC:=capacity_positive gs Q w hQ
  change result.steps ≤ P1CompactCloseoutRowsBankPolynomial.budget Q (P1CompactNativeMeasured.capacity gs Q w) at rs
  unfold P1CompactCloseoutRowsBankPolynomial.budget P1CompactCloseoutRowsDegreeLoop.budget CloseoutRowsBankClear.budget at rs
  nlinarith

theorem family_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ)
    (ps : List (List (List (Fin gs.length))))
    (hmask : ∀ ms∈ps, P1MaskDegree gs (rawRows ms)) (hw : ∀ ms∈ps,ms.length < 2^w) (hQ : 1 ≤ Q) :
    (ps.flatMap (P1CompactNativeFamily.emit gs Q w)).length ≤ allowance (P1CompactNativeMeasured.capacity gs Q w) Q ps.length:=by
  have h : (ps.flatMap (P1CompactNativeFamily.emit gs Q w)).length ≤
      ps.length*(256*(Q+1)*P1CompactNativeMeasured.capacity gs Q w):=by
    induction ps with
    | nil=>simp
    | cons ms ps ih=>
      letI := hmask ms (by simp)
      have hm:=polynomial_length gs Q w ms (hw ms (by simp)) hQ
      have ht:=ih (fun m h=>hmask m (by simp [h])) (fun m h=>hw m (by simp [h]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith
  unfold allowance
  nlinarith

end NearCubicWires.ExtIncidence.P1CompactNativeOutputBound
