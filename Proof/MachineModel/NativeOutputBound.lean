import Proof.MachineModel.NativeFamilyBudget

/-! The whole appended cut family fits a physically constructible multiple
of the retained native capacity and the two existing loop counters. -/
namespace NearCubicWires.ExtIncidence.NativeOutputBound
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def allowance (C Q N : ℕ):=C*(Q+1)*(N+1)*256

theorem capacity_positive {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (hQ : 1 ≤ Q) :
    1 ≤ NativeMeasured.capacity gs Q w:=by
  have h:=CountIndex.fits n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q)
    w gs.length Q 0 hQ (Nat.zero_le _)
  change CountIndex.budget w 0+1 ≤ NativeMeasured.capacity gs Q w at h
  omega

theorem polynomial_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (ms : List (List (Fin gs.length))) (hw : ms.length < 2^w) (hQ : 1 ≤ Q) :
    (NativeFamily.emit gs Q w ms).length ≤ 256*(Q+1)*NativeMeasured.capacity gs Q w:=by
  by_cases he : ms=[]
  · subst ms
    simp [NativeFamily.emit,rawRows,CloseoutRowsPacketOptional.cuts_nil]
  let rows:=rawRows ms
  have hl : ∀ row∈rows,row.length=gs.length:=by
    intro row hr
    obtain ⟨m,_,rfl⟩:=List.mem_map.mp hr
    exact List.length_ofFn
  have len : rows.length=ms.length:=by simp only [rows,rawRows,List.length_map]
  obtain ⟨result,run,rh,_rt,_clear,rs⟩:=CloseoutRowsBankPolynomial.polynomial_run gs
    (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) Q w rows [] hl
    (by rw [len];exact List.length_pos_iff.mpr he) (by rw [len];exact hw)
    (by unfold NativeWidth.width;omega) (by unfold NativeWidth.width;omega) le_rfl
  have bound:=SelectiveReset.prefix_head (prefix_of_run CloseoutRowsBankPolynomial.machine _ _ result run).1 31
  have hstart : (CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
      (NativeAllocation.capacity gs Q) Q w
      (CloseoutRowsPreparationBounds.capacity (l+r) (NativeWidth.width gs Q)
        (NativeAllocation.capacity gs Q) w gs.length Q) rows []).heads 31=0:=by
    rw [BankFields.heads]
    rfl
  have hend : result.final.heads 31=(NativeFamily.emit gs Q w ms).length:=by
    rw [rh]
    change ([]++NativeFamily.emit gs Q w ms).length=_
    rw [List.nil_append]
  rw [hstart,hend] at bound
  have hC:=capacity_positive gs Q w hQ
  change result.steps ≤ CloseoutRowsBankPolynomial.budget Q (NativeMeasured.capacity gs Q w) at rs
  unfold CloseoutRowsBankPolynomial.budget CloseoutRowsDegreeLoop.budget CloseoutRowsBankClear.budget at rs
  nlinarith

theorem family_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) (Q w : ℕ)
    (ps : List (List (List (Fin gs.length)))) (hw : ∀ ms∈ps,ms.length < 2^w) (hQ : 1 ≤ Q) :
    (ps.flatMap (NativeFamily.emit gs Q w)).length ≤ allowance (NativeMeasured.capacity gs Q w) Q ps.length:=by
  have h : (ps.flatMap (NativeFamily.emit gs Q w)).length ≤
      ps.length*(256*(Q+1)*NativeMeasured.capacity gs Q w):=by
    induction ps with
    | nil=>simp
    | cons ms ps ih=>
      have hm:=polynomial_length gs Q w ms (hw ms (by simp)) hQ
      have ht:=ih (fun m h=>hw m (by simp [h]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith
  unfold allowance
  nlinarith

end NearCubicWires.ExtIncidence.NativeOutputBound
