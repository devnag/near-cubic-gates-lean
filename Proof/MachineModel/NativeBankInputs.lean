import Proof.MachineModel.NativeTemplateExact
import Proof.MachineModel.NativeInitializedPorts

/-! The physically initialized bank supplies all native, count-conversion
and raw-incidence inputs, without an input row count or last-index word. -/
namespace NearCubicWires.ExtIncidence.NativeBankInputs
open LocalBitMultitape RepairOrdinary NativeInitializedPorts NativeFanoutLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem base {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (source out : List Bool) (i : Fin 113) (h52 : i≠52) (h107 : i≠107) :
    word (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w) source out (BankCount.old i)=
      (CloseoutRowsBankPolynomial.entry gs (NativeWidth.width gs Q)
        (NativeAllocation.capacity gs Q) Q w (NativeMeasured.capacity gs Q w) [] out).tapes i:=by
  by_cases h31 : i=31
  · subst i;exact (BankOptional.entry_out gs _ _ Q w _ [] out).symm
  by_cases h104 : i=104
  · subst i;exact (BankFields.driver gs _ _ Q w _ [] out).symm
  by_cases h105 : i=105
  · subst i;exact (BankFields.log gs _ _ Q w _ [] out).symm
  have n31 : BankCount.old i≠31:=by intro h;apply h31;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n104 : BankCount.old i≠104:=by intro h;apply h104;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n105 : BankCount.old i≠105:=by intro h;apply h105;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)
  have n113 : BankCount.old i≠113:=by
    intro h;have hv:=congrArg (fun x : Fin 128=>x.val) h;have hi:=i.isLt
    simp only [BankCount.old,Fin.val_castAdd] at hv;omega
  simp only [word,if_neg n31,if_neg n104,if_neg n105,if_neg n113]
  change ZeroPadding.pad (NativeMeasured.capacity gs Q w) (NativeTemplate.payload gs Q w i)=_
  exact (NativeTemplate.exact_input gs Q w out i h31 h52 h104 h105 h107).symm

theorem count_input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (source out : List Bool) (j : Fin 18) :
    word (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w) source out (BankCount.slots j)=
      CountIndexCopy.input (NativeMeasured.capacity gs Q w) w 0 j:=by
  fin_cases j <;> simp [word,selection,NativeMaster.words,BankCount.slots,CountIndexCopy.input,
    CountIndex.padded,CountIndex.input,CountIndexCopy.extra,Fin.addCases,ZeroPadding.pad]

theorem raw_input {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ)
    (source out : List Bool) (j : Fin 5) :
    word (NativeMaster.words gs Q w) (NativeMeasured.capacity gs Q w) source out
      (BankCount.rawOld (BankExecution.slots j))=
        Padded.tapes (NativeMeasured.capacity gs Q w) gs.length source [] 0 j:=by
  fin_cases j <;> simp [word,selection,NativeMaster.words,BankCount.rawOld,BankExecution.slots,
    Padded.tapes,ZeroPadding.pad]

end NearCubicWires.ExtIncidence.NativeBankInputs
