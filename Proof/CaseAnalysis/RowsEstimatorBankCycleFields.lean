import Proof.MachineModel.NativeBankPosition
import Proof.CaseAnalysis.RowsEstimatorBankCountOptionalRetained

/-! The completed optional worker has the literal all-blank reload bank. -/
namespace NearCubicWires.ExtIncidence.EstimatorBankCycle
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_heads (pos : ℕ) (out : List Bool) (i : Fin 113) :
    CloseoutRowsBankClear.zeroHeads out i=NativeInitialize.extraH pos out (BankCount.old i) := by
  fin_cases i <;> rfl

theorem native_word (C : ℕ) (source out : List Bool) (i : Fin 113) :
    CloseoutRowsBankClear.blank C out i=
      NativeInitializedPorts.word (fun _ : Fin 15=>[]) C source out (BankCount.old i) := by
  fin_cases i <;>simp [CloseoutRowsBankClear.blank,NativeInitializedPorts.word,BankCount.old,selection,ZeroPadding.pad]

theorem unused (data : Fin 15→List Bool) (C pos : ℕ) (source out : List Bool) (i : Fin 128)
    (hi : i.val=114 ∨ 116 ≤ i.val) :
    NativeBankPosition.heads pos out i=0 ∧ NativeInitialize.extraH pos out i=0 ∧
      NativeInitializedPorts.word data C source out i=List.replicate C false := by
  fin_cases i <;>simp_all [NativeBankPosition.heads,NativeBankPosition.raised,NativeInitialize.extraH,
    NativeInitializedPorts.word,selection,ZeroPadding.pad]

theorem cleared (data : Fin 15→List Bool) (C pos next : ℕ) (source out word : List Bool)
    (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (hh : ∀ i,H (BankCount.old i)=CloseoutRowsBankClear.zeroHeads word i)
    (ha : ∀ i,A (BankCount.old i)=CloseoutRowsBankClear.blank C word i)
    (sh : H 113=next) (sa : A 113=source) (ch : H 115=0) (ca : A 115=List.replicate C false)
    (keep : ∀ i : Fin 128,i.val=114 ∨ 116 ≤ i.val →
      H i=NativeBankPosition.heads pos out i ∧ A i=NativeInitializedPorts.word data C source out i)
    (i : Fin 128) : H i=NativeInitialize.extraH next word i ∧
      A i=NativeInitializedPorts.word (fun _ : Fin 15=>[]) C source word i := by
  by_cases hi : i.val<113
  · let j : Fin 113:=⟨i.val,hi⟩
    have he : BankCount.old j=i:=Fin.ext rfl
    rw [←he]
    exact ⟨(hh j).trans (native_heads next word j),(ha j).trans (native_word C source word j)⟩
  · by_cases h113 : i=113
    · subst i;exact ⟨sh,sa⟩
    by_cases h115 : i=115
    · subst i
      simpa [NativeInitialize.extraH,NativeInitializedPorts.word,selection,ZeroPadding.pad] using And.intro ch ca
    have hn113 : i.val≠113:=fun he=>h113 (Fin.ext he)
    have hn115 : i.val≠115:=fun he=>h115 (Fin.ext he)
    have hother : i.val=114 ∨ 116 ≤ i.val:=by omega
    have first:=unused data C pos source out i hother
    have last:=unused (fun _ : Fin 15=>[]) C next source word i hother
    exact ⟨(keep i hother).1.trans (first.1.trans last.2.1.symm),
      (keep i hother).2.trans (first.2.2.trans last.2.2.symm)⟩

end NearCubicWires.ExtIncidence.EstimatorBankCycle
