import Proof.MachineModel.BankCountFields
import Proof.MachineModel.BankOptional

/-! Discharge the native worker's row-dependent input from the actual table
and counted index. Every other native input is the same empty-row template. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 128:=i.castAdd 15
theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 128=>x.val) h)

theorem width {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (rows : List (List Bool)) (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes 109=
      ZeroPadding.pad C (List.replicate w true):=rfl

theorem native_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (A : Fin 128→List Bool)
    (hbase : ∀ i,i≠36 → i≠52 → i≠107 → A (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w
        (CloseoutRowsPreparationBounds.capacity n p F w gs.length Q) [] out).tapes i)
    (ht : A 36=ZeroPadding.pad (CloseoutRowsPreparationBounds.capacity n p F w gs.length Q) rows.flatten) :
    let C:=CloseoutRowsPreparationBounds.capacity n p F w gs.length Q
    ∀ i,changed A C w rows.length (old i)=
      (CloseoutRowsBankPolynomial.entry gs p F Q w C rows out).tapes i := by
  dsimp only
  intro i
  by_cases h52 : i=52
  · subst i
    change ZeroPadding.pad _ (frame (RepairOrdinary.SignedSortKey.binary w (rows.length-1)))=_
    exact (BankMetadata.last_index gs p F Q w _ rows out).1.symm
  by_cases h107 : i=107
  · subst i
    change ZeroPadding.pad _ (frame (RepairOrdinary.SignedSortKey.binary w (rows.length-1)))=_
    exact (BankMetadata.last_index gs p F Q w _ rows out).2.symm
  have n52 : old i≠52:=fun h=>h52 (Fin.ext (congrArg (fun x : Fin 128=>x.val) h))
  have n107 : old i≠107:=fun h=>h107 (Fin.ext (congrArg (fun x : Fin 128=>x.val) h))
  have n115 : old i≠115:=by
    intro h
    have hv : i.val=115:=congrArg (fun x : Fin 128=>x.val) h
    have hi:=i.isLt
    omega
  simp only [changed,Function.update_of_ne n107,Function.update_of_ne n52,Function.update_of_ne n115]
  by_cases h36 : i=36
  · subst i
    exact ht.trans (BankFields.table gs p F Q w _ rows out).symm
  exact (hbase i h36 h52 h107).trans
    (BankMetadata.row_independent gs p F Q w rows out hl hw hF i h36 h52 h107).symm

end NearCubicWires.ExtIncidence.BankCount
