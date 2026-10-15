import Proof.CaseAnalysis.RecoveryRowAddressBatch
import Proof.Amplification.RecoveryRowStructureField

/-! The original row address changes at its one physical source port.
All enclosing bank identities keep the large grammar and gate banks opaque. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem row_address (node C D F L : ℕ) (out : List Bool) (n total : ℕ)
    (before after refs : List Bool) (Q : ℕ) (source stack : List Bool) (count : ℕ) :
    RecoveryBoundedRow.data node C D F L out n total after refs Q source stack count=
      Function.update (RecoveryBoundedRow.data node C D F L out n total before refs Q source stack count) 58 after := by
  have he : RecoveryBoundedQuery.extraData F after refs=
      Function.update (RecoveryBoundedQuery.extraData F before refs) 2 after := by
    funext i;fin_cases i <;> rfl
  unfold RecoveryBoundedRow.data RecoveryBoundedQueries.bankData RecoveryBoundedQuery.data
  rw [he,bank_update_right,bank_update_left,bank_update_left]
  rfl

theorem padded_address (B : ℕ) (A : Fin 73→List Bool) (word : List Bool) :
    RecoveryBoundedRowReuse.paddedData B (Function.update A 58 word)=
      Function.update (RecoveryBoundedRowReuse.paddedData B A) 58 (ZeroPadding.pad B word) := by
  funext i
  by_cases h : i=58
  · subst i
    simp only [RecoveryBoundedRowReuse.paddedData,Function.update_self]
    rfl
  · simp only [RecoveryBoundedRowReuse.paddedData,Function.update_of_ne h]

theorem after_address (B : ℕ) (A : Fin 73→List Bool) (stack packet word : List Bool) :
    RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B (Function.update A 58 word)) B stack packet=
      Function.update (RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B A) B stack packet) 58 (ZeroPadding.pad B word) := by
  rw [padded_address]
  exact bank_update_left _ _ 58 _

def data (A : Fin 78→List Bool) (P : Fin 37→List Bool) : Fin 115→List Bool:=
  Fin.addCases (m:=78) (n:=37) (motive:=fun _=>List Bool) A P
def heads (H : Fin 78→ℕ) : Fin 115→ℕ:=
  Fin.addCases (m:=78) (n:=37) (motive:=fun _=>ℕ) H (fun _=>0)
def rowSlots (i : Fin 78) : Fin 115:=i.castAdd 37
def projectionSlots (i : Fin 37) : Fin 115:=i.natAdd 78
def addressSlots (i : Fin 38) : Fin 115:=⟨if i.val=37 then 58 else 78+i.val,by have hi:=i.isLt;split_ifs <;> omega⟩
theorem row_injective : Function.Injective rowSlots := by
  intro i j h;exact Fin.ext (congrArg (fun i : Fin 115=>i.val) h)
theorem projection_injective : Function.Injective projectionSlots := by
  intro i j h;apply Fin.ext;have hv:=congrArg (fun i : Fin 115=>i.val) h;change 78+i.val=78+j.val at hv;omega
theorem address_injective : Function.Injective addressSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 115=>i.val) h
  have hi:=i.isLt;have hj:=j.isLt
  apply Fin.ext
  dsimp only [addressSlots] at hv
  split_ifs at hv <;> omega

theorem data_row (A : Fin 78→List Bool) (P : Fin 37→List Bool) (i : Fin 78) :
    data A P (rowSlots i)=A i:=Fin.addCases_left i
theorem data_projection (A : Fin 78→List Bool) (P : Fin 37→List Bool) (i : Fin 37) :
    data A P (projectionSlots i)=P i:=Fin.addCases_right i
theorem heads_row (H : Fin 78→ℕ) (i : Fin 78) : heads H (rowSlots i)=H i:=Fin.addCases_left i
theorem heads_projection (H : Fin 78→ℕ) (i : Fin 37) : heads H (projectionSlots i)=0:=Fin.addCases_right i
theorem address_old (i : Fin 37) : addressSlots (i.castAdd 1)=projectionSlots i := by
  apply Fin.ext
  have hi:=i.isLt
  change (if i.val=37 then 58 else 78+i.val)=78+i.val
  rw [if_neg (by omega)]
theorem address_new : addressSlots 37=rowSlots 58:=by rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
