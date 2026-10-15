import Proof.Amplification.RecoveryMarkerAtomWhole

/-! All-code natural-number semantics for the executed marker atom.
Only actual predecessor/unpair outputs determine signs and payloads. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def codeCheck (which : Fin 3) (code : Nat) : Bool :=
  decide (code≠0) && decide ((Nat.unpair (Nat.unpair (code-1)).1).1≤1) &&
    tagOK which (decide ((Nat.unpair (Nat.unpair (code-1)).1).1≠0)) &&
    if which.val=1 then true else decide ((Nat.unpair (code-1)).2=0)

theorem decoded_sign (x : State) (hz : value x.inner.data.bits≠0) :
    (literalStep x).inner.data.flag=decide ((Nat.unpair (Nat.unpair (value x.inner.data.bits-1)).1).1≠0) := by
  have hp : (RecoveryRawLiteral.marked x.inner).present=true := by
    rw [RecoveryRawLiteral.marked_present]
    exact decide_eq_true hz
  change (RecoveryRawLiteral.output x.inner).data.flag=_
  rw [RecoveryRawLiteral.output,if_pos hp]
  change (RecoveryCheckedLiteral.checkedState (RecoveryRawLiteral.stepped x.inner).data 0
    (RecoveryRawLiteral.literal x.inner)).flag=_
  rw [RecoveryClauseEvaluation.checked_sign]
  have hv := RecoveryCellStore.head_value x.inner.data.bits hz
  change value (RecoveryRawLiteral.literal x.inner)=(Nat.unpair (value x.inner.data.bits-1)).1 at hv
  rw [hv]

theorem saved_bits (which : Fin 3) (x : State) : (saved which x).inner.data.bits=x.inner.data.bits := by
  unfold saved RecoveryMarkerSave.saved RecoveryMarkerSave.stored
  split <;> rfl
theorem sign_bits (which : Fin 3) (x : State) : (withSign which x).inner.data.bits=x.inner.data.bits := by
  unfold withSign
  split <;> rfl
theorem not_nonzero (n : Nat) : (!(decide (n≠0)))=decide (n=0) := by
  by_cases hn : n=0 <;> simp [hn]

theorem tail_answer (which : Fin 3) (x : State) (hz : value x.inner.data.bits≠0) :
    tailAnswer which (withSign which (literalStep x))=
      if which.val=1 then true else decide ((Nat.unpair (value x.inner.data.bits-1)).2=0) := by
  by_cases hm : which.val=1
  · simp only [tailAnswer,hm,ite_true]
  · simp only [tailAnswer,hm,ite_false,tested]
    change (!((saved which (withSign which (literalStep x))).inner.data.after 0).flag)=_
    rw [RecoveryThreeCellReader.after_flag,saved_bits,sign_bits]
    have hv := RecoveryRawLiteral.output_tail x.inner hz
    change value (literalStep x).inner.data.bits=(Nat.unpair (value x.inner.data.bits-1)).2 at hv
    rw [hv,not_nonzero]

theorem answer_eq_codeCheck (which : Fin 3) (x : State) :
    answer which x=codeCheck which (value x.inner.data.bits) := by
  by_cases hz : value x.inner.data.bits=0
  · have hp : (literalStep x).inner.present=false := by
      rw [show (literalStep x).inner.present=decide (value x.inner.data.bits≠0)
        from RecoveryRawLiteral.output_present x.inner]
      simp only [hz,ne_eq,not_true_eq_false,decide_false]
    simp only [answer,good,hp,Bool.false_and,codeCheck,hz,ne_eq,not_true_eq_false,decide_false]
  · have hp : (literalStep x).inner.present=true := by
      rw [show (literalStep x).inner.present=decide (value x.inner.data.bits≠0)
        from RecoveryRawLiteral.output_present x.inner]
      exact decide_eq_true hz
    have ht := RecoveryRawLiteral.output_tag x.inner hz
    change (literalStep x).inner.data.result=_ at ht
    rw [answer,good,hp,ht,decoded_sign x hz,tail_answer which x hz]
    simp only [codeCheck,decide_eq_true hz,Bool.true_and]

theorem variable_value (x : State) (hz : value x.inner.data.bits≠0) :
    value (variableWord x)=(Nat.unpair (Nat.unpair (value x.inner.data.bits-1)).1).2 :=
  (RecoveryRawLiteral.output_variable x.inner hz).2

end NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
