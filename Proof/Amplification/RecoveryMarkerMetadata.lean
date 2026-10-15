import Proof.Amplification.RecoveryMarkerWhole

/-! The three physical marker fields and polarity survive the surrounding
code traversal. This records the actual saved tapes used by the later
flat/nested consumer, without a supplied semantic field oracle. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerMetadata
open LocalBitMultitape RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Fields where
  payload : List Bool
  committed : List Bool
  count : List Bool
  flat : Bool
def read (x : State) : Fields := ⟨x.outer.fields 1,x.outer.fields 2,x.inner.data.fields 1,x.outer.result⟩
def store (which : Fin 3) (fields : Fields) (word : List Bool) : Fields :=
  if which.val=0 then {fields with payload:=word}
  else if which.val=1 then {fields with committed:=word} else {fields with count:=word}

theorem after_field (s : RecoveryClauseState.State) (which j : Fin 3) (hj : j≠which) :
    (s.after which).fields j=s.fields j := by
  unfold RecoveryClauseState.State.after
  split
  · rfl
  · exact Function.update_of_ne hj _ _

theorem literal_field (x : RecoveryRawLiteral.State) (j : Fin 3) (hj : j≠0) :
    (RecoveryRawLiteral.output x).data.fields j=x.data.fields j := by
  unfold RecoveryRawLiteral.output
  split
  · change (RecoveryCheckedLiteral.checkedState (x.data.after 0) 0 (RecoveryRawLiteral.literal x)).fields j=_
    rw [RecoveryClauseEvaluation.checked_field_other _ _ _ _ hj,after_field _ _ _ hj]
  · exact after_field x.data 0 j hj

theorem read_outer (x : State) : read (outerStep x)=read x := by
  unfold read outerStep
  rw [after_field x.outer 0 1 (by decide),after_field x.outer 0 2 (by decide),RecoveryThreeCellReader.after_result]

theorem read_empty (x : State) : read (emptyStep x)=read x := by
  unfold read emptyStep
  rw [after_field x.inner.data 0 1 (by decide)]

theorem read_literal (x : State) : read (literalStep x)=read x := by
  unfold read literalStep
  rw [literal_field x.inner 1 (by decide)]

theorem read_loaded (x : State) : read (loaded x)=read x := by
  unfold loaded
  split
  · exact read_outer x
  · change read (outerStep x)=read x
    exact read_outer x

theorem read_answered (x : State) (bit : Bool) : read (RecoveryMarkerFlags.answered x bit)=read x := rfl

theorem read_flat (x : State) :
    read (RecoveryMarkerFlags.flat x)={read x with flat:=x.inner.data.flag} := rfl

theorem read_saved (which : Fin 3) (x : State) :
    read (RecoveryMarkerSave.saved x which)=store which (read x) (x.inner.data.fields 0) := by
  fin_cases which <;> rfl

theorem read_tested (which : Fin 3) (x : State) :
    read (RecoveryMarkerAtom.tested which x)=store which (read x) (x.inner.data.fields 0) := by
  unfold RecoveryMarkerAtom.tested
  split
  · exact read_saved which x
  · rw [read_empty]
    exact read_saved which x

theorem atom_read (which : Fin 3) (x : State)
    (ha : RecoveryMarkerAtom.answer which x=true) :
    read (RecoveryMarkerAtom.output which x)=
      store which (read (RecoveryMarkerAtom.withSign which (literalStep x)))
        (frame (RecoveryMarkerAtom.variableWord x)) := by
  have hg : RecoveryMarkerAtom.good which (literalStep x)=true := by
    have h := ha
    rw [RecoveryMarkerAtom.answer,Bool.and_eq_true] at h
    exact h.1
  have ho : RecoveryMarkerAtom.output which x=
      RecoveryMarkerAtom.final which (RecoveryMarkerAtom.withSign which (literalStep x)) := by
    dsimp only [RecoveryMarkerAtom.output]
    exact if_pos hg
  rw [ho,RecoveryMarkerAtom.final,read_answered,read_tested]
  have hf : (RecoveryMarkerAtom.withSign which (literalStep x)).inner.data.fields 0=
      frame (RecoveryMarkerAtom.variableWord x) := by
    have h := RecoveryMarkerAtom.variable_field which x hg
    unfold RecoveryMarkerAtom.withSign
    split <;> exact h
  rw [hf]

end NearCubicWires.RepairOrdinary.RecoveryMarkerMetadata
