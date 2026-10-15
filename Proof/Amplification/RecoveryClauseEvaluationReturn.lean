import Proof.Amplification.RecoveryClauseEvaluationRouting

/-! Exact return layout for the retained assignment call on the clause
machine. Only the selected query field and the shared valuation workspace
change; the other two literal fields are retained for subsequent calls. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.VerifierDecoding RecoveryValuationStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def assignedState (s : State) (which : Fin 3) (out : Data) : State :=
  ⟨s.bits,s.capacity,s.backing,Function.update s.fields which (frame out.index),s.flag,s.result⟩
def assignedExtra (e : Extra) (s : State) (count : Nat) (out : Data) (guard : Bool) : Extra :=
  ⟨e.source,out.row,ZeroPadding.pad (RecoveryReusableUnpair.capacity s.bits) (CompareMachine.word count),
    e.binaryCount,e.committed,out.found,out.value,out.valid,guard,e.aggregate,e.cap,e.prefixLimit⟩

theorem assignment_output_slot (s : State) (e : Extra) (which : Fin 3) (word : List Bool)
    (count : Nat) (out : Data) (guard : Bool)
    (hs : e.source=ZeroPadding.pad (2*e.prefixLimit+1) (frame (word.take e.prefixLimit)))
    (hw : out.width=s.bits.length) (hsource : out.source=frame (word.take e.prefixLimit))
    (hc : out.capacity=RecoveryReusableUnpair.capacity s.bits) (j : Fin 16) :
    RecoveryAssignment.reuseTapes out count e.cap e.binaryCount e.committed guard
        (2*e.prefixLimit+1) (RecoveryReusableUnpair.capacity s.bits) s.capacity j=
      tapes (assignedState s which out) (assignedExtra e s count out guard) (assignmentSlots which j) := by
  fin_cases j <;>
    simp [RecoveryAssignment.reuseTapes,RecoveryAssignment.readyTapes,RecoveryAssignment.paddedTapes,
      RecoveryAssignment.padding,RecoveryAssignment.cfg_tapes,tapes,Extra.tapes,assignedState,
      assignedExtra,assignmentSlots,Fin.addCases,hw,hsource,hc,hs]
  all_goals rfl

theorem assigned_other (s : State) (which : Fin 3) (out : Data) (i : Fin 28)
    (hi : i≠savedSlot which) : s.tapes i=(assignedState s which out).tapes i := by
  refine Fin.addCases (m:=24) (n:=4) (motive:=fun j=>j≠savedSlot which →
    s.tapes j=(assignedState s which out).tapes j) ?_ ?_ i hi
  · intro j _
    rw [tapes_core,tapes_core]
    rfl
  · intro j hj
    refine Fin.addCases (m:=3) (n:=1) (motive:=fun k=>k.natAdd 24≠savedSlot which →
      s.tapes (k.natAdd 24)=(assignedState s which out).tapes (k.natAdd 24)) ?_ ?_ j hj
    · intro k hk
      have hkw : k≠which := by intro h; subst k; exact hk rfl
      simp [State.tapes,assignedState,hkw]
    · intro k _; fin_cases k; rfl

@[simp] theorem tapes_left (s : State) (e : Extra) (j : Fin 28) :
    tapes s e (j.castAdd 14)=s.tapes j := by simp [tapes]
@[simp] theorem tapes_right (s : State) (e : Extra) (j : Fin 14) :
    tapes s e (j.natAdd 28)=e.tapes s j := by simp [tapes]

theorem assignment_output_outside (s : State) (e : Extra) (which : Fin 3)
    (count : Nat) (out : Data) (guard : Bool) (i : Fin 42)
    (hi : ∀ j,assignmentSlots which j≠i) :
    tapes s e i=tapes (assignedState s which out) (assignedExtra e s count out guard) i := by
  apply routing_outside which (tapes s e)
    (tapes (assignedState s which out) (assignedExtra e s count out guard)) ?_ ?_ i hi
  · intro j hj
    rw [tapes_left,tapes_left]
    exact assigned_other s which out j hj
  · simp only [tapes_aggregate]
    rfl

theorem assignment_output (s : State) (e : Extra) (which : Fin 3) (word : List Bool)
    (count : Nat) (out : Data) (guard : Bool)
    (hs : e.source=ZeroPadding.pad (2*e.prefixLimit+1) (frame (word.take e.prefixLimit)))
    (hw : out.width=s.bits.length) (hsource : out.source=frame (word.take e.prefixLimit))
    (hc : out.capacity=RecoveryReusableUnpair.capacity s.bits) :
    install (assignmentSlots which) (tapes s e)
      (RecoveryAssignment.reuseTapes out count e.cap e.binaryCount e.committed guard
        (2*e.prefixLimit+1) (RecoveryReusableUnpair.capacity s.bits) s.capacity)=
      tapes (assignedState s which out) (assignedExtra e s count out guard) := by
  funext i
  by_cases hi : ∃ j,assignmentSlots which j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot (assignmentSlots which) (assignmentSlots_injective which)]
    exact assignment_output_slot s e which word count out guard hs hw hsource hc j
  · rw [install_other (assignmentSlots which) _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    exact assignment_output_outside s e which count out guard i (by intro j hj; exact hi ⟨j,hj⟩)

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
