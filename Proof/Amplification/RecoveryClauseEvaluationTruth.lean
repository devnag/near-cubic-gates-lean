import Proof.Amplification.RecoveryClauseEvaluationCalls

/-! The physical truth update preserves the literal decoder and the retained
lookup workspace, and records the OR accumulator for the next literal. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def truthState (s : State) (e : Extra) : State :=
  ⟨s.bits,s.capacity,s.backing,s.fields,s.flag,RecoveryLiteralTruth.accepted s.result e.valid⟩
def truthExtra (s : State) (e : Extra) : Extra :=
  ⟨e.source,e.row,e.counter,e.binaryCount,e.committed,e.found,e.value,e.valid,e.guard,
    RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid,e.cap,e.prefixLimit⟩

theorem truth_input (s : State) (e : Extra) (j : Fin 5) :
    tapes s e (truthSlots j)=![[s.flag],[e.value],[e.aggregate],[s.result],[e.valid]] j := by
  fin_cases j <;> rfl

theorem truth_output_slot (s : State) (e : Extra) (j : Fin 5) :
    ![[s.flag],[e.value],[RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid],
      [RecoveryLiteralTruth.accepted s.result e.valid],[e.valid]] j=
      tapes (truthState s e) (truthExtra s e) (truthSlots j) := by
  fin_cases j <;> rfl

theorem truth_state_other (s : State) (e : Extra) (i : Fin 28) (hi : i≠27) :
    s.tapes i=(truthState s e).tapes i := by
  refine Fin.addCases (m:=24) (n:=4) (motive:=fun j=>j≠27 →
    s.tapes j=(truthState s e).tapes j) ?_ ?_ i hi
  · intro j _; rw [tapes_core,tapes_core]; rfl
  · intro j hj
    refine Fin.addCases (m:=3) (n:=1) (motive:=fun k=>k.natAdd 24≠27 →
      s.tapes (k.natAdd 24)=(truthState s e).tapes (k.natAdd 24)) ?_ ?_ j hj
    · intro k _; simp [State.tapes,truthState]
    · intro k hk; fin_cases k; exact False.elim (hk rfl)

theorem truth_extra_update (s : State) (e : Extra) :
    (truthExtra s e).tapes (truthState s e)=Function.update (e.tapes s) 13
      [RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid] := by
  change ![e.source,e.row,RepairSource.VerifierDecoding.CompareMachine.word (s.bits.length+1),[e.found],[e.value],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.valid],e.counter,
      RepairSource.VerifierDecoding.CompareMachine.word e.cap,frame e.binaryCount,frame e.committed,[e.guard],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,
      [RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid]]=
    Function.update ![e.source,e.row,RepairSource.VerifierDecoding.CompareMachine.word (s.bits.length+1),[e.found],[e.value],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.valid],e.counter,
      RepairSource.VerifierDecoding.CompareMachine.word e.cap,frame e.binaryCount,frame e.committed,[e.guard],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.aggregate]]
      ((0 : Fin 1).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
      [RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid]
  simp only [Matrix.vecCons,← Fin.cons_update,Fin.update_cons_zero]

theorem truth_routing (input output : Fin 42→List Bool)
    (hc : ∀ j : Fin 28,j≠27 → input (j.castAdd 14)=output (j.castAdd 14))
    (he : ∀ j : Fin 14,j≠13 → input (j.natAdd 28)=output (j.natAdd 28))
    (i : Fin 42) (hi : ∀ j,truthSlots j≠i) : input i=output i := by
  refine Fin.addCases (m:=28) (n:=14) (motive:=fun k=>(∀ j,truthSlots j≠k) → input k=output k) ?_ ?_ i hi
  · intro j hj
    apply hc j
    intro h; subst j; exact hj 3 rfl
  · intro j hj
    apply he j
    intro h; subst j; exact hj 2 rfl

theorem truth_output_outside (s : State) (e : Extra) (i : Fin 42)
    (hi : ∀ j,truthSlots j≠i) : tapes s e i=tapes (truthState s e) (truthExtra s e) i := by
  apply truth_routing (tapes s e) (tapes (truthState s e) (truthExtra s e)) ?_ ?_ i hi
  · intro j hj
    rw [tapes_left,tapes_left]
    exact truth_state_other s e j hj
  · intro j hj
    rw [tapes_right,tapes_right,truth_extra_update]
    simp [hj]

theorem truth_ready (s : State) (e : Extra) :
    ReadyRun truthMachine 1 (tapes s e) (tapes (truthState s e) (truthExtra s e)) := by
  have h := (RecoveryLiteralTruth.truth_ready s.flag e.value e.aggregate s.result e.valid).focus
    truthSlots (by decide) (tapes s e) (truth_input s e)
  have he : install truthSlots (tapes s e)
      ![[s.flag],[e.value],[RecoveryLiteralTruth.result s.flag e.value e.aggregate s.result e.valid],
        [RecoveryLiteralTruth.accepted s.result e.valid],[e.valid]]=
      tapes (truthState s e) (truthExtra s e) := by
    funext i
    by_cases hi : ∃ j,truthSlots j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [install_slot truthSlots (by decide)]
      exact truth_output_slot s e j
    · rw [install_other truthSlots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
      exact truth_output_outside s e i (by intro j hj; exact hi ⟨j,hj⟩)
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
