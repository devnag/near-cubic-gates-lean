import Proof.Amplification.RecoveryClauseEvaluationReject

namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundaryState (mode : Fin 3) (s : State) (e : Extra) : State :=
  ⟨s.bits,s.capacity,s.backing,s.fields,s.flag,if mode=1 then e.aggregate else false⟩
def boundaryExtra (mode : Fin 3) (e : Extra) : Extra :=
  ⟨e.source,e.row,e.counter,e.binaryCount,e.committed,e.found,e.value,e.valid,e.guard,
    if mode=0 then false else e.aggregate,e.cap,e.prefixLimit⟩

theorem boundary_state_other (mode : Fin 3) (s : State) (e : Extra) (i : Fin 28) (hi : i≠27) :
    s.tapes i=(boundaryState mode s e).tapes i := by
  refine Fin.addCases (m:=24) (n:=4) (motive:=fun j=>j≠27 →
    s.tapes j=(boundaryState mode s e).tapes j) ?_ ?_ i hi
  · intro j _; rw [tapes_core,tapes_core]; rfl
  · intro j hj
    refine Fin.addCases (m:=3) (n:=1) (motive:=fun k=>k.natAdd 24≠27 →
      s.tapes (k.natAdd 24)=(boundaryState mode s e).tapes (k.natAdd 24)) ?_ ?_ j hj
    · intro k _; simp [State.tapes,boundaryState]
    · intro k hk; fin_cases k; exact False.elim (hk rfl)

theorem boundary_extra_update (mode : Fin 3) (s : State) (e : Extra) :
    (boundaryExtra mode e).tapes (boundaryState mode s e)=Function.update (e.tapes s) 13
      [if mode=0 then false else e.aggregate] := by
  change ![e.source,e.row,CompareMachine.word (s.bits.length+1),[e.found],[e.value],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.valid],e.counter,
      CompareMachine.word e.cap,frame e.binaryCount,frame e.committed,[e.guard],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[if mode=0 then false else e.aggregate]]=
    Function.update ![e.source,e.row,CompareMachine.word (s.bits.length+1),[e.found],[e.value],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.valid],e.counter,
      CompareMachine.word e.cap,frame e.binaryCount,frame e.committed,[e.guard],
      List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.aggregate]]
      ((0 : Fin 1).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
      [if mode=0 then false else e.aggregate]
  simp only [Matrix.vecCons,← Fin.cons_update,Fin.update_cons_zero]

theorem boundary_routing (input output : Fin 42→List Bool)
    (hc : ∀ j : Fin 28,j≠27 → input (j.castAdd 14)=output (j.castAdd 14))
    (he : ∀ j : Fin 14,j≠13 → input (j.natAdd 28)=output (j.natAdd 28))
    (i : Fin 42) (h27 : i≠27) (h41 : i≠41) : input i=output i := by
  refine Fin.addCases (m:=28) (n:=14) (motive:=fun k=>k≠27 → k≠41 → input k=output k) ?_ ?_ i h27 h41
  · intro j hj _
    apply hc j
    intro h; subst j; exact hj rfl
  · intro j _ hj
    apply he j
    intro h; subst j; exact hj rfl

@[simp] theorem tapes_answer (s : State) (e : Extra) : tapes s e 27=[s.result] := rfl

theorem boundary_layout (mode : Fin 3) (s : State) (e : Extra) :
    boundaryOutput mode (tapes s e)=tapes (boundaryState mode s e) (boundaryExtra mode e) := by
  funext i
  by_cases hi : i=27
  · subst i
    simp only [boundary_result,tapes_aggregate,tapes_answer]
    simp [boundaryState,readTapeBit]
  · by_cases hj : i=41
    · subst i
      by_cases hm : mode=0 <;> simp [boundaryOutput,tapes_aggregate,boundaryExtra,hm]
    · have ho : tapes s e i=tapes (boundaryState mode s e) (boundaryExtra mode e) i := by
        apply boundary_routing (tapes s e) (tapes (boundaryState mode s e) (boundaryExtra mode e)) ?_ ?_ i hi hj
        · intro j hn
          rw [tapes_left,tapes_left]
          exact boundary_state_other mode s e j hn
        · intro j hn
          rw [tapes_right,tapes_right,boundary_extra_update]
          simp [hn]
      by_cases hm : mode=0 <;> simpa [boundaryOutput,hi,hj,hm] using ho

theorem boundary_ready_state (mode : Fin 3) (s : State) (e : Extra) :
    ReadyRun (boundaryMachine mode) 1 (tapes s e) (tapes (boundaryState mode s e) (boundaryExtra mode e)) := by
  rw [← boundary_layout]
  exact boundary_ready mode (tapes s e) s.result e.aggregate rfl rfl

theorem boundary_valid (mode : Fin 3) (s : State) (e : Extra) (word : List Bool)
    (hs : s.Valid) (he : e.Valid s word) :
    (boundaryState mode s e).Valid ∧ (boundaryExtra mode e).Valid (boundaryState mode s e) word :=
  ⟨hs,⟨he.source,he.row,he.counter,he.count,he.committed,he.cap,he.prefixBound,he.reset⟩⟩

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
