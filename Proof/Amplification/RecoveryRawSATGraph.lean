import Proof.Amplification.RecoveryRawSATCalls

/-! A raw-SAT body clears its result, extracts one actual outer list cell,
gates its presence, and executes the old whole clause evaluator after a
paid framed copy. No witness clause value is supplied to this controller. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev outerStates := stateCount outerMachine
noncomputable abbrev copyStates := stateCount copyMachine
noncomputable abbrev clauseStates := stateCount clauseMachine
noncomputable def sizes : Fin 4→Nat := ![2,outerStates,copyStates,clauseStates]
noncomputable def programs : (j : Fin 4)→Machine 70 (sizes j)
  | ⟨0,_⟩=>clearMachine
  | ⟨1,_⟩=>outerMachine
  | ⟨2,_⟩=>copyMachine
  | ⟨3,_⟩=>clauseMachine
  | ⟨n+4,h⟩=>False.elim (by omega)
noncomputable def next : (j : Fin 4)→Fin (sizes j)→(Fin 70→Bool)→Option (Fin 4)
  | ⟨0,_⟩,_,_=>some 1
  | ⟨1,_⟩,_,bits=>if bits 65 then some 2 else none
  | ⟨2,_⟩,_,_=>some 3
  | ⟨3,_⟩,_,_=>none
  | ⟨n+4,h⟩,_,_=>False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def prepared (x : State) := copied (outerStep (cleared x)) (headWord x)
def leafAnswer (x : State) (word : List Bool) :=
  RecoveryClauseEvaluation.clauseWordCheck (prepared x).clause (prepared x).valuation word
def answer (x : State) (word : List Bool) :=
  decide (RadixSemantics.value x.outer.bits≠0) && leafAnswer x word
def budget (width : Nat) := 8388608*(width+1)^2

structure AcceptedResult (x : State) (word : List Bool) where
  data : State
  valid : data.Valid word
  width : data.width=x.width
  outerBits : data.outer.bits=(x.outer.after 0).bits
  count : data.valuation.binaryCount=x.valuation.binaryCount
  committed : data.valuation.committed=x.valuation.committed
  cap : data.valuation.cap=x.valuation.cap
  result : data.clause.result=answer x word

theorem head_width (x : State) (word : List Bool) (hx : x.Valid word) : (headWord x).length=x.width :=
  (RecoveryCellStore.headWord_length x.outer.bits).trans hx.2.2.2

theorem prepared_valid (x : State) (word : List Bool) (hx : x.Valid word) : (prepared x).Valid word :=
  copied_valid _ word _ (outer_step_valid _ word (cleared_valid x word hx)) (head_width x word hx)

theorem prepared_width (x : State) (word : List Bool) (hx : x.Valid word) : (prepared x).width=x.width :=
  head_width x word hx

theorem prepared_field (x : State) (hz : RadixSemantics.value x.outer.bits≠0) :
    (outerStep (cleared x)).outer.fields 0=frame (headWord x) := by
  change (x.outer.after 0).fields 0=_
  simp only [RecoveryClauseState.State.after,hz,ite_false,Function.update_self]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
