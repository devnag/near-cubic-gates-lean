import Proof.Amplification.RecoveryClauseEvaluationReader

/-! The three literal positions use fixed nodes of the one clause graph.
These are static routing equalities; all dynamic validity choices read the
actual result tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decodeNode (which : Fin 3) : Fin 13 := ⟨2+3*which.val,by omega⟩
def lookupNode (which : Fin 3) : Fin 13 := ⟨3+3*which.val,by omega⟩
def truthNode (which : Fin 3) : Fin 13 := ⟨4+3*which.val,by omega⟩
def continuationNode (which : Fin 3) : Fin 13 := ⟨5+3*which.val,by omega⟩

theorem decode_program_ready (which : Fin 3) (s : State) (e : Extra) (word : List Bool)
    (hs : s.Valid) (hl : word.length=s.bits.length) (hf : s.fields which=frame word) :
    ReadyRun (programs (decodeNode which)) (RecoveryCheckedLiteral.time word) (tapes s e)
      (tapes (RecoveryCheckedLiteral.checkedState s which word) e) := by
  fin_cases which <;> exact decode_ready s e _ word hs hl hf

theorem lookup_program_ready (which : Fin 3) (n : Nat) (input output : Fin 42→List Bool)
    (h : ReadyRun (assignmentMachine which) n input output) :
    ReadyRun (programs (lookupNode which)) n input output := by
  fin_cases which <;> exact h

theorem truth_program_ready (which : Fin 3) (s : State) (e : Extra) :
    ReadyRun (programs (truthNode which)) 1 (tapes s e) (tapes (truthState s e) (truthExtra s e)) := by
  fin_cases which <;> exact truth_ready s e

theorem decode_next (which : Fin 3) (q : Fin (sizes (decodeNode which))) (bits : Fin 42→Bool) :
    next (decodeNode which) q bits=some (if bits 27 then lookupNode which else 12) := by
  fin_cases which <;> rfl

theorem lookup_next (which : Fin 3) (q : Fin (sizes (lookupNode which))) (bits : Fin 42→Bool) :
    next (lookupNode which) q bits=some (if bits 34 then truthNode which else 12) := by
  fin_cases which <;> rfl

theorem truth_next (which : Fin 3) (q : Fin (sizes (truthNode which))) (bits : Fin 42→Bool) :
    next (truthNode which) q bits=some (continuationNode which) := by
  fin_cases which <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
