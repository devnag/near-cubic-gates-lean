import Proof.Amplification.RecoveryClauseEvaluationSemantics

/-! One fixed thirteen-node ordinary clause controller: clear, read exactly
three cells, decode/lookup/OR each literal, and physically write the final
answer. Shape, tag and table failures take the explicit rejection node. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundaryMachine (mode : Fin 3) : Machine 42 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    (fun i=>if i=27 then some (if mode=1 then bits 41 else false)
      else if mode=0 ∧ i=41 then some false else none),fun _=>.stay⟩ else none

abbrev machineStates {t n : Nat} (_ : Machine t n) : Nat := n
noncomputable abbrev readerStates := machineStates RecoveryThreeCellReader.machine
noncomputable abbrev decoderStates := machineStates (decodeMachine 0)
noncomputable abbrev lookupStates := machineStates (assignmentMachine 0)
noncomputable def sizes : Fin 13→Nat :=
  ![2,readerStates,decoderStates,lookupStates,2,decoderStates,lookupStates,2,
    decoderStates,lookupStates,2,2,2]
noncomputable def programs : (j : Fin 13)→Machine 42 (sizes j)
  | ⟨0,_⟩ => boundaryMachine 0
  | ⟨1,_⟩ => TapeEmbedding.machine 14 RecoveryThreeCellReader.machine
  | ⟨2,_⟩ => decodeMachine 0
  | ⟨3,_⟩ => assignmentMachine 0
  | ⟨4,_⟩ => truthMachine
  | ⟨5,_⟩ => decodeMachine 1
  | ⟨6,_⟩ => assignmentMachine 1
  | ⟨7,_⟩ => truthMachine
  | ⟨8,_⟩ => decodeMachine 2
  | ⟨9,_⟩ => assignmentMachine 2
  | ⟨10,_⟩ => truthMachine
  | ⟨11,_⟩ => boundaryMachine 1
  | ⟨12,_⟩ => boundaryMachine 2
  | ⟨n+13,h⟩ => False.elim (by omega)
def next (j : Fin 13) (_ : Fin (sizes j)) (bits : Fin 42→Bool) : Option (Fin 13) :=
  match j.val with
  | 0 => some 1
  | 1 => some (if bits 27 then 2 else 12)
  | 2 => some (if bits 27 then 3 else 12)
  | 3 => some (if bits 34 then 4 else 12)
  | 4 => some 5
  | 5 => some (if bits 27 then 6 else 12)
  | 6 => some (if bits 34 then 7 else 12)
  | 7 => some 8
  | 8 => some (if bits 27 then 9 else 12)
  | 9 => some (if bits 34 then 10 else 12)
  | 10 => some 11
  | _ => none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
