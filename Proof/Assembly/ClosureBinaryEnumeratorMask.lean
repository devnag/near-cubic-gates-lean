import Proof.Assembly.ClosureBinaryEnumeratorAssignment
import Proof.Assembly.ClosureFrozenMask

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryEnumerator
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairSource.VerifierDecoding RepairSource.CloseoutFinal

theorem frozen_mask_run {q : Nat} (live : Finset (Fin q))
    (y : BitInput live.card) (D : Nat) (hD : 4*q+3 ≤ D) :
    Step FrozenMask.readyMachine (8*q+8) (![0,0,0,1,0] : Fin 5 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,List.replicate q false,
        CompareMachine.word q,List.replicate D false]
      (![0,0,0,1,0] : Fin 5 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,
        List.ofFn (C10NaturalHardwireScore.frozenMask live y),CompareMachine.word q,
        List.replicate D false] := by
  have h := (FrozenMask.ready_run live y D hD).pad (![0,0,q,0,0] : Fin 5 → Nat)
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals funext i; fin_cases i <;> simp [ZeroPadding.pad]

end NearCubicWires.P1Closure.BinaryEnumerator
