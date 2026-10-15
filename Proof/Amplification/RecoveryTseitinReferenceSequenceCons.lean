import Proof.Amplification.RecoveryTseitinReferenceSequence

/-! One abstract sequence step at the strengthened capacity consumer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences.Sequence
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cons_join {s z : Nat} (parts : Fin 4→Machine 1062 s) (cost : Fin 4→Nat)
    (k : Fin 4) (ks : List (Fin 4)) (ambient : Configuration 1062 z)
    (first : ExecutionReceipt 1062 s) (last : ExecutionReceipt 1062 (bankStates s ks))
    (hf : runFrom (parts k) (cost k) (Composition.restart ambient (parts k).start)=some first)
    (hl : runFrom (bankMachine parts ks) (banksBudget cost ks)
      (Composition.restart first.final (bankMachine parts ks).start)=some last) :
    ∃ r,runFrom (bankMachine parts (k::ks)) (banksBudget cost (k::ks))
      (Composition.restart ambient (bankMachine parts (k::ks)).start)=some r ∧
      r.final.tapes=last.final.tapes ∧ r.final.heads=last.final.heads ∧ r.steps=first.steps+1+last.steps :=
  ⟨_,Composition.run_join (parts k) (bankMachine parts ks) _ _ _ first last hf hl,rfl,rfl,rfl⟩

end NearCubicWires.RepairSource.RecoveryTseitinReferences.Sequence
