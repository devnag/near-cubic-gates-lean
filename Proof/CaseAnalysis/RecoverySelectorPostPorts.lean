import Proof.CaseAnalysis.RecoverySelectorNextPrimitives

/-! Whole-function tape projections for the already executed selector body.
They avoid unfolding controller types or classical tape selections. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value C D ref : ℕ) (out skipped tail stack : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)

theorem post_data :
    (post b row start limit value C D ref out skipped tail stack hblock).tapes=
      Fin.addCases (m:=41) (n:=1) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (flagCaps C i)
          ((RecoveryBoundedSelectorJoin.completeState b row start limit value C D ref out [] skipped tail stack hblock).tapes i))
        (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true) := by
  rfl

theorem join_data :
    (RecoveryBoundedSelectorJoin.completeState b row start limit value C D ref out [] skipped tail stack hblock).tapes=
      install RecoveryBoundedSelectorJoin.slots
        (Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool)
          (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out [] skipped tail hblock).tapes
          (fun _=>stack))
        (RecoveryBoundedSelectorReference.data
          (RecoveryBoundedSelectorJoin.counter b row start limit value hblock+2) C
          (RecoveryBoundedSelectorReference.pushed (RecoveryBoundedSelectorJoin.counter b row start limit value hblock) stack)) := by
  rfl

theorem reset_data :
    (RecoveryBoundedSelectorReset.completeState b row start limit value C D ref out [] skipped tail hblock).tapes=
      Fin.addCases (m:=39) (n:=1) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (RecoveryBoundedSelectorReset.caps C i)
          ((RecoveryBoundedReferenceAppend.completeState b row start limit value C ref out [] skipped tail hblock).tapes i))
        (fun _=>List.replicate D false) := by
  rfl

theorem reference_data :
    (RecoveryBoundedReferenceAppend.completeState b row start limit value C ref out [] skipped tail hblock).tapes=
      Fin.addCases (m:=37) (n:=2) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (RecoveryBoundedReferenceAppend.caps C i)
          ((RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out [] hblock).tapes i))
        ![skipped++frame (List.replicate ref true)++tail,List.replicate C false] := by
  rfl

theorem guard_data :
    (RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out [] hblock).tapes=
      install RecoveryBoundedNativeGuarded.slots
        (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
          (RecoveryBoundedNativeUnaryJoin.completeState row start b.nodes.length C value limit out [] hblock).tapes
          (fun _=>List.replicate ref true))
        (PCPPNativeClauseBank.data
          (RecoveryBoundedNativeFold.values ref (RecoveryBoundedSelectorJoin.counter b row start limit value hblock))
          C (nextOut b row start limit value ref out hblock)) := by
  rfl

theorem unary_data :
    (RecoveryBoundedNativeUnaryJoin.completeState row start b.nodes.length C value limit out [] hblock).tapes=
      install RecoveryBoundedNativeUnaryJoin.foldSlots (fun _=>List.replicate value true)
        (RecoveryBoundedNativeUnaryJoin.finalState row start b.nodes.length C value limit out [] hblock).tapes := by
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop

