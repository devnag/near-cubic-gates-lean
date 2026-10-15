import Proof.CaseAnalysis.RecoverySelectorBody
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable {n bound : ℕ} (row : Fin (bound+1))
    (start base C D value limit ref : ℕ) (out skipped tail stack : List Bool)

theorem entry_data_outer :
    (entry (n:=n) row start base C D value limit ref out skipped tail stack).tapes=
      Fin.addCases (m:=41) (n:=1) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (flagCaps C i)
          ((RecoveryBoundedSelectorJoin.entry (n:=n) row start base C D value limit ref out [] skipped tail stack).tapes i))
        (fun _=>List.replicate (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start) true) := by
  rfl

theorem entry_data_join :
    (RecoveryBoundedSelectorJoin.entry (n:=n) row start base C D value limit ref out [] skipped tail stack).tapes=
      Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool)
        (RecoveryBoundedSelectorReset.entry (n:=n) row start base C D value limit ref out [] skipped tail).tapes
        (fun _=>stack) := by
  rfl

theorem entry_data_reset :
    (RecoveryBoundedSelectorReset.entry (n:=n) row start base C D value limit ref out [] skipped tail).tapes=
      Fin.addCases (m:=39) (n:=1) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (RecoveryBoundedSelectorReset.caps C i)
          ((RecoveryBoundedReferenceAppend.entry (n:=n) row start base C value limit ref out [] skipped tail).tapes i))
        (fun _=>List.replicate D false) := by
  funext i
  refine Fin.addCases (m:=39) (n:=1) (fun j=>?_) (fun j=>?_) i
  all_goals simp only [RecoveryBoundedSelectorReset.entry,ZeroPadding.config,
    Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
    Fin.addCases_left,Fin.addCases_right,ZeroPadding.pad_zero]
  rfl

theorem entry_data_reference :
    (RecoveryBoundedReferenceAppend.entry (n:=n) row start base C value limit ref out [] skipped tail).tapes=
      Fin.addCases (m:=37) (n:=2) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (RecoveryBoundedReferenceAppend.caps C i)
          ((RecoveryBoundedNativeGuarded.entry (n:=n) row start base C value limit 0 out []).tapes i))
        ![skipped++frame (List.replicate ref true)++tail,List.replicate C false] := by
  rfl

theorem entry_data_guard :
    (RecoveryBoundedNativeGuarded.entry (n:=n) row start base C value limit 0 out []).tapes=
      Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
        (RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start base C value limit out []).tapes
        (fun _=>[]) := by
  rfl

theorem entry_data_unary :
    (RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start base C value limit out []).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (RecoveryBoundedNativeUnaryBody.data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
          base C value false out [])
        (fun _=>RepairSource.VerifierDecoding.CompareMachine.word limit) := by
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
