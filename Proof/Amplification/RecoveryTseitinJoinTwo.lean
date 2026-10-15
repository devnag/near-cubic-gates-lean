import Proof.Amplification.RecoveryTseitinNativeReusePrefix

/-! Preserve abstract controller sizes while joining large concrete native
machines, exposing only the endpoint projections needed by their consumer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem join_two {t a b : Nat} (first : Machine t a) (second : Machine t b)
    (f g : Nat) (initial : Configuration t a) (x : ExecutionReceipt t a) (y : ExecutionReceipt t b)
    (hx : runFrom first f initial=some x)
    (hy : runFrom second g (Composition.restart x.final second.start)=some y) :
    ∃ r,runFrom (Composition.machine first second) (f+1+g) (Composition.leftConfig b initial)=some r ∧
      r.final.heads=y.final.heads ∧ r.final.tapes=y.final.tapes ∧ r.steps=x.steps+1+y.steps :=
  ⟨Composition.joinedReceipt x y,Composition.run_join first second f g initial x y hx hy,rfl,rfl,rfl⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative
