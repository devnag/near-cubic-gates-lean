import Proof.Amplification.RecoveryTseitinReferenceSequence

/-! Execute the fixed reference banks, retaining earlier canonical references
and the actual heads on every disjoint bank. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bankMachine (ks : List (Fin 4)) := Sequence.bankMachine referencePart ks
def banksBudget (counts : Fin 4→Nat) (ks : List (Fin 4)) :=
  Sequence.banksBudget (fun k=>RecoveryTseitinTautology.Cold.budget (counts k)) ks

theorem banks_run {z : Nat} (ks : List (Fin 4)) (hn : ks.Nodup)
    (counts : Fin 4→Nat) (ambient : Configuration 1062 z)
    (hh : ∀ k∈ks,∀ j,ambient.heads (bankSlots k j)=0)
    (ht : ∀ k∈ks,∀ j,ambient.tapes (bankSlots k j)=RecoveryTseitinTautology.Cold.driversInput (counts k) j) :
    ∃ r,runFrom (bankMachine ks) (banksBudget counts ks)
      (Composition.restart ambient (bankMachine ks).start)=some r ∧
      (∀ k∈ks,r.final.tapes (referenceSlot k)=
        ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (counts k))
          (RepairOrdinary.frame (counts k).bits) ∧ r.final.heads (referenceSlot k)=0) ∧
      (∀ l,l∉ks → ∀ j,r.final.tapes (bankSlots l j)=ambient.tapes (bankSlots l j) ∧
        r.final.heads (bankSlots l j)=ambient.heads (bankSlots l j)) ∧
      r.steps≤banksBudget counts ks :=
  Sequence.banks_run referencePart (fun k=>RecoveryTseitinTautology.Cold.budget (counts k))
    (fun k=>RecoveryTseitinTautology.Cold.driversInput (counts k))
    (fun k=>ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (counts k))
      (RepairOrdinary.frame (counts k).bits))
    (fun k ambient hh ht=>part_run k (counts k) ambient hh ht) ks hn ambient hh ht

end NearCubicWires.RepairSource.RecoveryTseitinReferences
