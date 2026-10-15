import Proof.Amplification.RecoveryTseitinColdState
import Proof.Amplification.RecoveryTseitinReferenceRun

/-! The target-reference bank also supplies the already paid capacity driver
and cleared log needed by the exact original node-clause kernel. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem part_driver_run {z : Nat} (k : Fin 4) (count : Nat) (ambient : Configuration 1062 z)
    (hh : ∀ j,ambient.heads (bankSlots k j)=0)
    (ht : ∀ j,ambient.tapes (bankSlots k j)=RecoveryTseitinTautology.Cold.driversInput count j) :
    ∃ r,runFrom (referencePart k) (RecoveryTseitinTautology.Cold.budget count)
      (Composition.restart ambient (referencePart k).start)=some r ∧
      r.final.tapes (referenceSlot k)=ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity count)
        (RepairOrdinary.frame count.bits) ∧ r.final.heads (referenceSlot k)=0 ∧
      r.final.tapes (bankSlots k 3)=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity count) true ∧
      r.final.tapes (bankSlots k 4)=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity count+1) false ∧
      r.final.heads (bankSlots k 3)=0 ∧ r.final.heads (bankSlots k 4)=0 ∧
      r.steps≤RecoveryTseitinTautology.Cold.budget count ∧
      (∀ l,k≠l → ∀ j,r.final.tapes (bankSlots l j)=ambient.tapes (bankSlots l j) ∧
        r.final.heads (bankSlots l j)=ambient.heads (bankSlots l j)) := by
  obtain ⟨base,hb,b0,b3,b4,bh0,bh3,bh4,bs⟩:=RecoveryTseitinTautology.Cold.reference_driver_run count
  obtain ⟨r,hr,_rc,rs,rh,rt,ro⟩:=RecoveryFocus.dock (bankSlots k) (bank_injective k)
    RecoveryTseitinTautology.Cold.machine _ ambient.heads ambient.tapes _ hh ht base hb
  refine ⟨r,hr,(rt 0).trans b0,(rh 0).trans bh0,(rt 3).trans b3,(rt 4).trans b4,
    (rh 3).trans bh3,(rh 4).trans bh4,rs.le.trans bs,?_⟩
  intro l hkl j
  have h:=ro (bankSlots l j) (by intro a; exact disjoint k l hkl a j)
  exact ⟨h.2,h.1⟩

end NearCubicWires.RepairSource.RecoveryTseitinReferences
