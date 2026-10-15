import Proof.Amplification.RecoveryTseitinReferenceDriver
import Proof.Amplification.RecoveryTseitinReferenceCold
import Proof.Amplification.RecoveryTseitinReferenceSequenceCons

/-! The four-reference run retains the first bank's actual capacity and
cleared log, which are consumed by the original node-clause kernel. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem driver_banks_run {z : Nat} (counts : Fin 4→Nat) (ambient : Configuration 1062 z)
    (hh : ∀ k j,ambient.heads (bankSlots k j)=0)
    (ht : ∀ k j,ambient.tapes (bankSlots k j)=RecoveryTseitinTautology.Cold.driversInput (counts k) j) :
    ∃ r,runFrom (bankMachine order) (banksBudget counts order)
      (Composition.restart ambient (bankMachine order).start)=some r ∧
      (∀ k,r.final.tapes (referenceSlot k)=ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (counts k))
        (RepairOrdinary.frame (counts k).bits) ∧ r.final.heads (referenceSlot k)=0) ∧
      r.final.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (counts 0)) true ∧
      r.final.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (counts 0)+1) false ∧
      r.final.heads 17=0 ∧ r.final.heads 18=0 ∧ r.steps≤banksBudget counts order := by
  obtain ⟨first,hf,f0,fh0,f3,f4,fh3,fh4,fs,fkeep⟩:=part_driver_run 0 (counts 0) ambient (hh 0) (ht 0)
  have hne (k : Fin 4) (hk : k∈([1,2,3] : List (Fin 4))) : (0 : Fin 4)≠k := by
    fin_cases k <;> simp_all
  obtain ⟨last,hl,lo,lk,ls⟩:=banks_run [1,2,3] (by decide) counts first.final
    (by intro k hk j; exact ((fkeep k (hne k hk) j).2).trans (hh k j))
    (by intro k hk j; exact ((fkeep k (hne k hk) j).1).trans (ht k j))
  obtain ⟨r,hr,rt,rh,rs⟩:=Sequence.cons_join referencePart
    (fun k=>RecoveryTseitinTautology.Cold.budget (counts k)) 0 [1,2,3] ambient first last hf hl
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_⟩
  · intro k
    rw [rt,rh]
    by_cases hk : k=0
    · subst k
      exact ⟨(lk 0 (by decide) 0).1.trans f0,(lk 0 (by decide) 0).2.trans fh0⟩
    exact lo k (by fin_cases k <;> simp_all)
  · rw [rt]; exact (lk 0 (by decide) 3).1.trans f3
  · rw [rt]; exact (lk 0 (by decide) 4).1.trans f4
  · rw [rh]; exact (lk 0 (by decide) 3).2.trans fh3
  · rw [rh]; exact (lk 0 (by decide) 4).2.trans fh4
  · rw [rs]
    exact Nat.add_le_add (Nat.add_le_add_right fs 1) ls

end NearCubicWires.RepairSource.RecoveryTseitinReferences
