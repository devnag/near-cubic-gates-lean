import Proof.Amplification.RecoveryTseitinReferenceDriverBanks

/-! The actual cold reference supplier also retains the target bank's paid
capacity and cleared log for immediate clause generation. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem ready_join {s t : Nat} (p : Machine 1062 s) (q : Machine 1062 t)
    (fp fq : Nat) (startData middle : Fin 1062→List Bool)
    (hp : ClockJoin.ReadyRun p fp startData middle) (last : ExecutionReceipt 1062 t)
    (hl : run q fq middle=some last) (ls : last.steps≤fq) :
    ∃ r,run (Composition.machine p q) (fp+1+fq) startData=some r ∧
      r.final.tapes=last.final.tapes ∧ r.final.heads=last.final.heads ∧ r.steps≤fp+1+fq := by
  obtain ⟨first,hf,ft,fh,fs⟩:=hp
  have he : Composition.restart first.final q.start=initialConfiguration q middle := by
    apply configuration_ext
    · rfl
    · funext i; exact fh i
    · exact ft
  change runFrom q fq (initialConfiguration q middle)=some last at hl
  rw [←he] at hl
  exact ⟨_,Composition.run_join p q fp fq _ first last hf hl,rfl,rfl,
    Nat.add_le_add (Nat.add_le_add_right fs 1) ls⟩

theorem cold_driver_run (arity index left right : Nat) : ∃ r,
    run coldMachine (coldBudget arity index left right) (coldInput arity index left right)=some r ∧
      (∀ k,r.final.tapes (referenceSlot k)=fields arity index left right k ∧ r.final.heads (referenceSlot k)=0) ∧
      r.final.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)) true ∧
      r.final.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)+1) false ∧
      r.final.heads 17=0 ∧ r.final.heads 18=0 ∧ r.steps≤coldBudget arity index left right := by
  obtain ⟨last,hl,lo,ld,ll,ldh,llh,ls⟩:=driver_banks_run (counts arity index left right)
    (initialConfiguration (bankMachine order) (afterSums arity index left right))
    (by intros; rfl) (after_sums_banks arity index left right)
  obtain ⟨r,hr,rt,rh,rs⟩:=ready_join scalarMachine (bankMachine order) (budget arity index left right)
    (banksBudget (counts arity index left right) order) (coldInput arity index left right)
    (afterSums arity index left right) (scalar_run arity index left right) last hl ls
  refine ⟨r,hr,?_,?_,?_,?_,?_,rs⟩
  · intro k; rw [rt,rh]; exact lo k
  · rw [rt]; exact ld
  · rw [rt]; exact ll
  · rw [rh]; exact ldh
  · rw [rh]; exact llh

end NearCubicWires.RepairSource.RecoveryTseitinReferences
