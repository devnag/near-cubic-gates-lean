import Proof.Amplification.RecoveryTseitinReferenceInput
import Proof.Amplification.RecoveryTseitinReferenceRun

/-! The complete physical reference producer starts with the actual unary
arity, node position and operands. No encoded reference is supplied as input. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReferences
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def order : List (Fin 4) := [0,1,2,3]
noncomputable def coldMachine := Composition.machine scalarMachine (bankMachine order)
def coldBudget (arity index left right : Nat) :=
  budget arity index left right+1+banksBudget (counts arity index left right) order
def fields (arity index left right : Nat) (k : Fin 4) :=
  ZeroPadding.pad (RecoveryTseitinTautology.Cold.driverCapacity (counts arity index left right k))
    (RepairOrdinary.frame (counts arity index left right k).bits)

private theorem join_ready {s t : Nat} (p : Machine 1062 s) (q : Machine 1062 t)
    (fp fq : Nat) (startData middle : Fin 1062→List Bool) (refs : Fin 4→List Bool)
    (hp : ClockJoin.ReadyRun p fp startData middle)
    (hq : ∃ r,run q fq middle=some r ∧
      (∀ k,r.final.tapes (referenceSlot k)=refs k ∧ r.final.heads (referenceSlot k)=0) ∧ r.steps≤fq) :
    ∃ r,run (Composition.machine p q) (fp+1+fq) startData=some r ∧
      (∀ k,r.final.tapes (referenceSlot k)=refs k ∧ r.final.heads (referenceSlot k)=0) ∧ r.steps≤fp+1+fq := by
  obtain ⟨first,hf,ft,fh,fs⟩:=hp
  obtain ⟨last,hl,lo,ls⟩:=hq
  have he : Composition.restart first.final q.start=initialConfiguration q middle := by
    apply configuration_ext
    · rfl
    · funext j; exact fh j
    · exact ft
  change runFrom q fq (initialConfiguration q middle)=some last at hl
  rw [←he] at hl
  exact ⟨_,Composition.run_join p q fp fq _ first last hf hl,lo,
    Nat.add_le_add (Nat.add_le_add_right fs 1) ls⟩

theorem cold_run (arity index left right : Nat) :
    ∃ r,run coldMachine (coldBudget arity index left right) (coldInput arity index left right)=some r ∧
      (∀ k,r.final.tapes (referenceSlot k)=fields arity index left right k ∧
        r.final.heads (referenceSlot k)=0) ∧ r.steps≤coldBudget arity index left right := by
  apply join_ready scalarMachine (bankMachine order) (budget arity index left right)
    (banksBudget (counts arity index left right) order) (coldInput arity index left right)
    (afterSums arity index left right) (fields arity index left right) (scalar_run arity index left right)
  obtain ⟨r,hr,ho,_hk,hs⟩:=banks_run order (by decide) (counts arity index left right)
    (initialConfiguration (bankMachine order) (afterSums arity index left right))
    (by intros; rfl) (by intro k _ j; exact after_sums_banks arity index left right k j)
  refine ⟨r,hr,?_,hs⟩
  intro k
  exact ho k (by fin_cases k <;> simp [order])

end NearCubicWires.RepairSource.RecoveryTseitinReferences
