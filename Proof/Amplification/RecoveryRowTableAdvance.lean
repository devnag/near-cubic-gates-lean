import Proof.Amplification.RecoveryRowReadChecked
import Proof.Amplification.RecoveryEraseWidth

/-! Actual increment of the checked-prior-row unary driver. Entry and exit
positioning are paid, and every unrelated cursor remains at its position. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverMove (move : HeadMove) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun _=>move⟩ else none

theorem driver_move_run (move : HeadMove) (pos : Nat) (tape : List Bool) :
    ∃ r,runFrom (driverMove move) 1 (⟨0,fun _=>pos,fun _=>tape⟩ : Configuration 1 2)=some r ∧
      r.final=⟨1,fun _=>move.apply pos,fun _=>tape⟩ ∧ r.steps=1 := by
  have h : step (driverMove move) (⟨0,fun _=>pos,fun _=>tape⟩ : Configuration 1 2)=
      some (⟨1,fun _=>move.apply pos,fun _=>tape⟩ : Configuration 1 2) := by
    rfl
  exact (Timed.single (by rfl) h).run (by rfl)

noncomputable def driverCore := Composition.machine (driverMove .right) RecoveryEraseWidth.incrementMachine
noncomputable def driverMachine := Composition.machine driverCore (driverMove .left)

theorem driver_ready (total : Nat) :
    ReadyRun driverMachine (2*total+6) (fun _=>CompareMachine.word total)
      (fun _=>CompareMachine.word (total+1)) := by
  obtain ⟨first,hr0,hf0,hs0⟩ := driver_move_run .right 0 (CompareMachine.word total)
  obtain ⟨middle,hr1,hf1,hs1⟩ := RecoveryEraseWidth.increment_run total
  have he1 : Composition.restart first.final RecoveryEraseWidth.incrementMachine.start=
      RecoveryEraseWidth.cfg 0 total 1 := by rw [hf0]; rfl
  rw [←he1] at hr1
  have hfirst := Composition.run_join (driverMove .right) RecoveryEraseWidth.incrementMachine
    1 (2*total+2) _ first middle hr0 hr1
  obtain ⟨last,hr2,hf2,hs2⟩ := driver_move_run .left 1 (CompareMachine.word (total+1))
  have he2 : Composition.restart (Composition.joinedReceipt first middle).final (driverMove .left).start=
      (⟨0,fun _=>1,fun _=>CompareMachine.word (total+1)⟩ : Configuration 1 2) := by
    change Composition.restart (Composition.rightConfig 2 middle.final) (driverMove .left).start=_
    rw [hf1]; rfl
  rw [←he2] at hr2
  have hall := Composition.run_join driverCore (driverMove .left) (1+1+(2*total+2)) 1
    _ (Composition.joinedReceipt first middle) last hfirst hr2
  have htime : 1+1+(2*total+2)+1+1=2*total+6 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt first middle) last,hall,?_,?_,?_⟩
  · change last.final.tapes=_
    rw [hf2]
  · intro i
    change last.final.heads i=0
    rw [hf2]; rfl
  · change first.steps+1+middle.steps+1+last.steps=2*total+6
    rw [hs0,hs1,hs2]
    omega

def priorSuccessor (x : Children) : Children := {x with total:=x.total+1}
def priorSlot : Fin 1→Fin 68 := fun _=>66
theorem priorSlot_injective : Function.Injective priorSlot := by decide
noncomputable def priorAdvanceMachine := RecoveryFocus.machine priorSlot driverMachine

theorem priorSuccessor_tapes (x : Children) :
    (priorSuccessor x).tapes=Function.update x.tapes 66 (CompareMachine.word (x.total+1)) := by
  funext i
  fin_cases i <;> rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem prior_advance_run (x : Children) :
    ∃ r,runFrom priorAdvanceMachine (2*x.total+6) (x.cfg priorAdvanceMachine.start)=some r ∧
      r.final=(priorSuccessor x).cfg r.final.control ∧ r.steps=2*x.total+6 := by
  obtain ⟨r,hr,hh,ht,hs⟩ := (driver_ready x.total).focus_at priorSlot priorSlot_injective x.heads x.tapes
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  have hi : install priorSlot x.tapes (fun _=>CompareMachine.word (x.total+1))=
      Function.update x.tapes 66 (CompareMachine.word (x.total+1)) := by
    apply install_eq priorSlot priorSlot_injective
    · intro j; fin_cases j; simp [priorSlot]
    · intro i hi
      have hn : i≠66 := by intro he; exact hi 0 he.symm
      simp only [Function.update_of_ne hn]
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht.trans (hi.trans (priorSuccessor_tapes x).symm)

theorem priorSuccessor_valid (x : Children) (word bits : List Bool) (hx : x.Valid word bits)
    (hc : (x.total+1)*(RecoveryRowLookupStream.budget x.bank.row.width+3)+5 ≤ x.lookupCapacity) :
    (priorSuccessor x).Valid word bits :=
  ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hc⟩

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
