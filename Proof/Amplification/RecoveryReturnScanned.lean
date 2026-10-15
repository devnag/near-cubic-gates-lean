import Proof.Amplification.RecoveryAllCodeCall

/-! One paid finite transition returns a fixed Boolean predicate of the
currently scanned tape cells. The cold verifier uses the conjunction of
its retained parsing gate and the executed checker result. -/
namespace NearCubicWires.RepairOrdinary.RecoveryReturnScanned
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine {t : Nat} (accept : (Fin t→Bool)→Bool) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val != 0
  rule := fun q bits=>if q.val=0 then
    some ⟨RecoveryReturnBit.code (accept bits),fun _=>none,fun _=>.stay⟩ else none

theorem flag_run {t : Nat} (accept : (Fin t→Bool)→Bool)
    (heads : Fin t→Nat) (tapes : Fin t→List Bool) :
    ∃ r,runFrom (flagMachine accept) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=⟨RecoveryReturnBit.code (accept (fun i=>readTapeBit (tapes i) (heads i))),heads,tapes⟩ ∧
      r.steps=1 := by
  let bit := accept (fun i=>readTapeBit (tapes i) (heads i))
  have hs : step (flagMachine accept) ⟨0,heads,tapes⟩=
      some (⟨RecoveryReturnBit.code bit,heads,tapes⟩ : Configuration t 3) := by rfl
  exact (Timed.single (by rfl) hs).run (by cases bit <;> rfl)

def machine {t s : Nat} (p : Machine t s) (accept : (Fin t→Bool)→Bool) :=
  Composition.machine p (flagMachine accept)

theorem finish_run {t s : Nat} (p : Machine t s) (accept : (Fin t→Bool)→Bool) (fuel : Nat)
    (source : Configuration t s) (first : ExecutionReceipt t s)
    (hr : runFrom p fuel source=some first) :
    ∃ r,runFrom (machine p accept) (fuel+2) (Composition.leftConfig 3 source)=some r ∧
      RecoveryReturnBit.accepting s r.final.control=accept first.final.scanned := by
  obtain ⟨last,hl,hf,_⟩ := flag_run accept first.final.heads first.final.tapes
  have hj := Composition.run_join p (flagMachine accept) fuel 1 source first last hr hl
  rw [show fuel+1+1=fuel+2 by omega] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_⟩
  simp only [Composition.joinedReceipt,Composition.rightConfig,hf,
    RecoveryReturnBit.accepting,Fin.addCases_right]
  change ((RecoveryReturnBit.code (accept first.final.scanned)).val==1)=accept first.final.scanned
  cases accept first.final.scanned <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryReturnScanned
