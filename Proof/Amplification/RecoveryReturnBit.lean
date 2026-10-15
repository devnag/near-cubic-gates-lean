import Proof.Amplification.RecoveryAllCodeCanonicalJoin

/-! Converting the checked Boolean cell into actual accepting/rejecting
finite control takes one local transition. Sequential handoff pays another. -/
namespace NearCubicWires.RepairOrdinary.RecoveryReturnBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (bit : Bool) : Fin 3 := if bit then 1 else 2
def flagMachine {t : Nat} (a : Fin t) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val != 0
  rule := fun q bits=>if q.val=0 then some ⟨code (bits a),fun _=>none,fun _=>.stay⟩ else none

theorem flag_run {t : Nat} (a : Fin t) (heads : Fin t→Nat) (tapes : Fin t→List Bool)
    (bit : Bool) (hh : heads a=0) (ht : tapes a=[bit]) :
    ∃ r,runFrom (flagMachine a) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=⟨code bit,heads,tapes⟩ ∧ r.steps=1 := by
  have hbit : (⟨0,heads,tapes⟩ : Configuration t 3).scanned a=bit := by
    change readTapeBit (tapes a) (heads a)=bit
    rw [hh,ht]
    rfl
  have hs : step (flagMachine a) ⟨0,heads,tapes⟩=some (⟨code bit,heads,tapes⟩ : Configuration t 3) := by
    change some (⟨code ((⟨0,heads,tapes⟩ : Configuration t 3).scanned a),heads,tapes⟩ : Configuration t 3)=_
    rw [hbit]
  exact (Timed.single (by rfl) hs).run (by cases bit <;> rfl)

def machine {t s : Nat} (p : Machine t s) (a : Fin t) := Composition.machine p (flagMachine a)
def accepting (s : Nat) : Fin (s+3)→Bool :=
  Fin.addCases (m:=s) (n:=3) (motive:=fun _=>Bool) (fun _=>false) (fun q=>q.val==1)

theorem finish_run {t s : Nat} (p : Machine t s) (a : Fin t) (fuel : Nat)
    (source : Configuration t s) (first : ExecutionReceipt t s)
    (hr : runFrom p fuel source=some first) (bit : Bool)
    (hh : first.final.heads a=0) (ht : first.final.tapes a=[bit]) :
    ∃ r,runFrom (machine p a) (fuel+2) (Composition.leftConfig 3 source)=some r ∧
      accepting s r.final.control=bit := by
  obtain ⟨last,hl,hf,_⟩ := flag_run a first.final.heads first.final.tapes bit hh ht
  have hj := Composition.run_join p (flagMachine a) fuel 1 source first last hr hl
  rw [show fuel+1+1=fuel+2 by omega] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_⟩
  simp only [Composition.joinedReceipt,Composition.rightConfig,hf,accepting,Fin.addCases_right]
  cases bit <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryReturnBit
