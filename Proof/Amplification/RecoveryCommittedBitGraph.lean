import Proof.Amplification.RecoveryCommittedBitTapes

/-! The committed-word bit selection controller is bounded by the word's
physical terminator. Its pure endpoint states the actual destructive binary
counter while retaining the source word and fixed capacities. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCommittedBit
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev graphSizes : Fin 5 → Nat := ![3,7,2,2,2]
def programs : (j : Fin 5) → Machine 5 (graphSizes j)
  | ⟨0,_⟩=>marker
  | ⟨1,_⟩=>predMachine
  | ⟨2,_⟩=>advance
  | ⟨3,_⟩=>writeResult true false
  | ⟨4,_⟩=>writeResult false false
  | ⟨n+5,h⟩=>False.elim (by omega)
def next (j : Fin 5) (q : Fin (graphSizes j)) (scanned : Fin 5 → Bool) : Option (Fin 5) :=
  if j.val=0 then if q.val=1 then some 1 else none else
  if j.val=1 then some (if scanned 1 then 2 else 3) else
  if j.val=2 ∨ j.val=4 then some 0 else none
noncomputable abbrev raw := RecoveryCalls.machine graphSizes programs 4 next
noncomputable abbrev machine := Rewind.machine raw

def finishData : List Bool → Data → Data
  | [],d=>d
  | bit::bits,d=>if value d.query=0 then d.atBit.afterPred.picked bit
    else finishData bits d.atBit.afterPred.atBit

def answer : List Bool → List Bool → Bool
  | [],_=>false
  | bit::bits,query=>if value query=0 then bit else answer bits (RecoveryListPredecessor.result query true)
def bitAt : List Bool → Nat → Bool
  | [],_=>false
  | bit::_,0=>bit
  | _::bits,n+1=>bitAt bits n

theorem bitAt_testBit (bits : List Bool) (index : Nat) : bitAt bits index=(value bits).testBit index := by
  induction bits generalizing index with
  | nil => simp [bitAt,value]
  | cons bit bits ih =>
    have hv : value (bit::bits)=Nat.bit bit (value bits) := by
      cases bit <;> simp [value,Nat.bit,Nat.add_comm]
    rw [hv]
    cases index with
    | zero => simp [bitAt]
    | succ index => simpa only [bitAt,Nat.testBit_bit_succ] using ih index

theorem answer_bitAt (bits query : List Bool) : answer bits query=bitAt bits (value query) := by
  induction bits generalizing query with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hz : value query=0
    · simp [answer,hz,bitAt]
    · rw [answer,if_neg hz,ih,RecoveryListPredecessor.predecessor_value query hz]
      cases he : value query with
      | zero => contradiction
      | succ index => rfl

theorem finish_result (bits : List Bool) (d : Data) (h : d.result=false) :
    (finishData bits d).result=answer bits d.query := by
  induction bits generalizing d with
  | nil => exact h
  | cons bit bits ih =>
    by_cases hz : value d.query=0
    · simp only [finishData,answer,hz,↓reduceIte,Data.picked]
    · simp only [finishData,answer,hz,↓reduceIte]
      exact ih d.atBit.afterPred.atBit h

theorem finish_query_length (bits : List Bool) (d : Data) :
    (finishData bits d).query.length=d.query.length := by
  induction bits generalizing d with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hz : value d.query=0 <;>
      simp only [finishData,hz,↓reduceIte,Data.picked]
    · exact RecoveryListPredecessor.result_length d.query true
    · exact (ih d.atBit.afterPred.atBit).trans (RecoveryListPredecessor.result_length d.query true)

theorem finish_source (bits : List Bool) (d : Data) : (finishData bits d).source=d.source := by
  induction bits generalizing d with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hz : value d.query=0 <;>
      simp only [finishData,hz,↓reduceIte,Data.picked]
    · rfl
    · exact ih d.atBit.afterPred.atBit

theorem finish_capacity (bits : List Bool) (d : Data) : (finishData bits d).capacity=d.capacity := by
  induction bits generalizing d with
  | nil => rfl
  | cons bit bits ih =>
    by_cases hz : value d.query=0 <;>
      simp only [finishData,hz,↓reduceIte,Data.picked]
    · rfl
    · exact ih d.atBit.afterPred.atBit

end NearCubicWires.RepairOrdinary.RecoveryCommittedBit
