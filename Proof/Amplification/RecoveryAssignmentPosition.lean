import Proof.Amplification.RecoveryAssignmentReturn

/-! Paid entry to each assignment scan: position the retained unary drivers
and clear the reused first-match/result flags on their actual tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryValuationStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clean (d : Data) : Data := {d with found:=false,value:=false}
noncomputable def inputTapes (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool) :=
  (cfg d 0 cap binaryCount committed guard (0 : Fin 1)).tapes

def positionMachine : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=4 ∨ i=5 then some false else none,
    fun i=>if i=2 ∨ i=8 ∨ i=9 then .right else .stay⟩ else none

theorem position_run (d : Data) (cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (hp : d.pos=0) :
    ∃ r,run positionMachine 1 (inputTapes d cap binaryCount committed guard)=some r ∧
      r.final=cfg (clean d) 0 cap binaryCount committed guard (1 : Fin 2) ∧ r.steps=1 := by
  have h : step positionMachine (initialConfiguration positionMachine (inputTapes d cap binaryCount committed guard))=
      some (cfg (clean d) 0 cap binaryCount committed guard (1 : Fin 2)) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rw [cfg_heads]
      funext i
      fin_cases i <;> simp [applyAction,positionMachine,initialConfiguration,HeadMove.apply,clean,hp]
    · rw [cfg_tapes]
      funext i
      fin_cases i <;> simp [applyAction,positionMachine,initialConfiguration,inputTapes,cfg_tapes,clean,writeTapeBit]
  exact (Timed.single (by rfl) h).run (by rfl)

noncomputable def positionedMachine := Composition.machine positionMachine machine

end NearCubicWires.RepairOrdinary.RecoveryAssignment
