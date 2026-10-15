import Proof.Amplification.RecoveryCheckedLiteralState

/-! Shared clause-evaluation storage: the three saved literal fields remain
in the existing decoder, while one retained valuation source and accumulator
serve all three calls. The decoder's erase driver/reset tape are shared. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Extra where
  source : List Bool
  row : List Bool
  counter : List Bool
  binaryCount : List Bool
  committed : List Bool
  found : Bool
  value : Bool
  valid : Bool
  guard : Bool
  aggregate : Bool
  cap : Nat
  prefixLimit : Nat

def Extra.tapes (e : Extra) (s : State) : Fin 14→List Bool :=
  ![e.source,e.row,CompareMachine.word (s.bits.length+1),[e.found],[e.value],
    List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.valid],e.counter,
    CompareMachine.word e.cap,frame e.binaryCount,frame e.committed,[e.guard],
    List.replicate (RecoveryReusableUnpair.capacity s.bits) false,[e.aggregate]]
def tapes (s : State) (e : Extra) : Fin 42→List Bool :=
  fun i=>Fin.addCases s.tapes (e.tapes s) i

def assignmentData (s : State) (e : Extra) (index word : List Bool) : RecoveryValuationStream.Data :=
  ⟨frame (word.take e.prefixLimit),0,s.bits.length,index,e.row,e.found,e.value,e.valid,
    RecoveryReusableUnpair.capacity s.bits⟩
def assignmentSlots (which : Fin 3) : Fin 16→Fin 42 :=
  ![28,29,30,(savedSlot which).castAdd 14,31,32,33,34,35,36,37,38,39,40,22,21]
theorem assignmentSlots_injective (which : Fin 3) : Function.Injective (assignmentSlots which) := by
  fin_cases which <;> decide
noncomputable def assignmentMachine (which : Fin 3) := RecoveryFocus.machine (assignmentSlots which) RecoveryAssignment.reusableMachine
noncomputable def decodeMachine (which : Fin 3) := TapeEmbedding.machine 14 (RecoveryCheckedLiteral.machine which)
def truthSlots : Fin 5→Fin 42 := ![23,32,41,27,34]
noncomputable def truthMachine := RecoveryFocus.machine truthSlots RecoveryLiteralTruth.machine

theorem assignment_input (s : State) (e : Extra) (which : Fin 3) (index word : List Bool)
    (hf : s.fields which=frame index)
    (hs : e.source=ZeroPadding.pad (2*e.prefixLimit+1) (frame (word.take e.prefixLimit))) (j : Fin 16) :
    tapes s e (assignmentSlots which j)=
      RecoveryAssignment.reuseInput (assignmentData s e index word) e.cap e.binaryCount e.committed e.guard
        (2*e.prefixLimit+1) (RecoveryReusableUnpair.capacity s.bits) s.capacity e.counter j := by
  fin_cases j <;>
    simp [tapes,Extra.tapes,assignmentSlots,RecoveryAssignment.reuseInput,RecoveryAssignment.reuseTapes,
      RecoveryAssignment.readyTapes,RecoveryAssignment.paddedTapes,RecoveryAssignment.padding,
      RecoveryAssignment.cfg_tapes,assignmentData,Fin.addCases,hs]
  case «3» =>
    exact hf
  all_goals rfl

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
