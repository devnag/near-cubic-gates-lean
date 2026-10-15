import Proof.Amplification.RecoveryQueryKernel
import Proof.MachineModel.OrdinaryOracleComposeGraph

/-! A literal charged oracle ask followed by one physical answer write.
The input query and every head are retained, including query padding. -/
namespace NearCubicWires.RepairSource.RecoveryQueryAnswer
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine {t : Nat} (answerSlot : Fin t) : Machine t 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q _ => if q.val=1 ∨ q.val=2 then
    some ⟨3,fun i => if i=answerSlot then some (q.val==2) else none,fun _ => .stay⟩ else none

def piece {t : Nat} (answerSlot : Fin t) : Piece t :=
  ⟨4,machine answerSlot,fun q => if q.val=0 then some ⟨1,2⟩ else none⟩

def output {t : Nat} (answerSlot : Fin t) (tapes : Fin t→List Bool) (bit : Bool) :=
  Function.update tapes answerSlot (writeTapeBit (tapes answerSlot) 0 bit)

theorem answer_step {t : Nat} (answerSlot : Fin t) (bit : Bool)
    (heads : Fin t→Nat) (tapes : Fin t→List Bool) (hh : heads answerSlot=0) :
    step (machine answerSlot) (⟨if bit then 2 else 1,heads,tapes⟩ : Configuration t 4)=
      some ⟨3,heads,output answerSlot tapes bit⟩ := by
  classical
  cases bit <;> apply congrArg some <;> apply configuration_ext
  all_goals try rfl
  all_goals
    funext i
    by_cases hi : i=answerSlot
    · subst i; simp [applyAction,output,hh]
    · simp [applyAction,output,hi]

theorem answer_trace {t : Nat} (ports : Ports t) (answerSlot : Fin t)
    (o : Nat→Bool) (heads : Fin t→Nat) (tapes : Fin t→List Bool)
    (bits padding : List Bool) (hq : heads ports.queryTape=0)
    (ha : heads answerSlot=0) (ht : tapes ports.queryTape=frame bits++padding) :
    OrdinaryOracleTrace o (ports.program (piece answerSlot)) ((frame bits).length+2)
      (⟨0,heads,tapes⟩ : Configuration t 4)
      (⟨3,heads,output answerSlot tapes (o (CanonicalBinary.bitsValue bits))⟩ : Configuration t 4) := by
  have ask := OrdinaryOracleStep.ask (oracle:=o) (program:=ports.program (piece answerSlot))
    (⟨0,heads,tapes⟩ : Configuration t 4) bits padding (⟨1,2⟩ : OracleReturn 4)
    rfl rfl hq ht
  have localStep : OrdinaryOracleStep o (ports.program (piece answerSlot)) 1
      (⟨if o (CanonicalBinary.bitsValue bits) then 2 else 1,heads,tapes⟩ : Configuration t 4)
      (⟨3,heads,output answerSlot tapes (o (CanonicalBinary.bitsValue bits))⟩ : Configuration t 4) := by
    refine .local _ _ ?_ ?_ (answer_step answerSlot _ heads tapes ha)
    · cases o (CanonicalBinary.bitsValue bits) <;> rfl
    · cases o (CanonicalBinary.bitsValue bits) <;> rfl
  have h := OrdinaryOracleCompose.trans (single ask) (single localStep)
  exact h

end NearCubicWires.RepairSource.RecoveryQueryAnswer
