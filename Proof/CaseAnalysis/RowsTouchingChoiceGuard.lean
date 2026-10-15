import Proof.CaseAnalysis.RowsTouchingGateFoldLayout

/-! The original k=0 branch is read from the actual padded counter. It
forces the physical comparison flag false and preserves the counter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ChoiceGuard
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,![.right,.stay]⟩
    else if q=1 then some ⟨2,![none,some (bits 0&&bits 1)],![.left,.stay]⟩ else none

def data (k P : ℕ) (old : Bool):Fin 2→List Bool:=![ZeroPadding.pad P (CompareMachine.word k),[old]]
def cfg (state : Fin 3) (position k P : ℕ) (old : Bool):Configuration 2 3:=⟨state,![position,0],data k P old⟩

theorem guard_run (k P : ℕ) (old : Bool):
    Step machine 2 (fun _=>0) (data k P old) (fun _=>0) (data k P (decide (0<k)&&old)):=by
  have first:step machine (cfg 0 0 k P old)=some (cfg 1 1 k P old):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  have bit:readTapeBit (ZeroPadding.pad P (CompareMachine.word k)) 1=decide (0<k):=by
    rw [ZeroPadding.read_pad]
    exact ClockUnaryProduct.read_sentinel k 0
  have second:step machine (cfg 1 1 k P old)=some (cfg 2 0 k P (decide (0<k)&&old)):=by
    change some (applyAction (cfg 1 1 k P old)
      (⟨2,![none,some (readTapeBit (ZeroPadding.pad P (CompareMachine.word k)) 1&&old)],![.left,.stay]⟩:
        Action 2 3))=_
    rw [bit]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,run,rf,_⟩:=((Timed.single (by rfl) first).trans (Timed.single (by rfl) second)).run (by rfl)
  have actual:=Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact actual.congr_in (by funext i;fin_cases i <;> rfl) rfl |>.congr
    (by funext i;fin_cases i <;> rfl) rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ChoiceGuard
