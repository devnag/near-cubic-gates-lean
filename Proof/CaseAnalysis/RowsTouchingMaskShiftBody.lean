import Proof.CaseAnalysis.RowsTouchingMaskShiftData

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (bits : Fin 5→Bool):Action 5 2:=⟨1,
  ![some (bits 0||(bits 1&&bits 3)),some (bits 4),some (bits 2&& !(bits 4)),none,some (bits 1)],
  ![.right,.right,.right,.stay,.stay]⟩
def body : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q bits=>if q=0 then some (action bits) else none

def heads (j : ℕ):Fin 5→ℕ:=![j,j,j,0,0]
def data (picked : Bool) (xs : List Cell) (j : ℕ):Fin 5→List Bool:=
  ![mixed live xs (transformed picked xs) j,mixed current xs (transformed picked xs) j,
    mixed remaining xs (transformed picked xs) j,[picked],[carry xs j]]
def entry (picked : Bool) (xs : List Cell) (j : ℕ) (_out : List Bool):Configuration 5 2:=⟨0,heads j,data picked xs j⟩

theorem body_run (picked : Bool) (xs : List Cell) (j : ℕ) (hj:j<xs.length) (out : List Bool):
    Step body 1 (heads j) (data picked xs j) (heads (j+1)) (data picked xs (j+1)):=by
  let x:=xs.getD j (false,false,false)
  let next:=update picked (carry xs j) x
  have hy:j<(transformed picked xs).length:=by rw [transformed_length];exact hj
  have get:xs[j]=x:=(List.getD_eq_getElem xs (false,false,false) hj).symm
  have read (f : Cell→Bool):readTapeBit (mixed f xs (transformed picked xs) j) j=f x:=
    (mixed_read f xs _ j hj hy.le).trans (congrArg f get)
  have write (f : Cell→Bool):writeTapeBit (mixed f xs (transformed picked xs) j) j (f next)=
      mixed f xs (transformed picked xs) (j+1):=by
    have actual:=mixed_write f xs (transformed picked xs) j hj hy
    rw [transformed_get picked xs j hj] at actual
    exact actual
  have scan:(entry picked xs j out).scanned=![live x,current x,remaining x,picked,carry xs j]:=by
    funext i;fin_cases i
    · exact read live
    · exact read current
    · exact read remaining
    · rfl
    · rfl
  have step:LocalBitMultitape.step body (entry picked xs j out)=some (⟨1,heads (j+1),data picked xs (j+1)⟩ : Configuration 5 2):=by
    change some (applyAction (entry picked xs j out) (action (entry picked xs j out).scanned))=_
    rw [scan]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,action,entry,heads,HeadMove.apply]
    · funext i;fin_cases i
      · exact write live
      · exact write current
      · exact write remaining
      · rfl
      · change writeTapeBit [carry xs j] 0 (current x)=[carry xs (j+1)]
        rw [carry_succ];rfl
  obtain ⟨r,run,rf,_⟩:=(Timed.single (by rfl) step).run (by rfl)
  exact Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.MaskShift
