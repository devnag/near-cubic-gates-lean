import Proof.CaseAnalysis.RowsTouchingTableAppend
import Proof.CaseAnalysis.RowsTouchingOverwrite
import Proof.CaseAnalysis.RowsTouchingPascalReady
import Proof.Amplification.RecoveryScratchErase

/-! One reusable eight-tape Pascal round produces a full row, appends it to
one table, overwrites both prior rows, and clears only the new-row bank.
All driver and reset words are retained for the counted outer loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalBody
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nextSlots : Fin 5→Fin 8:=![0,1,2,3,7]
def appendSlots : Fin 4→Fin 8:=![5,2,6,7]
def leftSlots : Fin 4→Fin 8:=![2,0,4,7]
def rightSlots : Fin 4→Fin 8:=![2,1,4,7]
def clearSlots : Fin 3→Fin 8:=![2,4,7]
noncomputable def next:=RecoveryFocus.machine nextSlots PascalReady.machine
noncomputable def append:=RecoveryFocus.machine appendSlots TableAppend.machine
noncomputable def left:=RecoveryFocus.machine leftSlots RecoveryBoundedTapeCopy.machine
noncomputable def right:=RecoveryFocus.machine rightSlots RecoveryBoundedTapeCopy.machine
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine next append) left) right) clear

def heads (out : List Bool) : Fin 8→ℕ:=![0,0,0,0,0,0,out.length,0]
def data (q C : ℕ) (l r scratch out : List Bool) : Fin 8→List Bool:=
  ![l,r,scratch,CompareMachine.word q,List.replicate (PascalReady.width q) true,
    UnaryTemplate.tape (PascalReady.width q),out,List.replicate C false]
def budget (q : ℕ):=PascalReady.budget q+10*PascalReady.width q+30

theorem body_run (q m C : ℕ) (out : List Bool) (hm:m<q)
    (hnext:PascalNext.budget q+2≤C) (happend:2*PascalReady.width q+6≤C):
    Step machine (budget q) (heads out)
      (data q C (PascalRow.row (q+1) m q) (PascalRow.row (q+1) m q)
        (List.replicate (PascalReady.width q) false) out)
      (heads (out++PascalRow.row (q+1) (m+1) q))
      (data q C (PascalRow.row (q+1) (m+1) q) (PascalRow.row (q+1) (m+1) q)
        (List.replicate (PascalReady.width q) false) (out++PascalRow.row (q+1) (m+1) q)):=by
  let oldRow:=PascalRow.row (q+1) m q
  let newRow:=PascalRow.row (q+1) (m+1) q
  let B:=PascalReady.width q
  let emptyRow:=List.replicate B false
  let appended:=out++newRow
  have oldLen:oldRow.length=B:=PascalRow.row_length (q+1) m q
  have newLen:newRow.length=B:=PascalRow.row_length (q+1) (m+1) q
  have hlog:B+1≤C:=by omega
  have prepared:Step next (PascalReady.budget q) (heads out) (data q C oldRow oldRow emptyRow out)
      (heads out) (data q C oldRow oldRow newRow out):=by
    have focused:=(PascalReady.ready q m C hm hnext).focus nextSlots (by decide) (heads out) (data q C oldRow oldRow emptyRow out)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3 | exact install_slot _ (by decide) _ _ 4
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3 | exact install_slot _ (by decide) _ _ 4
  have appendedStep:Step append (TableAppend.budget B) (heads out) (data q C oldRow oldRow newRow out)
      (heads appended) (data q C oldRow oldRow newRow appended):=by
    have focused:=(TableAppend.append_run newRow out C (by rw [newLen];exact happend)).focus appendSlots (by decide) (heads out) (data q C oldRow oldRow newRow out)
    rw [newLen] at focused
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1 | exact dockH_slot _ (by decide) _ _ 2 | exact dockH_slot _ (by decide) _ _ 3
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot _ (by decide) _ _ 0 | exact dockH_slot _ (by decide) _ _ 1 | exact dockH_slot _ (by decide) _ _ 2 | exact dockH_slot _ (by decide) _ _ 3
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
  have leftStep:Step left (2*B+4) (heads appended) (data q C oldRow oldRow newRow appended)
      (heads appended) (data q C newRow oldRow newRow appended):=by
    have focused:=(Step.of_ready (Overwrite.ready newRow oldRow B C newLen oldLen.le hlog)).focus leftSlots (by decide) (heads appended) (data q C oldRow oldRow newRow appended)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
  have rightStep:Step right (2*B+4) (heads appended) (data q C newRow oldRow newRow appended)
      (heads appended) (data q C newRow newRow newRow appended):=by
    have focused:=(Step.of_ready (Overwrite.ready newRow oldRow B C newLen oldLen.le hlog)).focus rightSlots (by decide) (heads appended) (data q C newRow oldRow newRow appended)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2 | exact install_slot _ (by decide) _ _ 3
  have cleared:Step clear (2*B+4) (heads appended) (data q C newRow newRow newRow appended)
      (heads appended) (data q C newRow newRow emptyRow appended):=by
    have erased:=RecoveryScratchErase.erase_ready B C (fun _ : Fin 1=>newRow) (by intro i;exact newLen.le)
    rw [Nat.max_eq_left hlog] at erased
    have focused:=(Step.of_ready erased).focus clearSlots (by decide) (heads appended)
      (data q C newRow newRow newRow appended)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot _ (by decide) _ _ 0 | exact install_slot _ (by decide) _ _ 1 | exact install_slot _ (by decide) _ _ 2
  have all:=(((prepared.seq appendedStep).seq leftStep).seq rightStep).seq cleared
  have time:PascalReady.budget q+1+TableAppend.budget B+1+(2*B+4)+1+(2*B+4)+1+(2*B+4)=budget q:=by
    unfold budget TableAppend.budget
    dsimp only [B]
    omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.PascalBody
