import Proof.Supplier.RowFieldPadding
import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.Layout

/-! Widen the actual binary table value to the accumulator width. The
existing counted framed copier writes every added zero bit; the old
scalar backing is cleared with the same paid field-length driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreWiden
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 3→Fin 5:=![1,4,3]
def copySlots (i : Fin 4):Fin 5:=i.castAdd 1
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copy:=RecoveryFocus.machine copySlots RecoveryColdPaddedCopy.machine
noncomputable def machine:=Composition.machine erase copy
def input (b w C x : ℕ) (backing : List Bool):Fin 5→List Bool:=
  ![frame (binary b x),backing,CompareMachine.word w,List.replicate C false,List.replicate (2*w+1) true]

theorem copy_run (b w C x : ℕ) (hw:b≤w) (hx:x<2^b) (hC:2*w+3≤C):
    Step RecoveryColdPaddedCopy.machine (4*w+8) (fun _=>0)
      ![frame (binary b x),List.replicate (2*w+1) false,CompareMachine.word w,List.replicate C false]
      (fun _=>0) ![frame (binary b x),frame (binary w x),CompareMachine.word w,List.replicate C false]:=by
  have actual:=Step.of_ready (RecoveryColdPaddedCopy.copy_ready (binary b x) w)
  have value:RecoveryColdPaddedCopy.data (binary b x) w=binary w x:=by
    rw [RecoveryColdPaddedCopy.data_eq_pad _ _ (by simpa using hw),binary_length]
    exact RowFieldPadding.binary_extend b w x hw hx
  let caps : Fin 4→ℕ:=![0,2*w+1,0,C]
  have padded:=actual.pad caps
  refine padded.congr_in rfl ?_ |>.congr rfl ?_
  · funext i;fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _
  · funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · change ZeroPadding.pad (2*w+1) (frame (RecoveryColdPaddedCopy.data (binary b x) w))=frame (binary w x)
      rw [value]
      simp [ZeroPadding.pad]
    · exact ZeroPadding.pad_zero _
    · exact pad_replicate_false _ _ hC

theorem widen_run (b w C x : ℕ) (backing : List Bool) (hw:b≤w) (hx:x<2^b)
    (hb:backing.length≤2*w+1) (hC:2*w+3≤C):
    Step machine (8*w+15) (fun _=>0) (input b w C x backing)
      (fun _=>0) (input b w C x (frame (binary w x))):=by
  have erased:=Step.of_ready (RecoveryScratchErase.erase_ready (2*w+1) C
    (fun _ : Fin 1=>backing) (by intro i;exact hb))
  rw [Nat.max_eq_left (by omega : 2*w+1+1≤C)] at erased
  have e:Step erase (2*(2*w+1)+4) (fun _=>0) (input b w C x backing)
      (fun _=>0) (input b w C x (List.replicate (2*w+1) false)):=by
    have focused:=erased.focus eraseSlots (by decide) (fun _=>0) (input b w C x backing)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;rfl
    · apply install_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first
      | exact install_other eraseSlots _ _ _ (by decide)
      | exact install_slot eraseSlots (by decide) _ _ 0
      | exact install_slot eraseSlots (by decide) _ _ 1
      | exact install_slot eraseSlots (by decide) _ _ 2
  have c:Step copy (4*w+8) (fun _=>0) (input b w C x (List.replicate (2*w+1) false))
      (fun _=>0) (input b w C x (frame (binary w x))):=by
    have focused:=(copy_run b w C x hw hx hC).focus copySlots (by decide) (fun _=>0)
      (input b w C x (List.replicate (2*w+1) false))
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;rfl
    · apply install_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first
      | exact install_slot copySlots (by decide) _ _ 0
      | exact install_slot copySlots (by decide) _ _ 1
      | exact install_slot copySlots (by decide) _ _ 2
      | exact install_slot copySlots (by decide) _ _ 3
      | exact install_other copySlots _ _ _ (by decide)
  exact (e.seq c).enlarge (by omega)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.ScoreWiden
