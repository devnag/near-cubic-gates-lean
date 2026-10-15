import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.NativeFanoutReusable
import Proof.MachineModel.Layout

/-! Reusable hardwired-child scratch: erase arbitrary bounded targets and
reload their exact padded templates from retained masters. The consumer is
the next hardwired-child call; masters, erase driver and reset log are explicit
inputs. This construction neither produces those inputs nor closes the loop. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.TemplateRestore
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound

def slots (k : Nat) (i : Fin (k+1+1)) : Fin (k+(k+1)+1) := ⟨k+i.val,by omega⟩
theorem slots_injective (k : Nat) : Function.Injective (slots k) := by
  intro i j h
  have h := congrArg Fin.val h
  apply Fin.ext
  simp only [slots] at h
  omega

theorem slots_left (k : Nat) (i : Fin (k+1)) :
    slots k (i.castAdd 1) = (i.natAdd k).castAdd 1 := by apply Fin.ext; rfl
theorem slots_right (k : Nat) (i : Fin 1) :
    slots k (i.natAdd (k+1)) = i.natAdd (k+(k+1)) := by
  apply Fin.ext
  simp only [slots,Fin.val_natAdd]
  omega

def pack {k : Nat} (masters : Fin k → List Bool) (tail : Fin (k+1+1) → List Bool) :
    Fin (k+(k+1)+1) → List Bool :=
  Fin.addCases (Fin.addCases masters (fun i=>tail (i.castAdd 1)))
    (fun i=>tail (i.natAdd (k+1)))

theorem pack_slot {k : Nat} (masters : Fin k → List Bool)
    (tail : Fin (k+1+1) → List Bool) (i : Fin (k+1+1)) :
    pack masters tail (slots k i)=tail i := by
  refine Fin.addCases (m:=k+1) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [slots_left]
    simp only [pack,Fin.addCases_left,Fin.addCases_right]
  · rw [slots_right]
    simp only [pack,Fin.addCases_right]

theorem install_pack {k : Nat} (masters : Fin k → List Bool)
    (before after : Fin (k+1+1) → List Bool) :
    install (slots k) (pack masters before) after = pack masters after := by
  funext i
  refine Fin.addCases (m:=k+(k+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=k) (n:=k+1) (fun j=>?_) (fun j=>?_) j
    · have away (a : Fin (k+1+1)) : slots k a ≠ (j.castAdd (k+1)).castAdd 1 := by
        intro h
        have h := congrArg Fin.val h
        simp only [slots,Fin.val_castAdd] at h
        omega
      rw [install_other _ _ _ _ away]
      simp only [pack,Fin.addCases_left]
    · rw [←slots_left,install_slot _ (slots_injective k),pack_slot]
  · rw [←slots_right,install_slot _ (slots_injective k),pack_slot]

def localInput {k : Nat} (dirty : Fin k → List Bool) (R : Nat) : Fin (k+1+1) → List Bool :=
  Fin.addCases (Fin.addCases dirty (fun _ : Fin 1=>List.replicate R true))
    (fun _ : Fin 1=>List.replicate (R+1) false)
def input {k : Nat} (masters dirty : Fin k → List Bool) (R : Nat) : Fin (k+(k+1)+1) → List Bool :=
  pack masters (localInput dirty R)
noncomputable def first (k : Nat) := RecoveryFocus.machine (slots k) (RecoveryScratchErase.resetMachine k)
noncomputable def machine (k : Nat) := Composition.machine (first k)
  (NativeFanout.machine (fun j : Fin k=>some j))

theorem run {k : Nat} (masters dirty : Fin k → List Bool) (R : Nat)
    (hmasters : ∀ j,(masters j).length≤R) (hdirty : ∀ j,(dirty j).length≤R) :
    Step (machine k) (4*R+9) (fun _=>0) (input masters dirty R)
      (fun _=>0) (NativeFanout.output (fun j=>some j) masters R) := by
  have erased : Step (RecoveryScratchErase.resetMachine k) (2*R+4)
      (fun _=>0) (localInput dirty R) (fun _=>0)
      (localInput (fun _ : Fin k=>List.replicate R false) R) := by
    unfold localInput
    simpa only [Nat.max_self] using
      Step.of_ready (RecoveryScratchErase.erase_ready R (R+1) dirty hdirty)
  have hz : dockH (slots k) (fun _=>0) (fun _=>0) = fun _=>0 :=
    dockH_existing _ _ _ (fun _=>rfl)
  have hin : install (slots k) (input masters dirty R) (localInput dirty R)=input masters dirty R :=
    install_existing _ _ _ (pack_slot masters (localInput dirty R))
  have hout : install (slots k) (input masters dirty R)
      (localInput (fun _ : Fin k=>List.replicate R false) R)=NativeFanout.reusableInput masters R := by
    rw [input,install_pack]
    funext i
    refine Fin.addCases (m:=k+(k+1)) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=k) (n:=k+1) (fun a=>?_) (fun a=>?_) j <;>
        simp only [pack,localInput,NativeFanout.reusableInput,Fin.addCases_left,Fin.addCases_right]
    · simp only [pack,localInput,NativeFanout.reusableInput,Fin.addCases_right]
  have clear := ((erased.focus (slots k) (slots_injective k) (fun _=>0)
    (input masters dirty R)).congr_in hz hin).congr hz hout
  have joined := clear.seq (NativeFanout.reusable (fun j=>some j) masters R hmasters)
  simpa only [machine,first,show 2*R+4+1+(2*R+4)=4*R+9 by omega] using joined

end NearCubicWires.P1Closure.TemplateRestore
