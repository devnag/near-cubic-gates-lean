import Proof.MachineModel.Body
import Proof.Amplification.RecoveryScratchErase

/-! The occurrence's paid cleanup erases the original source bank and the
frame-copy counter together. The two existing erase ports are retained. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation RepairOrdinary.DecompositionSource
open RepairOrdinary.RecoveryRootRound ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
abbrev CT := T a+1

def resetSelected (i : Fin (T a)) : Bool := decide (i.val < SB a ∨ i=fcp a)
def eraseSlots (i : Fin (SB a+1+1+1)) : Fin (CT a) :=
  if i.val<SB a then ⟨i.val,by have h:=i.isLt;unfold CT T;omega⟩
  else ⟨i.val+7,by have h:=i.isLt;unfold CT T;omega⟩

theorem eraseSlots_val (i : Fin (SB a+1+1+1)) :
    (eraseSlots a i).val=if i.val<SB a then i.val else i.val+7 := by
  unfold eraseSlots
  split_ifs <;> rfl

theorem eraseSlots_injective : Function.Injective (eraseSlots a) := by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [eraseSlots_val,eraseSlots_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem eraseSlots_bank (i : Fin (SB a)) :
    eraseSlots a (((i.castAdd 1).castAdd 1).castAdd 1)=(bk a i).castAdd 1 := by
  apply Fin.ext
  rw [eraseSlots_val]
  simp only [Fin.val_castAdd,Fin.is_lt,↓reduceIte,bk_val]

theorem eraseSlots_counter :
    eraseSlots a (((Fin.natAdd (SB a) (0 : Fin 1)).castAdd 1).castAdd 1)=(fcp a).castAdd 1 := by
  apply Fin.ext
  rw [eraseSlots_val]
  simp [fcp,ex_val]

theorem eraseSlots_driver :
    eraseSlots a ((Fin.natAdd (SB a+1) (0 : Fin 1)).castAdd 1)=(drv a).castAdd 1 := by
  apply Fin.ext
  rw [eraseSlots_val]
  simp [drv,ex_val]

theorem eraseSlots_workspace :
    eraseSlots a (Fin.natAdd (SB a+1+1) (0 : Fin 1))=(wsp a).castAdd 1 := by
  apply Fin.ext
  rw [eraseSlots_val]
  simp [wsp,ex_val]

noncomputable def eraseBody:=RecoveryFocus.machine (eraseSlots a)
  (RecoveryScratchErase.resetMachine (SB a+1))
def cleanData (C : ℕ) : Fin (SB a+1+1+1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin (SB a+1)=>List.replicate C false)
    (fun _ : Fin 1=>List.replicate C true)) (fun _ : Fin 1=>List.replicate (C+1) false)

theorem erase_body (C : ℕ) (H : Fin (CT a) → ℕ) (A : Fin (CT a) → List Bool)
    (hH : ∀ j,H (eraseSlots a j)=0)
    (hb : ∀ j : Fin (SB a+1),(A (eraseSlots a ((j.castAdd 1).castAdd 1))).length ≤ C)
    (hd : A ((drv a).castAdd 1)=List.replicate C true)
    (hw : A ((wsp a).castAdd 1)=List.replicate (C+1) false) :
    Step (eraseBody a) (2*C+4) H A
      (dockH (eraseSlots a) H (fun _=>0)) (install (eraseSlots a) A (cleanData a C)) := by
  have base:=Step.of_ready (RecoveryScratchErase.erase_ready C (C+1)
    (fun j=>A (eraseSlots a ((j.castAdd 1).castAdd 1))) hb)
  have run:=base.dock (eraseSlots a) (eraseSlots_injective a) H A hH (by
    intro j
    refine Fin.addCases (m:=SB a+1+1) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=SB a+1) (n:=1) (fun k=>?_) (fun k=>?_) i
      · simp only [Fin.addCases_left]
      · have hk:k=0:=Fin.eq_zero k
        subst hk
        simp only [Fin.addCases_left,Fin.addCases_right,eraseSlots_driver]
        exact hd
    · have hi:i=0:=Fin.eq_zero i
      subst hi
      simp only [Fin.addCases_right,eraseSlots_workspace]
      exact hw)
  refine run.congr rfl ?_
  apply congrArg (install (eraseSlots a) A)
  funext j
  refine Fin.addCases (m:=SB a+1+1) (n:=1) (fun i=>?_) (fun i=>?_) j
  · refine Fin.addCases (m:=SB a+1) (n:=1) (fun k=>?_) (fun k=>?_) i <;>
      simp only [cleanData,Fin.addCases_left,Fin.addCases_right]
  · simp only [cleanData,Fin.addCases_right,Nat.max_self]

end NearCubicWires.ExtDecompositionBatch
