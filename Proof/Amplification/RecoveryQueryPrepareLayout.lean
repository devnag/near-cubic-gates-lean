import Proof.Amplification.RecoveryQueryState

/-! Fixed physical preparation for each reused prefix query.  The three
source fields and one controller-produced unary capacity remain outside the
cleared work bank. No length or offset is used as finite-control advice. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlot (i : Fin 352) : Fin 357 := ⟨5+i.val,by omega⟩
def eraseSlots : Fin 354→Fin 357 :=
  Fin.addCases (m := 353) (n := 1) (motive := fun _=>Fin 357)
    (Fin.addCases (m := 352) (n := 1) (motive := fun _=>Fin 357) workSlot
      (fun _ : Fin 1=>3)) (fun _ : Fin 1=>4)
def literalSlots (destination : Fin 357) : Fin 2→Fin 357 := ![destination,356]
def sourceSlot : Fin 3→Fin 357 := ![0,1,2]
def destinationSlot : Fin 3→Fin 357 := ![bank 5 3,bank 2 3,bank 0 3]
def copySlots (k : Fin 3) : Fin 3→Fin 357 := ![sourceSlot k,destinationSlot k,356]

theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 357=>x.val) h
  have he (i : Fin 354) : (eraseSlots i).val=if i.val<352 then 5+i.val else i.val-349 := by
    refine Fin.addCases (m := 353) (n := 1) (fun a=>?_) (fun a=>?_) i
    · refine Fin.addCases (m := 352) (n := 1) (fun b=>?_) (fun b=>?_) a
      · simp [eraseSlots,workSlot]
      · fin_cases b; simp [eraseSlots]; rfl
    · fin_cases a; simp [eraseSlots]; rfl
  rw [he,he] at hv
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

theorem literal_injective (destination : Fin 357) (hd : destination≠356) :
    Function.Injective (literalSlots destination) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [literalSlots]

theorem copy_injective (k : Fin 3) : Function.Injective (copySlots k) := by
  fin_cases k <;> decide

noncomputable def clearMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 352)
noncomputable def literalMachine (destination : Fin 357) (word : List Bool) :=
  RecoveryFocus.machine (literalSlots destination) (HierarchyFixedWord.machine word)
noncomputable def copyMachine (k : Fin 3) := RecoveryFocus.machine (copySlots k) PCPFieldMoves.readyMachine
noncomputable def machine (flat : Bool) :=
  Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine clearMachine (literalMachine (bank 0 2) (frame (1 : Nat).bits)))
      (literalMachine (bank 5 2) (frame flat.toNat.bits)))
    (copyMachine 0)) (copyMachine 1)) (copyMachine 2)

def cleared (cap : Nat) (ambient : Fin 357→List Bool) : Fin 357→List Bool := fun i=>
  if i.val<3 then ambient i else if i.val=3 then List.replicate cap true
  else if i.val=4 then List.replicate (cap+1) false else List.replicate cap false

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
