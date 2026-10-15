import Proof.Amplification.RecoveryTseitinCore

/-! Fixed physical preparation for each reused prefix query.  The three
source fields and one controller-produced unary capacity remain outside the
cleared work bank. No length or offset is used as finite-control advice. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlot (i : Fin 234) : Fin 239 := ⟨5+i.val,by omega⟩
def eraseSlots : Fin 236→Fin 239 :=
  Fin.addCases (m := 235) (n := 1) (motive := fun _=>Fin 239)
    (Fin.addCases (m := 234) (n := 1) (motive := fun _=>Fin 239) workSlot
      (fun _ : Fin 1=>3)) (fun _ : Fin 1=>4)
def literalSlots (destination : Fin 239) : Fin 2→Fin 239 := ![destination,238]
def sourceSlot (sources : Fin 3→Fin 3) (k : Fin 3) : Fin 239 := ⟨(sources k).val,by have h:=(sources k).isLt; omega⟩
def destinationSlot : Fin 3→Fin 239 := ![bank 0 3,bank 1 3,bank 2 3]
def copySlots (sources : Fin 3→Fin 3) (k : Fin 3) : Fin 3→Fin 239 := ![sourceSlot sources k,destinationSlot k,238]

theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 239=>x.val) h
  have he (i : Fin 236) : (eraseSlots i).val=if i.val<234 then 5+i.val else i.val-231 := by
    refine Fin.addCases (m := 235) (n := 1) (fun a=>?_) (fun a=>?_) i
    · refine Fin.addCases (m := 234) (n := 1) (fun b=>?_) (fun b=>?_) a
      · simp [eraseSlots,workSlot]
      · fin_cases b; simp [eraseSlots]; rfl
    · fin_cases a; simp [eraseSlots]; rfl
  rw [he,he] at hv
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

theorem literal_injective (destination : Fin 239) (hd : destination≠238) :
    Function.Injective (literalSlots destination) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [literalSlots]

theorem copy_injective (sources : Fin 3→Fin 3) (k : Fin 3) : Function.Injective (copySlots sources k) := by
  intro i j h
  have hs := (sources k).isLt
  have hv := congrArg Fin.val h
  fin_cases k <;> fin_cases i <;> fin_cases j <;> dsimp [copySlots,sourceSlot,destinationSlot,bank] at hv ⊢ <;> first | rfl | omega

noncomputable def clearMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 234)
noncomputable def literalMachine (destination : Fin 239) (word : List Bool) :=
  RecoveryFocus.machine (literalSlots destination) (HierarchyFixedWord.machine word)
noncomputable def copyMachine (sources : Fin 3→Fin 3) (k : Fin 3) := RecoveryFocus.machine (copySlots sources k) PCPFieldMoves.readyMachine
noncomputable def machine (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) :=
  Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine (Composition.machine clearMachine
      (literalMachine (bank 0 2) (frame (signs 0).toNat.bits)))
      (literalMachine (bank 1 2) (frame (signs 1).toNat.bits)))
      (literalMachine (bank 2 2) (frame (signs 2).toNat.bits)))
      (copyMachine sources 0)) (copyMachine sources 1)) (copyMachine sources 2)

def cleared (cap : Nat) (ambient : Fin 239→List Bool) : Fin 239→List Bool := fun i=>
  if i.val<3 then ambient i else if i.val=3 then List.replicate cap true
  else if i.val=4 then List.replicate (cap+1) false else List.replicate cap false

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
