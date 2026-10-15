import Proof.Amplification.RecoveryRowStructureChildrenLookup

/-! The paired caller copies each actual child key into the reused lookup
bank, and saves the first returned count in the consumed parsed-code cell.
The original witness rows remain in their retained source buffer. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankKey (x : Children) (key : List Bool) : Children := {x with bank:={x.bank with key:=key}}
def leftSaved (x : Children) : Children := {x with base:=setCode x.base x.bank.saved}

theorem lookup_key_tapes (bank : RecoveryRowLookupStream.Data) (total capacity : Nat) (key : List Bool) :
    RecoveryRowLookupTable.readyTapes {bank with key:=key} total capacity=
      Function.update (RecoveryRowLookupTable.readyTapes bank total capacity) 7 (frame key) := by
  funext i
  fin_cases i <;> rfl

theorem bankKey_tapes (x : Children) (key : List Bool) :
    (bankKey x key).tapes=Function.update x.tapes 59 (frame key) := by
  change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (cfg x.base x.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes {x.bank with key:=key} x.total x.lookupCapacity)=_
  rw [lookup_key_tapes,bank_update_right]
  rfl

theorem leftSaved_tapes (x : Children) : (leftSaved x).tapes=Function.update x.tapes 46 (frame x.bank.saved) := by
  change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (cfg (setCode x.base x.bank.saved) x.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity)=_
  rw [cfg_code,bank_update_left]
  rfl

def keyCopySlots (left : Bool) : Fin 4→Fin 68 := ![if left then 17 else 24,59,51,22]
theorem keyCopySlots_injective (left : Bool) : Function.Injective (keyCopySlots left) := by cases left <;> decide
noncomputable def keyCopyMachine (left : Bool) := RecoveryFocus.machine (keyCopySlots left) RecoveryRootRound.copyMachine

def saveCountSlots : Fin 4→Fin 68 := ![60,46,51,22]
theorem saveCountSlots_injective : Function.Injective saveCountSlots := by decide
noncomputable def saveCountMachine := RecoveryFocus.machine saveCountSlots RecoveryRootRound.copyMachine

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem key_copy_output (left : Bool) (ambient : Fin 68→List Bool) (key : List Bool) (padding capacity reset : Nat)
    (hsource : ambient (if left then 17 else 24)=ZeroPadding.pad padding (frame key))
    (hcopy : ambient 51=List.replicate capacity false) (hreset : ambient 22=List.replicate reset false) :
    install (keyCopySlots left) ambient ![ZeroPadding.pad padding (frame key),frame key,
      List.replicate capacity false,List.replicate reset false]=Function.update ambient 59 (frame key) := by
  apply install_eq (keyCopySlots left) (keyCopySlots_injective left)
  · intro j
    fin_cases j
    · cases left <;> exact hsource.symm
    · cases left <;> simp [keyCopySlots]
    · cases left <;> exact hcopy.symm
    · cases left <;> exact hreset.symm
  · intro i hi
    have h59 : i≠59 := by intro he; exact hi 1 he.symm
    simp only [Function.update_of_ne h59]

theorem save_count_output (ambient : Fin 68→List Bool) (count : List Bool) (capacity reset : Nat)
    (hsource : ambient 60=frame count) (hcopy : ambient 51=List.replicate capacity false)
    (hreset : ambient 22=List.replicate reset false) :
    install saveCountSlots ambient ![frame count,frame count,List.replicate capacity false,List.replicate reset false]=
      Function.update ambient 46 (frame count) := by
  apply install_eq saveCountSlots saveCountSlots_injective
  · intro j
    fin_cases j
    · exact hsource.symm
    · simp [saveCountSlots]
    · exact hcopy.symm
    · exact hreset.symm
  · intro i hi
    have h46 : i≠46 := by intro he; exact hi 1 he.symm
    simp only [Function.update_of_ne h46]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
