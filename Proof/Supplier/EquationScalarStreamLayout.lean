import Proof.Supplier.EquationScalarPadded
import Proof.PCP.PCPFieldMoves
import Proof.PCP.PCPSerializerReuseCopy
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

/-! Static seventeen-tape streaming scalar caller. The capacity is actual
unary tape data and does not parameterize this machine's finite control. -/
namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def moveSlots : Fin 3→Fin 17 := ![0,1,13]
def scalarSlots (j : Fin 12) : Fin 17 := ⟨j.val+1,by omega⟩
def copySlots : Fin 3→Fin 17 := ![10,14,13]
def scratchSlots (j : Fin 13) : Fin 17 := ⟨j.val+1,by omega⟩
def eraseSlots : Fin 15→Fin 17 :=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _=>Fin 17)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>Fin 17) scratchSlots (fun _=>15)) (fun _=>16)
def moveProgram := RecoveryFocus.machine moveSlots PCPFieldMoves.advanceMachine
def scalarProgram (negate : Bool) := RecoveryFocus.machine scalarSlots (EquationScalar.machine negate)
def copyProgram := RecoveryFocus.machine copySlots PCPSerializerReuse.copyMachine
def eraseProgram := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 13)
def first (negate : Bool) := Composition.machine moveProgram (scalarProgram negate)
def tail := Composition.machine copyProgram eraseProgram
def machine (negate : Bool) := Composition.machine (first negate) tail

def heads (pos outPos : Nat) : Fin 17→Nat := fun i => if i=0 then pos else if i=14 then outPos else 0
def tapes (C : Nat) (source out : List Bool) : Fin 17→List Bool :=
  fun i => if i=0 then source else if i=14 then out else if i=15 then List.replicate C true
    else if i=16 then List.replicate (C+1) false else List.replicate C false
def entry (negate : Bool) (C pos : Nat) (source out : List Bool) :=
  RecoveryCalls.restarted (machine negate) (heads pos out.length) (tapes C source out)
def budget (C p : Nat) := 2*C+100*(p+1)

theorem scalar_injective : Function.Injective scalarSlots := by intro i j h; exact Fin.ext (by have hv:=congrArg Fin.val h; dsimp [scalarSlots] at hv; omega)
theorem scratch_injective : Function.Injective scratchSlots := by intro i j h; exact Fin.ext (by have hv:=congrArg Fin.val h; dsimp [scratchSlots] at hv; omega)
theorem erase_injective : Function.Injective eraseSlots := by decide
theorem scalar_scratch (j : Fin 12) : scalarSlots j=scratchSlots (j.castAdd 1) := rfl

theorem pick_move (i : Fin 17) : RecoveryFocus.pick moveSlots i=
    (if i=0 then some 0 else if i=1 then some 1 else if i=13 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot moveSlots (by decide) 0
    | exact RecoveryFocus.pick_slot moveSlots (by decide) 1
    | exact RecoveryFocus.pick_slot moveSlots (by decide) 2
    | decide
theorem pick_copy (i : Fin 17) : RecoveryFocus.pick copySlots i=
    (if i=10 then some 0 else if i=14 then some 1 else if i=13 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot copySlots (by decide) 0
    | exact RecoveryFocus.pick_slot copySlots (by decide) 1
    | exact RecoveryFocus.pick_slot copySlots (by decide) 2
    | decide

theorem scalar_other (i : Fin 17) (hi : i=0 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16) :
    ∀ j,scalarSlots j≠i := by
  intro j he
  have hv:=congrArg Fin.val he
  simp only [scalarSlots] at hv
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> dsimp at hv <;> omega

end
end NearCubicWires.RepairOrdinary.EquationScalarStream
