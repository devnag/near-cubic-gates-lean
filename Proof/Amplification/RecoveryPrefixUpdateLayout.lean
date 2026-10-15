import Proof.Amplification.RecoveryPrefixAdvanceReuse
import Proof.Amplification.RecoveryPrefixCounter
import Proof.Amplification.RecoveryPrefixFlag

/-! Fixed native prefix-body tape layout. The query occupies the original
357 tapes; three extra tapes retain the answer and two reset counters. -/
namespace NearCubicWires.RepairOrdinary.RecoveryPrefixUpdate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def querySlots (i : Fin 357) : Fin 360 := i.castAdd 3
def flagSlots : Fin 2→Fin 360 := ![356,357]
def tailSlots : Fin 3→Fin 360 := ![1,357,358]
def countSlots : Fin 2→Fin 360 := ![2,359]
theorem query_injective : Function.Injective querySlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 360=>k.val) h)
theorem flag_injective : Function.Injective flagSlots := by decide
theorem tail_injective : Function.Injective tailSlots := by decide
theorem count_injective : Function.Injective countSlots := by decide
noncomputable def flagMachine := RecoveryFocus.machine flagSlots RecoveryPrefixFlag.machine
noncomputable def tailMachine := RecoveryFocus.machine tailSlots RecoveryPrefixTail.machine
noncomputable def countMachine := RecoveryFocus.machine countSlots ClockIncrement.machine
noncomputable def machine := Composition.machine (Composition.machine flagMachine tailMachine) countMachine

def first (cap : Nat) (answer : Bool) (ambient : Fin 360→List Bool) :=
  Function.update ambient 357 (ZeroPadding.pad cap [answer])
def second (cap : Nat) (xs : List Bool) (answer : Bool) (ambient : Fin 360→List Bool) :=
  Function.update (first cap answer ambient) 1 (ZeroPadding.pad cap (frame ((xs++[!answer])++[false,true])))
def finished (cap n : Nat) (xs : List Bool) (answer : Bool) (ambient : Fin 360→List Bool) :=
  Function.update (second cap xs answer ambient) 2 (ZeroPadding.pad cap (frame (n+1).bits))

end NearCubicWires.RepairOrdinary.RecoveryPrefixUpdate
