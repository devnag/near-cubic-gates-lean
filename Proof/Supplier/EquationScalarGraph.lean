import Proof.Supplier.EquationScalarPrepare
import Proof.Supplier.EquationScalarEmit

/-! A fixed finite graph for the two signed scalar operations. Every node
is an already executed local program; graph returns cost a physical step. -/
namespace NearCubicWires.RepairOrdinary.EquationScalar.Graph
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def incSlots : Fin 2→Fin 12 := ![2,5]
def predSlots : Fin 3→Fin 12 := ![2,4,5]
def scanSlots : Fin 4→Fin 12 := ![2,6,7,8]
def emitSlots : Fin 5→Fin 12 := ![2,1,7,9,11]
def sizes : Fin 5→Nat := ![10,5,7,8,8]
def programs (negate : Bool) : (j : Fin 5)→Machine 12 (sizes j) :=
  Fin.cases Prepare.machine (Fin.cases
    (RecoveryFocus.machine incSlots FramedIncrement.machine) (Fin.cases
    (RecoveryFocus.machine predSlots RecoveryListPredecessor.machine) (Fin.cases
    (RecoveryFocus.machine scanSlots Scan.machine) (Fin.cases
    (RecoveryFocus.machine emitSlots (Emit.machine negate)) (fun i => nomatch i)))))
def next (negate : Bool) (j : Fin 5) (_ : Fin (sizes j)) (bs : Fin 12→Bool) : Option (Fin 5) :=
  if j=0 then some (if negate then 3 else if bs 1 then 2 else 1)
  else if j=1 ∨ j=2 then some 3 else if j=3 then some 4 else none
def machine (negate : Bool) := RecoveryCalls.machine sizes (programs negate) 0 (next negate)
def entry (negate : Bool) (j : Fin 5) (a : Fin 12→List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs negate j) a)

theorem pick_inc (i : Fin 12) : RecoveryFocus.pick incSlots i=
    (if i=2 then some 0 else if i=5 then some 1 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot incSlots (by decide) 0
    | exact RecoveryFocus.pick_slot incSlots (by decide) 1
    | decide
theorem pick_pred (i : Fin 12) : RecoveryFocus.pick predSlots i=
    (if i=2 then some 0 else if i=4 then some 1 else if i=5 then some 2 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot predSlots (by decide) 0
    | exact RecoveryFocus.pick_slot predSlots (by decide) 1
    | exact RecoveryFocus.pick_slot predSlots (by decide) 2
    | decide
theorem pick_scan (i : Fin 12) : RecoveryFocus.pick scanSlots i=
    (if i=2 then some 0 else if i=6 then some 1 else if i=7 then some 2 else if i=8 then some 3 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot scanSlots (by decide) 0
    | exact RecoveryFocus.pick_slot scanSlots (by decide) 1
    | exact RecoveryFocus.pick_slot scanSlots (by decide) 2
    | exact RecoveryFocus.pick_slot scanSlots (by decide) 3
    | decide
theorem pick_emit (i : Fin 12) : RecoveryFocus.pick emitSlots i=
    (if i=2 then some 0 else if i=1 then some 1 else if i=7 then some 2 else
      if i=9 then some 3 else if i=11 then some 4 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot emitSlots (by decide) 0
    | exact RecoveryFocus.pick_slot emitSlots (by decide) 1
    | exact RecoveryFocus.pick_slot emitSlots (by decide) 2
    | exact RecoveryFocus.pick_slot emitSlots (by decide) 3
    | exact RecoveryFocus.pick_slot emitSlots (by decide) 4
    | decide

theorem entry_zero (negate : Bool) (a : Fin 12→List Bool) :
    entry negate 0 a=initialConfiguration (machine negate) a := rfl

end
end NearCubicWires.RepairOrdinary.EquationScalar.Graph
