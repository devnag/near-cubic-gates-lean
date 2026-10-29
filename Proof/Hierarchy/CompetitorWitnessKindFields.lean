import Proof.Hierarchy.CompetitorWitnessKindInit

namespace NearCubicWires.RepairOrdinary.CompetitorWitnessKind
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics RecoveryLiteralTag
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
def rowSlots : Fin 5 → Fin 6 := ![0,1,2,3,4]
def predSlots : Fin 3 → Fin 6 := ![0,5,4]
noncomputable def row := RecoveryFocus.machine rowSlots RecoveryRowKind.machine
noncomputable def predecessor := RecoveryFocus.machine predSlots RecoveryListPredecessor.machine

def rowFlags (bits : List Bool) : Fin 4 → Bool :=
  ![decide (value bits=0),decide (value bits=1),decide (value bits=2),false]
def predFlags (bits : List Bool) : Fin 4 → Bool :=
  ![decide (value bits=0),decide (value bits=1),decide (value bits=2),nonzero (RecoveryRowKind.after bits)]
def after (bits : List Bool) := predWord (RecoveryRowKind.after bits)
def choose (flags : Fin 4 → Bool) := flags 0 || (!(flags 1) && !(flags 2) && !(flags 3))
def flags (bits : List Bool) : Fin 4 → Bool :=
  ![decide (value bits=0),decide (value bits=1),decide (value bits=2),decide (value bits=0 ∨ value bits=3)]

theorem after_row_length (bits : List Bool) : (RecoveryRowKind.after bits).length=bits.length := by
  simp [RecoveryRowKind.after,predWord]

theorem choose_eq (bits : List Bool) : choose (predFlags bits)=decide (value bits=0 ∨ value bits=3) := by
  by_cases h0 : value bits=0
  · simp [choose,predFlags,h0]
  by_cases h1 : value bits=1
  · simp [choose,predFlags,h1]
  by_cases h2 : value bits=2
  · simp [choose,predFlags,h2]
  have hp1 := RecoveryListPredecessor.predecessor_value bits h0
  change value (predWord bits)=value bits-1 at hp1
  have hp2 := RecoveryListPredecessor.predecessor_value (predWord bits) (by omega)
  change value (predWord (predWord bits))=value (predWord bits)-1 at hp2
  have hp3 := RecoveryListPredecessor.predecessor_value (predWord (predWord bits)) (by omega)
  change value (RecoveryRowKind.after bits)=value (predWord (predWord bits))-1 at hp3
  apply Bool.eq_iff_iff.mpr
  simp [choose,predFlags,nonzero,h0,h1,h2]
  omega

end NearCubicWires.RepairOrdinary.CompetitorWitnessKind
