import Proof.CaseAnalysis.RecoverySearchGraphDock
import Proof.Amplification.RecoveryTseitinNativeSerialize

/-! The fixed final two-call controller, independent of its run proof. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedColdSearchJoin
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open RecoveryBoundedSearchGraphDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pieces {u s : Nat} (first : Machine (1664+u) s) : Fin 2→Piece (1664+u+790)
  | 0=>ordinary (TapeEmbedding.machine 790 first)
  | 1=>focused (RecoveryBoundedSearchExecution.program 1073741824) (slots u)
def next {u s : Nat} (first : Machine (1664+u) s) (j : Fin 2)
    (_ : Fin (pieces first j).states) (_ : Fin (1664+u+790)→Bool) : Option (Fin 2):=
  if j=0 then some 1 else none
noncomputable abbrev program {u s : Nat} (first : Machine (1664+u) s):=
  (ports u).program (graph (pieces first) 0 (next first))

end NearCubicWires.RepairSource.RecoveryBoundedColdSearchJoin
