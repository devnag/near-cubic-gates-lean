import Proof.CaseAnalysis.RecoveryClauseLiteralOutput

/-! Actual graph and original source cursors after the complete literal. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOutput
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def graph (second neg : Bool) (ref : ℕ) (out : List Bool):=
  out++if neg then RecoveryBoundedLiteral.emitted second ref else []
def heads (H : Fin 71→ℕ) (second neg : Bool) (ref : ℕ) (out pre bits : List Bool):=
  RecoveryBoundedLiteralDock.heads second neg
    (RecoveryBoundedLiteralLoad.heads H (pre.length+2*bits.length+1)) ref out

theorem head_other (H : Fin 71→ℕ) (second neg : Bool) (ref : ℕ) (out pre bits : List Bool)
    (i : Fin 71) (h20 : i≠20) (h70 : i≠70) : heads H second neg ref out pre bits i=H i := by
  cases neg <;> simp [heads,RecoveryBoundedLiteralDock.heads,RecoveryBoundedLiteralLoad.heads,h20,h70]
theorem head_graph (H : Fin 71→ℕ) (second neg : Bool) (ref : ℕ) (out pre bits : List Bool)
    (h20 : H 20=out.length) : heads H second neg ref out pre bits 20=(graph second neg ref out).length := by
  cases neg <;> simp [heads,graph,RecoveryBoundedLiteralDock.heads,RecoveryBoundedLiteralLoad.heads,h20]
theorem head_source (H : Fin 71→ℕ) (second neg : Bool) (ref : ℕ) (out pre bits : List Bool) :
    heads H second neg ref out pre bits 70=(pre++frame bits).length := by
  cases neg <;> simp [heads,RecoveryBoundedLiteralDock.heads,RecoveryBoundedLiteralLoad.heads,frame_length,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOutput
