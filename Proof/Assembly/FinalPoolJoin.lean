import Proof.Assembly.FinalPoolMaskDock

/-! Exact four bank definitions consumed by the native hardwire runner. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalPool
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsGateSupport CloseoutRowsPoolWeight CloseoutRowsTouching
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wT (src backing out msk : List Bool) (total : ℕ) : Fin 5→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (data src backing out msk)
    (fun _ : Fin 1=>CompareMachine.word total)
def wH (pos mpos : ℕ) (out : List Bool) : Fin 5→ℕ:=
  Fin.addCases (motive:=fun _=>ℕ) (heads pos mpos out) (fun _ : Fin 1=>1)
def mT (src msk : List Bool) (bw bC ba total : ℕ) : Fin 21→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool) (CloseoutRowsPoolMinimum.data src msk bw bC ba)
    (fun _ : Fin 1=>CompareMachine.word total)
def mH (pos mpos : ℕ) : Fin 21→ℕ:=
  Fin.addCases (motive:=fun _=>ℕ) (CloseoutRowsPoolMinimum.heads pos mpos) (fun _ : Fin 1=>1)

end NearCubicWires.RepairOrdinary.CloseoutFinalPool
