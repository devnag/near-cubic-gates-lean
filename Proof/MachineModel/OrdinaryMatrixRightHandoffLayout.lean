import Proof.MachineModel.OrdinaryMatrixCoordinateReset

/-! Fixed physical bank for transposition followed by the right sorter.
Six fresh sort/rewind tapes and the three actual dimension drivers are named. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightHandoff
open LocalBitMultitape
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sortStates := 88+MatrixRightSort.planeStates
def slots : Fin 11 → Fin 23 := ![10,13,14,15,16,17,18,19,20,21,22]
def heads (out : List Bool) : Fin 10 → ℕ := ![0,0,0,0,0,0,out.length,1,1,1]
def tapes (out : List Bool) (U used pad : ℕ) : Fin 10 → List Bool :=
  ![[],[],[],[],[],[],out,UnaryTemplate.tape U,CompareMachine.word used,UnaryTemplate.tape pad]
noncomputable def prefixMachine : Machine 23 40 := TapeEmbedding.machine 10 MatrixCoordinateTranspose.resetMachine
noncomputable def sortMachine : Machine 23 sortStates := RecoveryFocus.machine slots MatrixRightSort.machine
noncomputable def machine : Machine 23 (40+sortStates) := Composition.machine prefixMachine sortMachine

noncomputable def input (M scratch : ℕ) (rs : List MatrixCoordinateTranspose.Record) (out : List Bool) (U used pad : ℕ) :
    Configuration 23 (40+sortStates) :=
  Composition.leftConfig sortStates (TapeEmbedding.config (heads out) (tapes out U used pad)
    (MatrixCoordinateTranspose.resetInput M scratch rs [] [] [] []))

theorem selected_heads {s : ℕ} (c : Configuration 13 s) (req : SortCarrier.Request)
    (out : List Bool) (U used pad : ℕ) (hc : c.heads 10=0) :
    ∀ j,(TapeEmbedding.config (heads out) (tapes out U used pad) c).heads (slots j)=
      (MatrixRightSort.input req out U used pad).heads j := by
  intro j
  fin_cases j <;> simp [slots,TapeEmbedding.config,heads,MatrixRightSort.input,Composition.leftConfig,
    initialConfiguration,Fin.addCases,hc]

theorem selected_tapes {s : ℕ} (c : Configuration 13 s) (req : SortCarrier.Request)
    (out : List Bool) (U used pad : ℕ) (hc : c.tapes 10=StablePartition.stream req.records) :
    ∀ j,(TapeEmbedding.config (heads out) (tapes out U used pad) c).tapes (slots j)=
      (MatrixRightSort.input req out U used pad).tapes j := by
  intro j
  fin_cases j <;> simp [slots,TapeEmbedding.config,tapes,MatrixRightSort.input,Composition.leftConfig,
    initialConfiguration,SourceHandoff.sourceTapes,Fin.addCases,hc]

end NearCubicWires.RepairOrdinary.MatrixRightHandoff
