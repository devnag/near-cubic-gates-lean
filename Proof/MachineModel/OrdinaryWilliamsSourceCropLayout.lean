import Proof.MachineModel.OrdinaryWilliamsCrop
import Proof.MachineModel.OrdinaryWilliamsReplay
import Proof.Amplification.RecoveryFocusedMachine

/-! Static source-to-crop tape wiring. The source's actual output is the
crop's input; its workspace and the transition-log tape remain allocated. -/
namespace NearCubicWires.RepairOrdinary.WilliamsSourceCrop
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapeCount (a : WilliamsAlgorithm) : ℕ := (a.tapeCount + 1) + 6
def sourceTape (a : WilliamsAlgorithm) : Fin (tapeCount a) := (a.outputTape.castAdd 1).castAdd 6
def extra (a : WilliamsAlgorithm) (i : Fin 6) : Fin (tapeCount a) := i.natAdd (a.tapeCount + 1)
def slot (a : WilliamsAlgorithm) : Fin 7 → Fin (tapeCount a) :=
  ![extra a 0, sourceTape a, extra a 1, extra a 2, extra a 3, extra a 4, extra a 5]

theorem slot_injective (a : WilliamsAlgorithm) : Function.Injective (slot a) := by
  intro i j h
  have hs := a.outputTape.isLt
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [slot, sourceTape, extra] at hv ⊢ <;> omega

def extraHeads : Fin 6 → ℕ := ![1, 0, 1, 1, 1, 1]
def extraTapes (r : RectangularProductRequest) : Fin 6 → List Bool :=
  let v := WilliamsPaddedRequest.dimension r.dimension
  let w := natBitLength v
  let lo := natBitLength r.dimension
  ![UnaryTemplate.tape lo, [], UnaryTemplate.tape (w - lo), CompareMachine.word r.dimension,
    UnaryTemplate.tape ((v - r.dimension) * w), CompareMachine.word r.dimension]

noncomputable def sourceProgram (a : WilliamsAlgorithm) : Machine (tapeCount a) (a.stateCount + 2) :=
  TapeEmbedding.machine 6 (WilliamsReplay.machine a)
noncomputable def cropProgram (a : WilliamsAlgorithm) : Machine (tapeCount a) MatrixCropRows.stateCount :=
  RecoveryFocus.machine (slot a) MatrixCropRows.machine
noncomputable def machine (a : WilliamsAlgorithm) : Machine (tapeCount a) ((a.stateCount + 2) + MatrixCropRows.stateCount) :=
  Composition.machine (sourceProgram a) (cropProgram a)

def sourceInput (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    Configuration (tapeCount a) (a.stateCount + 2) :=
  TapeEmbedding.config extraHeads (extraTapes r) (initialConfiguration (WilliamsReplay.machine a)
    (Fin.addCases (WilliamsReplay.inputs a (WilliamsPaddedRequest.request r hr)) (fun _ => [])))

noncomputable def cropInput (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) :
    Configuration 7 MatrixCropRows.stateCount :=
  let v := WilliamsPaddedRequest.dimension r.dimension
  let w := natBitLength v
  let lo := natBitLength r.dimension
  MatrixCropRows.config MatrixCropRows.machine.start (WilliamsPaddedRequest.request r hr).output
    0 [] lo (w - lo) r.dimension ((v - r.dimension) * w) r.dimension

theorem focus_same {t u s k : ℕ} (slots : Fin t → Fin u) (ambient : Configuration u s) (part : Configuration t k)
    (hh : ∀ i, ambient.heads (slots i) = part.heads i)
    (ht : ∀ i, ambient.tapes (slots i) = part.tapes i) :
    RecoveryFocus.config slots ambient.heads ambient.tapes part = Composition.restart ambient part.control := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config, Composition.restart, hp]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hp
      simpa [RecoveryFocus.config, Composition.restart, hp, hj] using (hh j).symm
  · funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [RecoveryFocus.config, Composition.restart, hp]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slots hp
      simpa [RecoveryFocus.config, Composition.restart, hp, hj] using (ht j).symm

theorem handoff (a : WilliamsAlgorithm) (r : RectangularProductRequest) (hr : 1 ≤ r.dimension)
    (finished : Configuration (a.tapeCount + 1) (a.stateCount + 2))
    (hh : ∀ i, finished.heads i = 0)
    (hout : finished.tapes (a.outputTape.castAdd 1) = (WilliamsPaddedRequest.request r hr).output) :
    RecoveryFocus.config (slot a) (TapeEmbedding.config extraHeads (extraTapes r) finished).heads
      (TapeEmbedding.config extraHeads (extraTapes r) finished).tapes (cropInput r hr) =
      Composition.restart (TapeEmbedding.config extraHeads (extraTapes r) finished) (cropProgram a).start := by
  apply focus_same
  · intro i
    fin_cases i <;> simp [slot, sourceTape, extra, TapeEmbedding.config, extraHeads, cropInput,
      MatrixCropRows.config, MatrixCropRow.config, MatrixCropCells.config, MatrixCropCell.config,
      MatrixRawBlock.config, Fin.addCases, hh] <;> omega
  · intro i
    fin_cases i <;> simp [slot, sourceTape, extra, TapeEmbedding.config, extraTapes, cropInput,
      MatrixCropRows.config, MatrixCropRow.config, MatrixCropCells.config, MatrixCropCell.config,
      MatrixRawBlock.config, Fin.addCases, hout] <;> omega

end NearCubicWires.RepairOrdinary.WilliamsSourceCrop
