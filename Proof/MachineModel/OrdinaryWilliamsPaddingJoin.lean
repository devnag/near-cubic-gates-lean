import Proof.MachineModel.OrdinaryWilliamsPadding
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! One actual continuous pass over the two raw source matrices produces
both exact-power inputs. The caller supplies the dimension frame and unary
templates; their production and final source-input rewinds are separate. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPadding
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation
open WilliamsLoaderForms RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rightSlots : Fin 5 → Fin 8 := ![4, 1, 5, 6, 7]
theorem right_injective : Function.Injective rightSlots := by decide
def rightHeads : Fin 4 → ℕ := ![1, 0, 1, 1]
def rightTapes (r : RectangularProductRequest) : Fin 4 → List Bool :=
  ![UnaryTemplate.tape r.dimension, [], UnaryTemplate.tape (WilliamsPaddedRequest.dimension r.dimension - r.dimension),
    CompareMachine.word (rectangularInnerDimension r.dimension)]

def leftProgram : Machine 8 10 := TapeEmbedding.machine 4 MatrixPadRow.machine
noncomputable def rightProgram : Machine 8 MatrixPadRows.stateCount := RecoveryFocus.machine rightSlots MatrixPadRows.machine
noncomputable def joinedMachine : Machine 8 (10 + MatrixPadRows.stateCount) := Composition.machine leftProgram rightProgram

def input (r : RectangularProductRequest) (pre suffix : List Bool) : Configuration 8 10 :=
  let v := WilliamsPaddedRequest.dimension r.dimension
  let c := rectangularInnerDimension r.dimension
  TapeEmbedding.config rightHeads (rightTapes r)
    (MatrixPadRow.config MatrixPadRow.machine.start (pre ++ rowMajorBitMatrix r.left ++ rowMajorBitMatrix r.right ++ suffix)
      pre.length (natWord v) (r.dimension * c) ((v - r.dimension) * c))

theorem joined_run (r : RectangularProductRequest) (pre suffix : List Bool) :
    let v := WilliamsPaddedRequest.dimension r.dimension
    let c := rectangularInnerDimension r.dimension
    ∃ actual : ExecutionReceipt 8 (10 + MatrixPadRows.stateCount),
      runFrom joinedMachine (4 * v * c + 12 * c + 13)
        (Composition.leftConfig MatrixPadRows.stateCount (input r pre suffix)) = some actual ∧
      actual.final.tapes 2 = natWord v ++ rowMajorBitMatrix (WilliamsPaddedRequest.left r) ∧
      actual.final.tapes 5 = rowMajorBitMatrix (WilliamsPaddedRequest.right r) ∧
      actual.final.heads 1 = pre.length + r.dimension * c + c * r.dimension ∧
      actual.steps ≤ 4 * v * c + 12 * c + 13 := by
  dsimp only
  let v := WilliamsPaddedRequest.dimension r.dimension
  let c := rectangularInnerDimension r.dimension
  let source := pre ++ rowMajorBitMatrix r.left ++ rowMajorBitMatrix r.right ++ suffix
  obtain ⟨left, hl, hlf, hls⟩ := left_run r pre (rowMajorBitMatrix r.right ++ suffix)
  have hsource : pre ++ rowMajorBitMatrix r.left ++ (rowMajorBitMatrix r.right ++ suffix) = source := by
    simp only [source, List.append_assoc]
  rw [hsource] at hl hlf
  have he := TapeEmbedding.run_embed MatrixPadRow.machine rightHeads (rightTapes r) _ _ left hl
  obtain ⟨right, hr, hrf, hrs⟩ := right_run r (pre ++ rowMajorBitMatrix r.left) suffix []
  have hlen : (rowMajorBitMatrix r.left).length = r.dimension * c := WilliamsLoader.matrix_length r.left
  rw [List.length_append, hlen] at hr hrf
  let ambient : Configuration 8 10 := TapeEmbedding.config rightHeads (rightTapes r) left.final
  let rightInput := MatrixPadRows.config MatrixPadRows.machine.start source (pre.length + r.dimension * c) []
    r.dimension (v - r.dimension) c
  have hsame : RecoveryFocus.config rightSlots ambient.heads ambient.tapes rightInput =
      Composition.restart ambient rightProgram.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hlf]
      fin_cases i <;> simp [rightSlots, rightHeads, rightInput, TapeEmbedding.config,
        MatrixPadRow.config, MatrixPadRows.config, MatrixRawBlock.config, Fin.addCases, c]
    · intro i
      dsimp only [ambient]
      rw [hlf]
      fin_cases i <;> simp [rightSlots, rightTapes, rightInput, TapeEmbedding.config,
        MatrixPadRow.config, MatrixPadRows.config, MatrixRawBlock.config, Fin.addCases, v, c]
  obtain ⟨focused, hfocus, hff, hfs⟩ := RecoveryFocus.run_config rightSlots right_injective MatrixPadRows.machine
    ambient.heads ambient.tapes (c * (2 * v + 12) + 3) rightInput right hr
  rw [hsame] at hfocus
  have hj := Composition.run_join leftProgram rightProgram (2 * (v * c) + 9) (c * (2 * v + 12) + 3) _
    (TapeEmbedding.receipt rightHeads (rightTapes r) left) focused he hfocus
  let actual := Composition.joinedReceipt (TapeEmbedding.receipt rightHeads (rightTapes r) left) focused
  have htime : 2 * (v * c) + 9 + 1 + (c * (2 * v + 12) + 3) = 4 * v * c + 12 * c + 13 := by ring
  have hslot (i : Fin 5) : RecoveryFocus.pick rightSlots (rightSlots i) = some i := RecoveryFocus.pick_slot _ right_injective i
  have hnone : RecoveryFocus.pick rightSlots (2 : Fin 8) = none := by
    have h : ¬∃ i, rightSlots i = 2 := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      fin_cases i <;> norm_num [rightSlots] at hv
    simp [RecoveryFocus.pick, h]
  refine ⟨actual, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · change focused.final.tapes 2 = _
    rw [hff]
    simp only [RecoveryFocus.config, hnone]
    dsimp only [ambient]
    rw [hlf]
    rfl
  · change focused.final.tapes (rightSlots 2) = _
    rw [hff, hrf]
    simp [RecoveryFocus.config, hslot, MatrixPadRows.config, MatrixPadRow.config, MatrixRawBlock.config,
      TapeEmbedding.config, Fin.addCases]
  · change focused.final.heads (rightSlots 1) = _
    rw [hff, hrf]
    simp [RecoveryFocus.config, hslot, MatrixPadRows.config, MatrixPadRow.config, MatrixRawBlock.config,
      TapeEmbedding.config, Fin.addCases, c]
  · change left.steps + 1 + focused.steps ≤ _
    rw [hfs, hls]
    dsimp only [v, c] at *
    nlinarith

end NearCubicWires.RepairOrdinary.WilliamsPadding
