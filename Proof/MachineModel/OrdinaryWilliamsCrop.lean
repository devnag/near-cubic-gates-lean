import Proof.MachineModel.OrdinaryMatrixNaturalCrop
import Proof.MachineModel.OrdinaryWilliamsPaddedRequest

/-! Actual crop of the exact positive-power source's output to the literal
arbitrary-dimension product. No function-valued matrix access is executed by
the crop machine: all cells are read from the source's existing output tape. -/
namespace NearCubicWires.RepairOrdinary.WilliamsCrop
open LocalBitMultitape SourceInterfaces WilliamsLoaderForms
open WilliamsProductCertificate RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (u v width : ℕ) : ℕ := u * (u * (2 * width + 12) + 2 * ((v - u) * width) + 11) + 3

theorem crop_le {u v lo width : ℕ} (hu : u ≤ v) (hw : lo ≤ width) (a : NatMatrix v v) (out : List Bool) :
    ∃ r : ExecutionReceipt 7 MatrixCropRows.stateCount,
      runFrom MatrixCropRows.machine (budget u v width)
        (MatrixCropRows.config MatrixCropRows.machine.start
          (encodedNatCellTape width (rowMajorNatMatrix a)) 0 out lo (width - lo) u ((v - u) * width) u) = some r ∧
      r.final = MatrixCropRows.config (RepairSource.VerifierDecoding.RepeatMachine.phaseCode MatrixCropRow.stateCount 3)
        (encodedNatCellTape width (rowMajorNatMatrix a)) (u * (v * width))
        (out ++ encodedNatCellTape lo (rowMajorNatMatrix (fun row : Fin u => fun col : Fin u =>
          a (row.castLE hu) (col.castLE hu)))) lo (width - lo) u ((v - u) * width) u ∧
      r.steps ≤ budget u v width := by
  obtain ⟨pad, rfl⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨hi, rfl⟩ := Nat.exists_eq_add_of_le hw
  have hcast (i : Fin u) : i.castLE hu = i.castAdd pad := Fin.ext rfl
  simpa only [budget, Nat.add_sub_cancel_left, hcast] using MatrixNaturalCrop.crop_run lo hi a out

theorem request_run (r : RectangularProductRequest) (hr : 1 ≤ r.dimension) (out : List Bool) :
    let v := WilliamsPaddedRequest.dimension r.dimension
    let w := natBitLength v
    let lo := natBitLength r.dimension
    ∃ actual : ExecutionReceipt 7 MatrixCropRows.stateCount,
      runFrom MatrixCropRows.machine (budget r.dimension v w)
        (MatrixCropRows.config MatrixCropRows.machine.start (WilliamsPaddedRequest.request r hr).output
          0 out lo (w - lo) r.dimension ((v - r.dimension) * w) r.dimension) = some actual ∧
      actual.final = MatrixCropRows.config (RepairSource.VerifierDecoding.RepeatMachine.phaseCode MatrixCropRow.stateCount 3)
        (WilliamsPaddedRequest.request r hr).output (r.dimension * (v * w))
        (out ++ encodedNatCellTape lo (rowMajorNatMatrix (integerMatrixProduct r.left r.right)))
        lo (w - lo) r.dimension ((v - r.dimension) * w) r.dimension ∧
      actual.steps ≤ budget r.dimension v w := by
  dsimp only
  have hu := WilliamsPaddedRequest.dimension_ge r.dimension
  have hw : natBitLength r.dimension ≤ natBitLength (WilliamsPaddedRequest.dimension r.dimension) :=
    Nat.add_le_add_right (Nat.log_mono_right hu) 1
  obtain ⟨actual, hrun, hfinal, hsteps⟩ := crop_le hu hw
    (integerMatrixProduct (WilliamsPaddedRequest.left r) (WilliamsPaddedRequest.right r)) out
  have he : (fun row : Fin r.dimension => fun col : Fin r.dimension =>
      integerMatrixProduct (WilliamsPaddedRequest.left r) (WilliamsPaddedRequest.right r)
        (row.castLE hu) (col.castLE hu)) = integerMatrixProduct r.left r.right := by
    funext row col
    exact WilliamsPaddedRequest.product_crop r row col
  rw [he] at hfinal
  exact ⟨actual, hrun, hfinal, hsteps⟩

theorem budget_quadratic (u v width : ℕ) (hu : u ≤ v) (hv : v ≤ 1024 * u) :
    budget u v width ≤ 4096 * (u + 1) ^ 2 * (width + 1) := by
  have hdiff : u + (v - u) = v := Nat.add_sub_of_le hu
  have he : budget u v width = 2 * u * v * width + 12 * u * u + 11 * u + 3 := by
    unfold budget
    calc
      _ = 2 * u * (u + (v - u)) * width + 12 * u * u + 11 * u + 3 := by ring
      _ = _ := by rw [hdiff]
  rw [he]
  have hprod : u * v * width ≤ 1024 * u * u * width := by
    calc
      _ ≤ u * (1024 * u) * width := Nat.mul_le_mul_right width (Nat.mul_le_mul_left u hv)
      _ = _ := by ring
  nlinarith

end NearCubicWires.RepairOrdinary.WilliamsCrop
