import Proof.MachineModel.BlockScrub
import Proof.MachineModel.ClockUnarySum
import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.PCPSerializerCapacityPower
import Proof.PCP.ProjectionDimensionPowerBounds
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
open RepairOrdinary.RecoveryRootRound NearCubicWires.ExtDecompositionBatch
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

namespace UnaryCalc

/-! ## 1. `+` (and the copier) -/

/-- Unary sum, exact on all four tapes, heads `0` at both ends. -/
theorem sum_step (r s : ℕ) :
    Step ClockUnarySum.machine (2*(r+s)+6) (fun _ => 0)
      ![List.replicate r true, List.replicate s true, [], []] (fun _ => 0)
      ![List.replicate r true, List.replicate s true, List.replicate (r+s) true,
        List.replicate (r+s+2) false] :=
  CloseoutFinalSelector.step_of_clock (ClockUnarySum.sum_ready r s)

def sum (r s : ℕ) : Block 4 := ofStep (sum_step r s)

@[simp] theorem sum_cost (r s : ℕ) : (sum r s).cost = 2*(r+s)+6 := rfl

/-- The copier: `r` onto a fresh tape, leaving the rewind log `replicate (r+2) false`. -/
theorem copy_step (r : ℕ) :
    Step ClockUnarySum.machine (2*r+6) (fun _ => 0)
      ![List.replicate r true, [], [], []] (fun _ => 0)
      ![List.replicate r true, [], List.replicate r true, List.replicate (r+2) false] :=
  sum_step r 0

/-! ## 2. `×` -/

/-- Unary product, exact; the second factor is in the template form `false :: 1^e`. -/
theorem product_step (d e : ℕ) :
    Step ClockUnaryProduct.machine (2*(d*(2*e+3)+2)+2) (fun _ => 0)
      (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
        ![List.replicate d true, false :: List.replicate e true, []] (fun _ : Fin 1 => []))
      (fun _ => 0)
      ![List.replicate d true, false :: List.replicate e true, List.replicate (d*e) true,
        List.replicate (d*(2*e+3)+2) false] := by
  obtain ⟨r, hr, h0, h1, h2, h3, hh, hs⟩ := ClockUnaryProduct.product_run d e
  refine ⟨r, hr, funext hh, ?_, le_of_eq hs⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

def product (d e : ℕ) : Block 4 := ofStep (product_step d e)

/-! ## 3. The polynomial normal form `C*(n+1)^D` -/

/-- Tapes of the polynomial run (`14+2*D`). -/
abbrev tapes (D : ℕ) : ℕ := DimensionPolynomial.tapes D
/-- Its input tape: the unary dimension. -/
def inputTape (D : ℕ) : Fin (tapes D) := ⟨0, by simp [tapes, DimensionPolynomial.tapes]⟩
/-- Its output tape: the unary value. -/
abbrev outputTape (D : ℕ) : Fin (tapes D) := PCPSerializerCapacity.Power.outputSlot D

/-- The driver value. -/
def value (D C n : ℕ) : ℕ := C*(n+1)^D

theorem output_ne_input (D : ℕ) : outputTape D ≠ inputTape D := by
  intro h
  have hv := congrArg Fin.val h
  simp [outputTape, inputTape, PCPSerializerCapacity.Power.outputSlot,
    DimensionPolynomial.binarySlots] at hv

/-- **The polynomial run**, from one unary dimension on `inputTape` (all else blank, heads 0)
to `replicate (C*(n+1)^D) true` on `outputTape`; the input is preserved; the private
workspace is left existential. One fixed machine per `(D, C)`. -/
theorem poly_step (D C n : ℕ) : ∃ out : Fin (tapes D) → List Bool,
    Step (PCPSerializerCapacity.Power.machine D C) (PCPSerializerCapacity.Power.budget D C n)
      (fun _ => 0) (DimensionPolynomial.input D n) (fun _ => 0) out ∧
    out (inputTape D) = List.replicate n true ∧
    out (outputTape D) = List.replicate (value D C n) true := by
  obtain ⟨out, h, h0, h1⟩ := PCPSerializerCapacity.Power.capacity_run D C n
  exact ⟨out, CloseoutFinalSelector.step_of_clock h, h0, h1⟩

/-- The coefficient of the polynomial run's cost bound. -/
def polyCoefficient (D C : ℕ) : ℕ := 13+2*C+7*D+6*C*D*2^(D+1)

/-- **The run's cost is a fixed polynomial in its input**, degree `D+1`
(from `DimensionPower.cost_bound`, `Proof/PCP/ProjectionDimensionPowerBounds.lean`). -/
theorem poly_cost_polyBounded (D C n : ℕ) :
    ValidatorPolynomialDomination.PolyBounded (PCPSerializerCapacity.Power.budget D C n) n
      (polyCoefficient D C) (D+1) := by
  unfold ValidatorPolynomialDomination.PolyBounded PCPSerializerCapacity.Power.budget
    polyCoefficient
  have hc := DimensionPower.cost_bound D C (n+1) D le_rfl
  have hpos : 1 ≤ (n+1)^(D+1) := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hle : n+1 ≤ (n+1)^(D+1) := Nat.le_self_pow (by omega) _
  have h2 : (n+1+1)^(D+1) ≤ 2^(D+1)*(n+1)^(D+1) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) _
  have h6 := Nat.mul_le_mul_left (6*C*D) h2
  have e1 : D*(6*C*(n+1+1)^(D+1)+7) = 6*C*D*(n+1+1)^(D+1)+7*D := by ring
  have e2 : (13+2*C+7*D+6*C*D*2^(D+1))*(n+1)^(D+1) =
      13*(n+1)^(D+1)+2*C*(n+1)^(D+1)+7*D*(n+1)^(D+1)+6*C*D*(2^(D+1)*(n+1)^(D+1)) := by ring
  have hC : 2*C ≤ 2*C*(n+1)^(D+1) := Nat.le_mul_of_pos_right _ hpos
  have hD : 7*D ≤ 7*D*(n+1)^(D+1) := Nat.le_mul_of_pos_right _ hpos
  omega

/-- The driver value itself is `PolyBounded` at the same measure (degree `D`). -/
theorem value_polyBounded (D C n : ℕ) :
    ValidatorPolynomialDomination.PolyBounded (value D C n) n C D := le_rfl

end UnaryCalc
end
end NearCubicWires.BlockPlatform
