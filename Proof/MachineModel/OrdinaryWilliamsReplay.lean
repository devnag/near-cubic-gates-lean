import Proof.Foundations.RepresentationSourceContracts

/-! Execute the selected positive-power source and pay for returning its
output cursor. The extra tape records real source transitions; no head or
workspace reset is inferred from the source's output equation. -/
namespace NearCubicWires.RepairOrdinary.WilliamsReplay
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inputs (a : WilliamsAlgorithm) (r : ExactPowerRequest) : Fin a.tapeCount → List Bool :=
  fun tape => if tape.val = 0 then
    natWord r.dimension ++ WilliamsLoaderForms.rowMajorBitMatrix r.left
  else if tape.val = 1 then WilliamsLoaderForms.rowMajorBitMatrix r.right
  else []

def budget (a : WilliamsAlgorithm) (r : ExactPowerRequest) : ℕ :=
  a.coefficient * r.dimension ^ 2 * logScale r.dimension ^ a.logExponent

def machine (a : WilliamsAlgorithm) : Machine (a.tapeCount + 1) (a.stateCount + 2) :=
  Rewind.machine a.machine

theorem source_run (a : WilliamsAlgorithm) (r : ExactPowerRequest) :
    ∃ source : ExecutionReceipt a.tapeCount a.stateCount,
    ∃ actual : ExecutionReceipt (a.tapeCount + 1) (a.stateCount + 2),
      run a.machine (budget a r) (inputs a r) = some source ∧
      run (machine a) (2 * budget a r + 2)
        (Fin.addCases (inputs a r) (fun _ => [])) = some actual ∧
      actual.final.tapes (a.outputTape.castAdd 1) = r.output ∧
      (∀ i, actual.final.heads i = 0) ∧
      (∀ i : Fin a.tapeCount, actual.final.tapes (i.castAdd 1) = source.final.tapes i) ∧
      actual.steps = 2 * source.steps + 2 ∧
      actual.steps ≤ 2 * budget a r + 2 ∧
      actual.peakTapeCells ≤ source.peakTapeCells + source.steps := by
  obtain ⟨source, hs, hout⟩ := a.runs r
  obtain ⟨actual, ha, ht, hh, hsteps, hpeak⟩ := Rewind.reset_run a.machine (budget a r)
    (inputs a r) source hs
  have hb : source.steps ≤ budget a r := runFrom_steps_le a.machine _ _ source hs
  have hm := run_moreFuel (machine a) (2 * source.steps + 2)
    ((2 * budget a r + 2) - (2 * source.steps + 2)) _ actual ha
  rw [Nat.add_sub_of_le (by omega : 2 * source.steps + 2 ≤ 2 * budget a r + 2)] at hm
  exact ⟨source, actual, hs, hm, (ht a.outputTape).trans hout, hh, ht, hsteps, by omega, hpeak⟩

/-- The original source exponent survives the actual replay and reset. -/
theorem source_budget (a : WilliamsAlgorithm) (r : ExactPowerRequest) (q residual : ℕ)
    (hU : r.dimension ^ 2 ≤ 2 * residual) (hlog : logScale r.dimension ≤ q + 2) :
    2 * budget a r + 2 ≤ 4 * a.coefficient * residual * (q + 2) ^ a.logExponent + 2 := by
  have h := williams_residual_charge a.coefficient a.logExponent r.dimension q residual hU hlog
  dsimp only [budget]
  nlinarith

end NearCubicWires.RepairOrdinary.WilliamsReplay
