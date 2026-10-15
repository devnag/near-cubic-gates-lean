import Proof.CaseAnalysis.FinalSupplierTotality
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
open LocalBitMultitape SourceInterfaces RepairSource ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def StepAtInputs {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (budget : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), ∃ hout tout,
    Step p (budget n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) hout tout

/-- A docked receipt is the supplier's halting fact. -/
theorem total_of_stepAtInputs {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ) (h : StepAtInputs p ht result fuel) : Total p ht result fuel := by
  intro n x bits
  obtain ⟨_hout, _tout, r, hr, _, _, _⟩ := h n x bits
  exact ⟨r, hr⟩

theorem stepAtInputs_mono {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (budget fuel : ℕ → ℕ) (hle : ∀ n, budget n ≤ fuel n)
    (h : StepAtInputs p ht result budget) : StepAtInputs p ht result fuel := by
  intro n x bits
  obtain ⟨hout, tout, hstep⟩ := h n x bits
  exact ⟨hout, tout, Step.enlarge hstep (hle n)⟩

/-- End to end: a docked receipt at any sufficient budget discharges the
`ClosureAt.supplier` field, at the canonical meaning. -/
theorem allInputRun_of_stepAtInputs {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (budget fuel : ℕ → ℕ) (hle : ∀ n, budget n ≤ fuel n)
    (h : StepAtInputs p ht result budget) :
    AllInputRun p ht result fuel (decides p ht result fuel) :=
  allInputRun_of_total p ht result fuel
    (total_of_stepAtInputs p ht result fuel (stepAtInputs_mono p ht result budget fuel hle h))

end NearCubicWires.RepairOrdinary.CloseoutWitness.Weak
