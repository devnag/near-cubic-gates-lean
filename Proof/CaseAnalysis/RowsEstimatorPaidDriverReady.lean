import Proof.CaseAnalysis.RowsEstimatorPaidDriver

/-! The concrete driver run has no supplier-Ready assumption. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def driver (a : WilliamsAlgorithm):=RecoveryFocus.machine (slots a (producer a)) (ScannedClean.machine a)
noncomputable def driverEntry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :=
  {initialConfiguration (driver a) (input a (producer a) row C fields out) with heads:=heads a (producer a) out}

def DriverResult {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (worker : Machine (tapes a p) s)
    (fuel : ℕ) (initial : Configuration (tapes a p) s) (row : EquationRow.Input) (C D : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) : Prop := ∃ extra r,
  runFrom worker fuel initial=some r ∧ r.final.heads=heads a p out ∧
    r.final.tapes=Fin.addCases (publicInput p row C D fields out) extra ∧ r.steps ≤ fuel ∧
    extra (ScannedClean.fresh a 1)=List.replicate D true

theorem driver_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (fields : Fin 7 → List Bool) (out : List Bool) :
    DriverResult a (producer a) (driver a) (ScannedClean.budget a row C) (driverEntry a row C fields out)
      row C (Driver.value a row.d row.p row.cuts.length C) fields out := by
  obtain ⟨localOut,hr,oldWords,dword,_zero,dcopy,_log,_work⟩:=ScannedClean.ready a row C
  exact driver_generic a (producer a) row C (Driver.value a row.d row.p row.cuts.length C) _ fields out
    (ScannedClean.machine a) localOut hr oldWords dword dcopy

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
