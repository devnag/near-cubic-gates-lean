import Proof.CaseAnalysis.RowsEstimatorScannedDriverJoin
import Proof.CaseAnalysis.RowsEstimatorDriverSupport

/-! The actual focused driver receipt bounds its fresh physical bank.
No local-output identification or additional scan is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem driver_val (a : WilliamsAlgorithm) : (driver a).val=70+(97+2*DriverLayout.e a) := by
  unfold driver slots DriverPorts.slots DriverLayout.output
  simp [show ¬97+2*DriverLayout.e a<4 by omega]

theorem private_support (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (out : Fin (tapes a) → List Bool)
    (hr : ClockJoin.ReadyRun (machine a) (DriverLayout.budget a row.d row.p row.cuts.length C)
      (input a row C) out) (i : Fin (tapes a)) (hi : 70 ≤ i.val) :
    (out i).length≤DriverLayout.sweepCount a*Driver.value a row.d row.p row.cuts.length C := by
  obtain ⟨r,run,rt,_rh,_rs⟩:=hr
  have hz : input a row C i=[] := by
    let j : Fin (DriverLayout.tapes a):=⟨i.val-70,by have ht:=i.isLt;dsimp [tapes] at ht;omega⟩
    have he : i=j.natAdd 70:=Fin.ext (by dsimp [j];omega)
    rw [he]
    simp only [input,Fin.addCases_right]
  have hb:=DriverLayout.fuel_support a row.d row.p row.cuts.length C
  have h:=CloseoutRowsProjectionReset.scratch_support (machine a)
    (DriverLayout.budget a row.d row.p row.cuts.length C)
    (DriverLayout.sweepCount a*Driver.value a row.d row.p row.cuts.length C)
    _ r run i rfl (by change (input a row C i).length≤_;rw [hz];simp) (by omega)
  rw [rt] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
