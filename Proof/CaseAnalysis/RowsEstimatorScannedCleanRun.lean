import Proof.CaseAnalysis.RowsEstimatorScannedCleanJoin

/-! Symbolic finite-control join of the actual driver and cleanup donors.
Keeping callee controls abstract prevents unfolding thousands of fixed passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine a) (budget a row C) (input a row C) out ∧
      (∀ i : Fin 70,out (old a (i.castAdd (DriverLayout.tapes a)))=Scanned.output row C i) ∧
      out (driver a)=List.replicate (Driver.value a row.d row.p row.cuts.length C) true ∧
      out (fresh a 0)=[] ∧
      out (fresh a 1)=List.replicate (Driver.value a row.d row.p row.cuts.length C) true ∧
      out (fresh a 2)=List.replicate (Driver.value a row.d row.p row.cuts.length C+2) false ∧
      (∀ i,out (work a i)=List.replicate
        (DriverLayout.sweepCount a*Driver.value a row.d row.p row.cuts.length C) false) := by

  obtain ⟨before,hb,keepOld,hd⟩:=ScannedDriver.ready a row C
  have bound : ∀ i,(before (project a i)).length≤
      DriverLayout.sweepCount a*Driver.value a row.d row.p row.cuts.length C := by
    intro i
    exact ScannedDriver.private_support a row C before hb (project a i) (work_bounds a i).1
  have hc:=DriverCleanBank.ready (Driver.value a row.d row.p row.cuts.length C)
    (DriverLayout.sweepCount a) (fun i=>before (project a i)) bound
  obtain ⟨out,hr,hkeep,hd0,hzero,hd1,hlog,hw⟩:=join_generic a (ScannedDriver.machine a)
    (DriverCleanBank.machine (count a) (DriverLayout.sweepCount a)) _ _
    (Driver.value a row.d row.p row.cuts.length C) (DriverLayout.sweepCount a)
    (ScannedDriver.input a row C) before hb hd hc
  refine ⟨out,hr,?_,hd0,hzero,hd1,hlog,hw⟩
  intro i
  exact (hkeep i).trans (keepOld i)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedClean
