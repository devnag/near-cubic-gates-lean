import Proof.SourceAssembly.SourceSymmetricHeaderQuery
import Proof.MachineModel.ClosureLocalSupport

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblySymmetricBound
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
noncomputable section

theorem budget_le (q : Nat) : SourceAssemblySymmetricCold.budget q+1 ≤ Capacity.value q := by
  have hw : natBitLength q ≤ q+1:=Nat.add_le_add_right (Nat.log_le_self 2 q) 1
  simp only [SourceAssemblySymmetricCold.budget,
    SourceAssemblySymmetricScan.budget,SourceAssemblySymmetricScan.cost,
    SymmetricBody.cost,DecompositionSource.natWord_length,Capacity.value]
  nlinarith

theorem output_bound (q : Nat) (bits : List Bool) (j : Fin 2) :
    (SourceAssemblySymmetricScan.outputs q bits q j).length ≤ Capacity.value q := by
  have run:=SourceAssemblySymmetricCold.run q (Capacity.value q) bits
    (SourceAssemblySymmetricQuery.capacity_fit q)
  fin_cases j
  · exact P1Closure.LocalSupport.step_fits run 3 (Capacity.value q) (by simp [SourceAssemblySymmetricCold.input]) (by simpa only [Nat.zero_add] using budget_le q)
  · exact P1Closure.LocalSupport.step_fits run 4 (Capacity.value q) (by simp [SourceAssemblySymmetricCold.input]) (by simpa only [Nat.zero_add] using budget_le q)

end
end SourceAssemblySymmetricBound
