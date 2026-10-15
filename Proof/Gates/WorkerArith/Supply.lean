import Proof.Gates.WorkerArith.Rest
import Proof.Gates.WorkerArith.Fit

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

/-- **The worker supply**, from the per-circuit and per-row size facts. -/
theorem workerSupply_of_fit (hCF : WorkerBounds.CircuitSizeFit) (hRF : WorkerBounds.RowSizeFit) (hSU : Setup.SetupSupply) :
    Closure.WorkerSupply :=
  workerSupply_of (hrest_of hCF hRF hSU)

theorem workerSupply (hSU : Setup.SetupSupply) : Closure.WorkerSupply :=
  workerSupply_of_fit WorkerBounds.circuitSizeFit WorkerBounds.rowSizeFit hSU

end NearCubicGates.Close.WorkerArith
