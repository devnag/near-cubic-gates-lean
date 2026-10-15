import Proof.Gates.Codec.Copy
import Proof.Gates.Codec.Circuit
import Proof.Gates.Codec.ParityW
import Proof.Gates.Interfaces.Counter

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close

def CircuitSizeFit : Prop :=
  ∀ (q : ℕ) (C : Interfaces.NCircuit q) (W : ℕ), (Interfaces.circuitWord C).length + q + 2 ≤ W →
    Codec.CircuitFits (4 * W + 4) C ∧ Codec.circuitCost C ≤ 100000 * W ^ 3 ∧
      Codec.copyCircuitCost C ≤ 100000 * W ^ 3 ∧ ∀ cap V : ℕ, V + 20 * W + 20 ≤ cap → Codec.CopyFits cap V C

def RowSizeFit : Prop :=
  ∀ (q : ℕ) (row : List ℕ) (W : ℕ), (∀ x ∈ row, x < q) → row.length ≤ q → q + 2 ≤ W →
    Codec.rowCost row ≤ 100000 * W ^ 3 ∧
      (2 ^ (natBitLength row.length + 1) ≤ 4 * W + 4 ∧ row.length ≤ 4 * W + 4 ∧
        ∀ x ∈ row, natBitLength x + 1 ≤ 4 * W + 4) ∧
      (Interfaces.listWord natWord row).length ≤ 10 * W ^ 2

end NearCubicGates.Close.WorkerArith.WorkerBounds
