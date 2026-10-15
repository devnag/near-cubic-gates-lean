import Proof.Gates.Recovery.AfterParts
import Proof.CaseAnalysis.Capacity

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP

/-- **Stage workspace and cost from the final address** (paper §11.6, formulas of size `2^{O(q)}`, `q ≤ n`). -/
def StageBudget (d : ℕ) : Prop :=
  ∃ A B C E : ℕ, ∀ (n w R : ℕ) (vals : List Bool) (hw : w ≤ R) {m : ℕ} (x : BitInput m),
    R ≤ n → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ CloseoutCapacity.capacity A B n ∧
    (DedupBytes.fields (unitPCP w vals)).length ≤ CloseoutCapacity.capacity A B n ∧
    2 ^ R ≤ CloseoutCapacity.capacity A B n ∧
    (0 < oracleSizeBound d R →
      UStage.cost d w R (CloseoutCapacity.capacity A B n) vals hw x ≤ C * (2 ^ n + 1) ^ E)

end NearCubicGates.Close.Recovery.After
