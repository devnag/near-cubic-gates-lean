import Proof.CaseAnalysis.RowsEstimatorPaidDriverFalse
import Proof.CaseAnalysis.RowsEstimatorPreparedRetained

/-! One actual enclosing receipt retains native metadata and every scratch cleanup fact. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem joined_embed_heads {n e s t : ℕ} (x : ExecutionReceipt (n+e) s)
    (y : ExecutionReceipt n t) (extra : Fin e → List Bool) :
    (Composition.joinedReceipt x (TapeEmbedding.receipt (fun _ : Fin e=>0) extra y)).final.heads=
      Fin.addCases y.final.heads (fun _ : Fin e=>0) := rfl

def Private (a : WilliamsAlgorithm) (extra : Fin (ScannedClean.tapes a) → List Bool) : Prop :=
  ∀ i,i≠ScannedClean.fresh a 1 → ∃ n,extra i=List.replicate n false
def Protected (p : Program) (row : EquationRow.Input) (C : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) : Prop :=
  ∀ i : Fin 70,i.val=52 ∨ i.val=68 →
    A (WarmPrepare.old p (i.castAdd (CloseoutRowsRawRecord.tapes p)))=Scanned.output row C i
def Owned {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (worker : Machine (tapes a p) s)
    (fuel bound : ℕ) (initial : Configuration (tapes a p) s) (row : EquationRow.Input) (C D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) : Prop := ∃ A extra r,
  runFrom worker fuel initial=some r ∧ r.final.heads=heads a p word ∧
    r.final.tapes=install (retireSlots a p) (Fin.addCases A extra) (fun _=>List.replicate D false) ∧
    r.steps ≤ bound ∧ Returned p D word fields A ∧ Private a extra ∧ Protected p row C A

def WarmOwned {s : ℕ} (a : WilliamsAlgorithm) (p : Program) (worker : Machine (tapes a p) s)
    (fuel bound : ℕ) (initial : Configuration (tapes a p) s) (row : EquationRow.Input) (C D : ℕ)
    (word : List Bool) (fields : Fin 7 → List Bool) : Prop := ∃ A extra r,
  runFrom worker fuel initial=some r ∧ r.final.heads=heads a p word ∧
    r.final.tapes=Fin.addCases A extra ∧ r.steps ≤ bound ∧ Returned p D word fields A ∧
    extra (ScannedClean.fresh a 1)=List.replicate D true ∧ Private a extra ∧ Protected p row C A

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
