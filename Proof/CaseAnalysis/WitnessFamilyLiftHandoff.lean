import Proof.CaseAnalysis.WitnessFamilyLift

/-! Exact prepared heads/tapes of the retained three-bank lift, proved
before instantiating the large original-source control type. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) :
    (receipt E bits r).final.heads=FamilyFromPolicy.heads E
      (TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>frame bits) r).final.heads:=rfl

theorem tapes (E : ℕ) {t s : ℕ} (bits : List Bool) (r : ExecutionReceipt t s) :
    (receipt E bits r).final.tapes=FamilyFromPolicy.input E
      (TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>frame bits) r).final.tapes:=rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilyLift
