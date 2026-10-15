import Proof.CaseAnalysis.WitnessFamilySupportPrefix
import Proof.CaseAnalysis.WitnessFamilyLiftHandoff

/-! The actual cold legal receipt enters the strengthened capacity/family
continuation through exactly the original source and policy fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportLift
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def receipt {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s):=
  TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>[]) (ColdFamilyLift.receipt E bits prior)
def base {t s : ℕ} (bits : List Bool) (prior : ExecutionReceipt t s):=
  TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>frame bits) prior

theorem heads {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) :
    (receipt E bits prior).final.heads=FamilySupportFromPolicy.heads E (base bits prior).final.heads []:=by
  change SupportDock.lift (ColdFamilyLift.receipt E bits prior).final.heads 0=_
  rw [ColdFamilyLift.heads]
  rfl

theorem tapes {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) :
    (receipt E bits prior).final.tapes=FamilySupportFromPolicy.input E (base bits prior).final.tapes []:=by
  change SupportDock.lift (ColdFamilyLift.receipt E bits prior).final.tapes []=_
  rw [ColdFamilyLift.tapes]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportLift
