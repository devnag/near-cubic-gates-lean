import Proof.CaseAnalysis.WitnessSupportLiftHandoff

/-! Physical old/fresh projections are proved with an opaque state count,
before a large source control graph is substituted into the receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SupportLift
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (E : ℕ) {t : ℕ} (i : Fin t):=(ColdFamilyLift.old E i).castAdd 1
def fresh (E : ℕ) {t : ℕ} (i : Fin 3243):=(i.natAdd (t+1+FamilyCapacity.Call.extra E)).castAdd 1

theorem heads_old {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin t) :
    (receipt E bits prior).final.heads (old E i)=prior.final.heads i:=
  (TapeEmbedding.receipt_heads_old _ _ (ColdFamilyLift.receipt E bits prior) _).trans
    (ColdFamilyLift.heads_old E bits prior i)
theorem tapes_old {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin t) :
    (receipt E bits prior).final.tapes (old E i)=prior.final.tapes i:=
  (TapeEmbedding.receipt_tapes_old _ _ (ColdFamilyLift.receipt E bits prior) _).trans
    (ColdFamilyLift.tapes_old E bits prior i)
theorem heads_new {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin 3243) :
    (receipt E bits prior).final.heads (fresh (t:=t) E i)=0:=
  (TapeEmbedding.receipt_heads_old _ _ (ColdFamilyLift.receipt E bits prior) _).trans
    (ColdFamilyLift.heads_new E bits prior i)
theorem tapes_new {t s : ℕ} (E : ℕ) (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin 3243) :
    (receipt E bits prior).final.tapes (fresh (t:=t) E i)=[]:=
  (TapeEmbedding.receipt_tapes_old _ _ (ColdFamilyLift.receipt E bits prior) _).trans
    (ColdFamilyLift.tapes_new E bits prior i)
theorem base_heads_old {t s : ℕ} (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin t) :
    (base bits prior).final.heads (i.castAdd 1)=prior.final.heads i:=
  TapeEmbedding.receipt_heads_old _ _ prior i
theorem base_tapes_old {t s : ℕ} (bits : List Bool) (prior : ExecutionReceipt t s) (i : Fin t) :
    (base bits prior).final.tapes (i.castAdd 1)=prior.final.tapes i:=
  TapeEmbedding.receipt_tapes_old _ _ prior i

end NearCubicWires.RepairOrdinary.CloseoutWitness.SupportLift
