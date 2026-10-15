import Proof.CaseAnalysis.WitnessFamilySupportCall
import Proof.CaseAnalysis.WitnessFamilyFromPolicyLayout

/-! The original paid capacity prefix carries the added support stream
unchanged into the actual family dock. No copy or extra reset is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
namespace FamilySupportPrefix

def machine {t s : ℕ} (p : Machine t s):=TapeEmbedding.machine 1 (TapeEmbedding.machine 3243 p)
def receipt {t s : ℕ} (supports : List Bool) (r : ExecutionReceipt t s):=
  TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports)
    (TapeEmbedding.receipt (fun _ : Fin 3243=>0) (fun _=>[]) r)

theorem run_lift {t s : ℕ} (p : Machine t s) (fuel : ℕ) (cursor : Fin t→ℕ) (data : Fin t→List Bool)
    (supports : List Bool) (r : ExecutionReceipt t s)
    (hr:runFrom p fuel ⟨p.start,cursor,data⟩=some r) :
    runFrom (machine p) fuel
      ⟨(machine p).start,FamilySupportCall.heads cursor supports,FamilySupportCall.input data supports⟩=
      some (receipt supports r) := by
  have inner:=TapeEmbedding.run_embed p (fun _ : Fin 3243=>0) (fun _=>[]) _ _ r hr
  exact TapeEmbedding.run_embed (TapeEmbedding.machine 3243 p)
    (fun _ : Fin 1=>supports.length) (fun _=>supports) _ _ _ inner

theorem receipt_heads {t s : ℕ} (supports : List Bool) (r : ExecutionReceipt t s) :
    (receipt supports r).final.heads=FamilySupportCall.heads r.final.heads supports:=by
  funext i
  simp only [receipt,TapeEmbedding.receipt,TapeEmbedding.config,FamilySupportCall.heads,
    FamilyCold.Call.heads,SupportDock.lift]
theorem receipt_tapes {t s : ℕ} (supports : List Bool) (r : ExecutionReceipt t s) :
    (receipt supports r).final.tapes=FamilySupportCall.input r.final.tapes supports:=by
  funext i
  simp only [receipt,TapeEmbedding.receipt,TapeEmbedding.config,FamilySupportCall.input,
    FamilyCold.Call.input,SupportDock.lift]
theorem receipt_steps {t s : ℕ} (supports : List Bool) (r : ExecutionReceipt t s) :
    (receipt supports r).steps=r.steps:=rfl

end FamilySupportPrefix

namespace FamilySupportFromPolicy
open LocalBitMultitape
variable {t s : ℕ}
def first (E K : ℕ) (source : Fin t):=FamilySupportPrefix.machine (FamilyCapacity.Call.machine E K source)
def second (supplier : Machine 3244 s) (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  FamilySupportCall.machine supplier (FamilyFromPolicy.fields e E source count raw policy)
def machine (supplier : Machine 3244 s) (e E K : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  Composition.machine (first E K source) (second supplier e E source count raw policy)
def input (E : ℕ) (data : Fin t→List Bool) (supports : List Bool):=
  FamilySupportCall.input (FamilyCapacity.Call.input E data) supports
def heads (E : ℕ) (cursor : Fin t→ℕ) (supports : List Bool):=
  FamilySupportCall.heads (FamilyCapacity.Call.heads E cursor) supports

end FamilySupportFromPolicy
end
end NearCubicWires.RepairOrdinary.CloseoutWitness
