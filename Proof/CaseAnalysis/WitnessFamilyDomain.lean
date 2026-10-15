import Proof.CaseAnalysis.WitnessFamilyMeaning

/-! The exact successful family layout retains the original source-domain
cache template at its documented head, independently of output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem retained_domain (sym : Bool) (P V C T core W L km : ℕ) (q : ℚ) (bits : List Bool)
    (cursor : Fin 3243→ℕ) (data : Fin 3243→List Bool)
    (h:retained sym P V C T core W L km q bits cursor data) :
    cursor 2501=1 ∧ data 2501=UnaryTemplate.tape core:=by
  obtain ⟨extra,after,_hv,hh,ht,_store⟩:=h
  exact ⟨(congrFun hh 2501).trans rfl,(congrFun ht 2501).trans rfl⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
