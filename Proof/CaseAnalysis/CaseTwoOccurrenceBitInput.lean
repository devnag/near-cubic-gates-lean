import Proof.CaseAnalysis.CaseTwoOccurrenceBitLayout

/-! Exact incoming cache and untouched honest-input ports for the physical
unsigned occurrence bit. The support projection is a literal bank projection. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem variable_input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : ℕ) (position : Bool) (j : Fin 59) :
    input a r u index position (variableSlots a j)=ClauseVariable.data a r index position j:=by
  fin_cases j <;>simp [variableSlots,variableMap,old,input,ClauseVariable.data,ClauseVariable.extra,cache,Fin.addCases]
theorem variable_heads (a : PointwisePCPPAlgorithm) (j : Fin 59) :
    heads a (variableSlots a j)=ClauseVariable.heads j:=by
  fin_cases j <;>simp [variableSlots,variableMap,old,heads,ClauseVariable.heads,PCPPQueryClauseReuse.heads,Fin.addCases]
theorem variable_fresh (a : PointwisePCPPAlgorithm) (i : Fin (tapes a)) (hi : 84 ≤ i.val) :
    ∀ j,variableSlots a j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have hb:=(variableMap j).isLt
  change (variableMap j).val=i.val at h
  omega
theorem variable_reserved (a : PointwisePCPPAlgorithm) (i : Fin 25) (hi : 19 ≤ i.val ∧ i.val<24) :
    ∀ j,variableSlots a j≠base a i:=by
  intro j he
  have h:=congrArg Fin.val he
  simp only [variableSlots,base,old,Fin.val_castAdd,variable_val] at h
  split_ifs at h <;>omega
theorem high_input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : ℕ) (position : Bool) (j : Fin (tapes a)) (hj : 25 ≤ j.val) :
    input a r u index position j=[]:=by
  simp only [input,dif_neg (show ¬j.val<19 by omega),show j.val≠19 by omega,
    show j.val≠20 by omega,show j.val≠21 by omega,show j.val≠22 by omega,
    show j.val≠23 by omega,show j.val≠24 by omega,if_false]
def supportMap : Fin 9 → Fin 19:=![0,1,2,13,15,14,16,17,18]
theorem support_data (source : List Bool) (q index C : ℕ) (j : Fin 9) :
    PCPPQueryClauseReuse.data source q index C [] (supportMap j)=
      PCPPQuerySupportReuse.data source q index C [] j:=by
  fin_cases j <;>simp [supportMap,PCPPQueryClauseReuse.data,PCPPQuerySupportReuse.data]

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
