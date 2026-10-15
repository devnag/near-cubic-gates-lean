import Proof.CaseAnalysis.CaseTwoAssignmentPrepared

/-! Literal tape and head equalities of the already prepared systematic call.
They are independent of the large execution receipts which consume them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem systematic_entry_heads (a : PointwisePCPPAlgorithm) (j : Fin 13) :
    heads a (systematicSlots a j)=SystematicReady.heads j:=by
  fin_cases j <;>rfl

private theorem support_other (source : List Bool) (q C oldIndex index : ℕ)
    (j : Fin 9) (hj : j≠5) :
    PCPPQuerySupportReuse.data source q oldIndex C [] j=
      PCPPQuerySupportReuse.data source q index C [] j:=by
  fin_cases j <;>simp_all [PCPPQuerySupportReuse.data]

theorem systematic_outside (a : PointwisePCPPAlgorithm) (j : Fin 13) (hj : j≠5) :
    ∀ i,prepareSlots a i≠systematicSlots a j:=by
  apply prepare_outside
  fin_cases j <;>first | exact (hj rfl).elim | (simp [systematicSlots,low])

theorem systematic_input_data (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index oldIndex : ℕ) (j : Fin 13) (hj : j≠5) :
    input a r u index oldIndex (systematicSlots a j)=SystematicBit.data a r u index j:=by
  have other:=support_other (pcppOutput r (a.output r)) r.arity
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) oldIndex index
  fin_cases j
  · exact other 0 (by decide)
  · exact other 1 (by decide)
  · exact other 2 (by decide)
  · exact other 3 (by decide)
  · exact other 4 (by decide)
  · exact (hj rfl).elim
  · exact other 6 (by decide)
  · exact other 7 (by decide)
  · exact other 8 (by decide)
  all_goals rfl

theorem systematic_entry_data (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index oldIndex : ℕ) (A : Fin (tapes a) → List Bool)
    (p15 : A (low a 15)=UnaryTemplate.tape index)
    (keep : ∀ i,(∀ j,prepareSlots a j≠i) → A i=input a r u index oldIndex i)
    (j : Fin 13) : A (systematicSlots a j)=SystematicBit.data a r u index j:=by
  by_cases hj : j=5
  · subst j;exact p15
  · rw [keep _ (systematic_outside a j hj)]
    exact systematic_input_data a r u index oldIndex j hj

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
