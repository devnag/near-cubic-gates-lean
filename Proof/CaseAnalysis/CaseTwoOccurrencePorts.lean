import Proof.CaseAnalysis.CaseTwoOccurrenceLayout

/-! Literal semantic fields returned by the physical address front are the
entire entry of the physical bit worker. Only the old unused index differs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem cache_other (source : List Bool) (q index C : ℕ) (j : Fin 19) (hj : j≠14) :
    PCPPQueryIndexPadding.clauseData source q 0 C [] j=
      PCPPQueryClauseReuse.data source q index C [] j:=by
  fin_cases j <;>simp_all [PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data]

theorem port_data (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (clause : BitInput (a.output r).clauseBits) (position : Bool)
    (address : List Bool) (A : Fin (OccurrenceAddress.tapes D) → List Bool)
    (hA : OccurrenceAddress.Result D a r u clause position address A) (j : Fin 25) :
    A (inputPort D j)=OccurrenceBit.input a r u (binaryAddress clause).val position (OccurrenceBit.base a j):=by
  have pc (k : Fin 19) (hk : k≠14) : A (OccurrenceAddress.base D (k.castAdd 39))=
      OccurrenceBit.cache a r (binaryAddress clause).val k:=
    (hA.source k).trans (cache_other (pcppOutput r (a.output r)) r.arity (binaryAddress clause).val
      (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) k hk)
  fin_cases j
  · exact pc 0 (by decide)
  · exact pc 1 (by decide)
  · exact pc 2 (by decide)
  · exact pc 3 (by decide)
  · exact pc 4 (by decide)
  · exact pc 5 (by decide)
  · exact pc 6 (by decide)
  · exact pc 7 (by decide)
  · exact pc 8 (by decide)
  · exact pc 9 (by decide)
  · exact pc 10 (by decide)
  · exact pc 11 (by decide)
  · exact pc 12 (by decide)
  · exact pc 13 (by decide)
  · exact hA.clause
  · exact pc 15 (by decide)
  · exact pc 16 (by decide)
  · exact pc 17 (by decide)
  · exact pc 18 (by decide)
  · exact hA.request
  · exact hA.inputFrame
  · exact hA.inputRaw
  · exact hA.arity
  · exact hA.systematic
  · exact hA.position

theorem port_heads (D : ℕ) (a : PointwisePCPPAlgorithm) (j : Fin 25) :
    OccurrenceAddress.finalHeads D (inputPort D j)=OccurrenceBit.heads a (OccurrenceBit.base a j):=by
  have hv : (OccurrenceAddress.fieldSlots D 19).val=58+Widths.tapes D+8+19:=rfl
  simp only [OccurrenceAddress.finalHeads,Fin.ext_iff,OccurrenceAddress.heads,
    OccurrenceBit.heads,OccurrenceBit.base,OccurrenceBit.old,Fin.val_castAdd,port_value,hv]
  fin_cases j <;>norm_num <;>omega

theorem input_not_address (D : ℕ) (j : Fin 25) : inputPort D j≠OccurrenceAddress.base D 57:=by
  intro he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  change (inputPort D j).val=57 at h
  rw [port_value] at h
  split_ifs at h <;>omega
theorem address_outside (D : ℕ) (a : PointwisePCPPAlgorithm) :
    ∀ j,bitSlots D a j≠old D a (OccurrenceAddress.base D 57):=by
  intro j he
  by_cases hj : j.val<25
  · apply input_not_address D ⟨j.val,hj⟩
    apply old_injective D a
    simpa only [bitSlots,dif_pos hj] using he
  · have h:=congrArg Fin.val he
    have bound:=(OccurrenceAddress.base D 57).isLt
    simp only [bitSlots,dif_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at h
    omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Occurrence
