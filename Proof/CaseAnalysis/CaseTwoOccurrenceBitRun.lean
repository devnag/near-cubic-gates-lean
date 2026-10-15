import Proof.CaseAnalysis.CaseTwoOccurrenceBitInput

/-! One complete original unsigned occurrence bit: actual cached clause
query, original literal decoding, paid result clear, and the selected original
systematic parity or honest auxiliary execution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem cache_slot (a : PointwisePCPPAlgorithm) (j : Fin 19) :
    variableSlots a (ClauseVariable.querySlots j)=base a (j.castAdd 6):=by
  apply Fin.ext
  simp only [variableSlots,ClauseVariable.querySlots,old,base,Fin.val_castAdd,variable_val,
    if_pos j.isLt]

theorem bit_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool) : ∃ out,
    runFrom (machine a) (budget a r u index position)
      ⟨(machine a).start,heads a,input a r u index.val position⟩=some out ∧
      out.steps ≤ budget a r u index position ∧
      out.final.tapes (outputSlot a)=
        [(a.output r).assignment u ((a.output r).honestAuxiliary u) (named a r index position)]:=by
  obtain ⟨v,hv,vs,vh,vc,v57⟩:=ClauseVariable.variable_run a r index position
  rw [selected_named a r index position] at v57
  obtain ⟨first,hfirst,_,fs,fh,ft,fkeep⟩:=RecoveryFocus.dock (variableSlots a) (variable_injective a)
    ClauseVariable.machine _ (heads a) (input a r u index.val position) _ (variable_heads a)
    (variable_input a r u index.val position) v hv
  have firstH : first.final.heads=heads a:=by
    funext i
    by_cases hi : ∃ j,variableSlots a j=i
    · obtain ⟨j,rfl⟩:=hi
      exact (fh j).trans ((congrFun vh j).trans (variable_heads a j).symm)
    · exact (fkeep i (by intro j hj;exact hi ⟨j,hj⟩)).1
  have firstCache (j : Fin 19) : first.final.tapes (base a (j.castAdd 6))=cache a r index.val j:=by
    rw [←cache_slot a j]
    exact (ft (ClauseVariable.querySlots j)).trans (vc j)
  have reserved (j : Fin 25) (hj : 19 ≤ j.val ∧ j.val<24) :
      first.final.tapes (base a j)=input a r u index.val position (base a j):=
    (fkeep _ (variable_reserved a j hj)).2
  have fresh (j : Fin (tapes a)) (hj : 84 ≤ j.val) : first.final.tapes j=[]:=by
    rw [(fkeep j (variable_fresh a j hj)).2]
    exact high_input a r u index.val position j (by omega)
  have projection (j : Fin 9) :
      first.final.tapes (old a (assignmentMap (j.castAdd 6)))=
        PCPPQuerySupportReuse.data (pcppOutput r (a.output r)) r.arity index.val
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j:=by
    have slot : old a (assignmentMap (j.castAdd 6))=base a ((supportMap j).castAdd 6):=by
      fin_cases j <;>rfl
    rw [slot]
    exact (firstCache (supportMap j)).trans (support_data _ _ _ _ j)
  have firstHeads (k : Fin 15) : heads a (old a (assignmentMap k))=
      Assignment.heads a (Assignment.low a (k.castAdd 15)):=by
    fin_cases k <;>rfl
  have firstInput (k : Fin 15) : first.final.tapes (old a (assignmentMap k))=
      Assignment.input a r u (named a r index position).val index.val
        (Assignment.low a (k.castAdd 15)):=by
    fin_cases k
    · exact projection 0
    · exact projection 1
    · exact projection 2
    · exact projection 3
    · exact projection 4
    · exact projection 5
    · exact projection 6
    · exact projection 7
    · exact projection 8
    · exact reserved 19 (by decide)
    · exact reserved 20 (by decide)
    · exact reserved 22 (by decide)
    · exact reserved 21 (by decide)
    · exact (ft 57).trans v57
    · exact reserved 23 (by decide)
  obtain ⟨s,hs,ss,sbit⟩:=Assignment.bit_run a r u (named a r index position) index.val
  obtain ⟨last,hl,_,ls,_,lt,_⟩:=RecoveryFocus.dock (assignmentSlots a) (assignment_injective a)
    (Assignment.machine a) _ first.final.heads first.final.tapes _
    (by intro j
        change first.final.heads (assignmentSlots a j)=Assignment.heads a j
        rw [firstH]
        by_cases hj : j.val<15
        · let k : Fin 15:=⟨j.val,hj⟩
          have he : j=Assignment.low a (k.castAdd 15):=Fin.ext rfl
          rw [he]
          simp only [assignmentSlots,Assignment.low,Fin.val_castAdd,dif_pos k.isLt]
          exact firstHeads k
        · have h3 : j.val≠3:=by omega
          have h5 : j.val≠5:=by omega
          simp only [assignmentSlots,dif_neg hj,heads,Fin.val_natAdd,
            show 84+j.val≠13 by omega,show 84+j.val≠14 by omega,or_self,if_false,
            Assignment.heads,h3,h5])
    (by intro j
        change first.final.tapes (assignmentSlots a j)=
          Assignment.input a r u (named a r index position).val index.val j
        by_cases hj : j.val<15
        · let k : Fin 15:=⟨j.val,hj⟩
          have he : j=Assignment.low a (k.castAdd 15):=Fin.ext rfl
          rw [he]
          simp only [assignmentSlots,Assignment.low,Fin.val_castAdd,dif_pos k.isLt]
          exact firstInput k
        · rw [assignmentSlots,dif_neg hj,fresh _ (by simp)]
          exact (Assignment.high_input a r u (named a r index position).val index.val j (by omega)).symm) s hs
  have whole:=Composition.run_join (queryVariable a) (assignment a) _ _ _ first last hfirst hl
  refine ⟨_,whole,?_,(lt (Assignment.low a 25)).trans sbit⟩
  change first.steps+1+last.steps ≤ _
  rw [fs,ls]
  unfold budget
  omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
