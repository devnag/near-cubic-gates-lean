import Proof.CaseAnalysis.CaseTwoAssignmentPrepared
import Proof.CaseAnalysis.CaseTwoAuxiliaryInput
import Proof.CaseAnalysis.CaseTwoAssignmentPaths

/-! Complete auxiliary path through the original assignment dispatcher.
The actual systematic count is subtracted before the original honest call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem auxiliary_lower (a : PointwisePCPPAlgorithm) (j : Fin (AuxiliaryBit.tapes a)) :
    9 ≤ (auxiliarySlots a j).val:=by
  dsimp only [auxiliarySlots,low]
  split_ifs <;>simp only [Fin.val_castAdd,Fin.val_natAdd] <;>omega
theorem auxiliary_output (a : PointwisePCPPAlgorithm) :
    auxiliarySlots a (AuxiliaryBit.outputSlot a)=low a 25:=by
  have hb : 7 ≤ HonestCall.tapes a:=by unfold HonestCall.tapes;omega
  have h0 : (AuxiliaryBit.outputSlot a).val≠0:=by
    change HonestCall.tapes a+1≠0;omega
  have h1 : (AuxiliaryBit.outputSlot a).val≠1:=by
    change HonestCall.tapes a+1≠1;omega
  have hi : AuxiliaryBit.outputSlot a≠AuxiliaryBit.indexSlot a:=by
    intro he
    have h:=congrArg Fin.val he
    change HonestCall.tapes a+1=HonestCall.tapes a+0 at h
    omega
  simp only [auxiliarySlots,h0,h1,hi,if_false,if_true]

theorem auxiliary_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : Fin (a.output r).auxiliaryBits) (oldIndex : ℕ) : ∃ out,
    runFrom (machine a) (budget a r u ((a.output r).systematicBits+index.val))
      ⟨(machine a).start,heads a,input a r u ((a.output r).systematicBits+index.val) oldIndex⟩=some out ∧
      out.steps≤budget a r u ((a.output r).systematicBits+index.val) ∧
      out.final.tapes (low a 25)=[(a.output r).honestAuxiliary u index]:=by
  let selected:=(a.output r).systematicBits+index.val
  obtain ⟨p,hp,_,ph,p15,p17,p14,pkeep⟩:=prepared_run a r u selected oldIndex
  have flag : readTapeBit (p.final.tapes (low a 17)) (p.final.heads (low a 17))=true:=by
    rw [ph,p17]
    change readTapeBit [decide ((a.output r).systematicBits ≤ selected)] 0=true
    have hi : (a.output r).systematicBits ≤ selected:=by dsimp [selected];omega
    simp only [hi,decide_true]
    rfl
  obtain ⟨offsetOut,hd,d4⟩:=VariablePrep.auxiliary_run selected (a.output r).systematicBits
    (by dsimp [selected];omega)
  have value : selected-(a.output r).systematicBits=index.val:=by dsimp [selected];omega
  rw [value] at d4
  obtain ⟨q,hq,qh,qt,_⟩:=hd.focus_at (offsetSlots a) (offset_injective a) p.final.heads p.final.tapes
    (by intro j
        by_cases h0 : j=0
        · subst j;exact p15
        by_cases h1 : j=1
        · subst j;exact p14
        rw [pkeep _ (prepare_outside a _ (by fin_cases j <;>first | exact (h0 rfl).elim | exact (h1 rfl).elim | (simp [offsetSlots,low])))]
        have hz:=high_input a r u selected oldIndex (offsetSlots a j)
          (by fin_cases j <;>first | exact (h0 rfl).elim | exact (h1 rfl).elim | (simp [offsetSlots,low]))
        fin_cases j <;>first | exact (h0 rfl).elim | exact (h1 rfl).elim | exact hz)
    (by intro j;rw [ph];fin_cases j <;>rfl)
  have q21 : q.final.tapes (low a 21)=List.replicate index.val true:=by
    rw [qt]
    exact (install_slot (offsetSlots a) (offset_injective a) _ offsetOut 4).trans d4
  have kept (i : Fin (tapes a)) (hi : i.val < 13 ∨ 24 < i.val) :
      q.final.tapes i=input a r u selected oldIndex i:=by
    rw [qt,install_other (offsetSlots a) _ _ i (offset_outside a i (by omega))]
    exact pkeep i (prepare_outside a i (by omega))
  obtain ⟨bout,hb,bit⟩:=AuxiliaryBit.bit_run a r u index
  have bt (j : Fin (AuxiliaryBit.tapes a)) :
      q.final.tapes (auxiliarySlots a j)=AuxiliaryBit.input a r u index.val j:=by
    rw [AuxiliaryBit.input_flat]
    by_cases h0 : j.val=0
    · simp only [h0,if_true,auxiliarySlots]
      rw [kept _ (Or.inl (by simp [low]))]
      rfl
    by_cases h1 : j.val=1
    · simp only [h1,if_true,auxiliarySlots]
      rw [kept _ (Or.inl (by simp [low]))]
      rfl
    by_cases hindex : j.val=HonestCall.tapes a
    · have he : j=AuxiliaryBit.indexSlot a:=by apply Fin.ext;exact hindex
      rw [if_neg h0,if_neg h1,if_pos hindex]
      rw [auxiliarySlots,if_neg h0,if_neg h1,if_pos he]
      exact q21
    have hindex' : j≠AuxiliaryBit.indexSlot a:=by
      intro he;apply hindex;have hv:=congrArg Fin.val he;exact hv
    simp only [h0,h1,hindex,if_false,auxiliarySlots,hindex']
    by_cases hout : j=AuxiliaryBit.outputSlot a
    · simp only [hout,if_true]
      rw [kept _ (Or.inr (by simp [low]))]
      exact high_input a r u selected oldIndex _ (by simp [low])
    · simp only [hout,if_false]
      rw [kept _ (Or.inr (by simp;omega))]
      exact high_input a r u selected oldIndex _ (by simp;omega)
  obtain ⟨last,hl,_,lt,_⟩:=hb.focus_at (auxiliarySlots a) (auxiliary_injective a) q.final.heads q.final.tapes bt
    (by intro j;rw [qh,ph];exact high_heads a _ (by have h:=auxiliary_lower a j;omega))
  let used:=VariablePrep.budget selected (a.output r).systematicBits+1+
    (VariablePrep.auxiliaryBudget selected (a.output r).systematicBits+1)+
    (AuxiliaryBit.budget a r u index.val+1)
  obtain ⟨out,ho,os,_,ot⟩:=AssignmentPaths.three (sizes a) (programs a) 0 (next a) 2 3
    (VariablePrep.budget selected (a.output r).systematicBits)
    (VariablePrep.auxiliaryBudget selected (a.output r).systematicBits)
    (AuxiliaryBit.budget a r u index.val) (heads a) (input a r u selected oldIndex) p q last hp hq hl
    (by change some (if readTapeBit (p.final.tapes (low a 17))
          (p.final.heads (low a 17)) then (2 : Fin 4) else 1)=some 2
        rw [flag];rfl) (by rfl) (by rfl)
  have hbound : used ≤ budget a r u selected:=by unfold used budget;rw [value];omega
  have more:=runFrom_moreFuel (machine a) used (budget a r u selected-used) _ out ho
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨out,more,os.trans hbound,?_⟩
  rw [ot]
  change last.final.tapes (low a 25)=_
  rw [lt,←auxiliary_output a]
  exact (install_slot (auxiliarySlots a) (auxiliary_injective a) _ bout _).trans bit

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
