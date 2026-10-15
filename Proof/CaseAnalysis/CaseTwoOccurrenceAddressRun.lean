import Proof.CaseAnalysis.CaseTwoOccurrenceAddressPrepared
import Proof.CaseAnalysis.CaseTwoOccurrenceAddressPorts

/-! Whole paid occurrence-address execution: original metadata, scheduled
widths, the actual fixed block crop, and actual input/clause/position fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def finalHeads (D : ℕ) (i : Fin (tapes D)):=if i=fieldSlots D 19 then 1 else heads D i
structure Result (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (clause : BitInput (a.output r).clauseBits)
    (position : Bool) (address : List Bool) (A : Fin (tapes D) → List Bool) : Prop where
  source : ∀ j : Fin 19,A (base D (j.castAdd 39))=cache a r j
  arity : A (base D 53)=List.replicate r.arity true
  systematic : A (base D 28)=UnaryTemplate.tape (a.output r).systematicBits
  request : A (base D 56)=frame (pcppInput r)
  address : A (base D 57)=frame address
  inputRaw : A (fieldSlots D 4)=List.ofFn u
  inputFrame : A (fieldSlots D 8)=frame (List.ofFn u)
  clause : A (fieldSlots D 19)=UnaryTemplate.tape (binaryAddress clause).val
  position : A (fieldSlots D 21)=[position]

theorem address_run (D block : ℕ) (hD : 1 ≤ D) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (clause : BitInput (a.output r).clauseBits) (pad pre tail : List Bool) (position : Bool)
    (hpad : (a.output r).clauseBits+pad.length=RepairSource.CloseoutLanguage.clauseWidth D r.arity)
    (hpre : pre.length=block*(r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1)) :
    let address:=pre++AddressFields.word u clause pad position++tail
    ∃ out,runFrom (machine D block) (budget D block a r pad.length (binaryAddress clause).val)
      ⟨(machine D block).start,heads D,input D a r address⟩=some out ∧
      out.steps ≤ budget D block a r pad.length (binaryAddress clause).val ∧
      out.final.heads=finalHeads D ∧ Result D a r u clause position address out.final.tapes:=by
  dsimp only
  let address:=pre++AddressFields.word u clause pad position++tail
  obtain ⟨p,hp,ps,ph,pd⟩:=prepared_run D block hD a r address
  have length : (AddressFields.word u clause pad position).length=
      r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1:=by
    simp only [AddressFields.word,List.length_append,List.length_ofFn,List.length_singleton]
    omega
  have pos : r.arity+(a.output r).clauseBits+pad.length=
      r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity:=by omega
  obtain ⟨c,hc,cf,_,c0,_,_⟩:=SliceFrame.slice_run pre (AddressFields.word u clause pad position) tail
  rw [hpre,length] at hc
  obtain ⟨middle,hm,mh,mt,ms⟩:=hc.focus_at (cropSlots D) (crop_injective D) p.final.heads p.final.tapes
    (by intro j;fin_cases j
        · exact pd.address
        · exact pd.fresh _ (by simp [cropSlots])
        · change p.final.tapes (scalarPort D 8)=List.replicate pre.length true
          rw [hpre];exact pd.offset
        · change p.final.tapes (scalarPort D 2)=List.replicate (AddressFields.word u clause pad position).length true
          rw [length];exact pd.length
        all_goals exact pd.fresh _ (by simp [cropSlots]))
    (by intro j;rw [ph]
        have hj:=crop_high D j
        simp only [heads,show (cropSlots D j).val≠13 by omega,
          show (cropSlots D j).val≠14 by omega,or_self,if_false])
  have middleH : middle.final.heads=heads D:=mh.trans ph
  have old (i : Fin (tapes D)) (hi : (i.val<58 ∧ i.val≠57) ∨
      58+Widths.tapes D+8 ≤ i.val) : middle.final.tapes i=p.final.tapes i:=by
    rw [mt]
    exact install_other (cropSlots D) _ c i (crop_outside D i hi)
  have scalar (j : Fin 22) (hj : 2 ≤ j.val) (h2 : j≠2) (h8 : j≠8) :
      middle.final.tapes (scalarPort D j)=p.final.tapes (scalarPort D j):=by
    rw [mt]
    exact install_other (cropSlots D) _ c _ (crop_scalar_outside D j hj h2 h8)
  obtain ⟨f,hf,fs,fh,_,f4,f8,f19,f21⟩:=AddressFields.fields_run u clause pad position
  have f1:=AddressRetention.arity_retained u clause pad position _ f hf
  obtain ⟨last,hl,_,ls,lh,lt,keep⟩:=RecoveryFocus.dock (fieldSlots D) (field_injective D)
    AddressFields.machine _ middle.final.heads middle.final.tapes _
    (by intro j;rw [middleH]
        have hj:=field_high D j
        simp only [heads,show (fieldSlots D j).val≠13 by omega,
          show (fieldSlots D j).val≠14 by omega,or_self,if_false]
        rfl)
    (by intro j
        by_cases h0 : j=0
        · subst j
          change middle.final.tapes (cropSlots D 6)=frame (AddressFields.word u clause pad position)
          rw [mt]
          exact (install_slot (cropSlots D) (crop_injective D) _ c 6).trans cf
        by_cases h1 : j=1
        · subst j
          exact (old (base D 53) (Or.inl (by simp [base]))).trans pd.arity
        by_cases h2 : j=2
        · subst j
          exact (scalar 18 (by decide) (by decide) (by decide)).trans pd.clause
        by_cases h3 : j=3
        · subst j
          change middle.final.tapes (scalarPort D 14)=List.replicate (r.arity+(a.output r).clauseBits+pad.length) true
          rw [pos]
          exact (scalar 14 (by decide) (by decide) (by decide)).trans pd.position
        have j0 : j.val≠0:=fun h=>h0 (Fin.ext h)
        have j1 : j.val≠1:=fun h=>h1 (Fin.ext h)
        have j2 : j.val≠2:=fun h=>h2 (Fin.ext h)
        have j3 : j.val≠3:=fun h=>h3 (Fin.ext h)
        have hj : 58+Widths.tapes D+8 ≤ (fieldSlots D j).val:=by
          simp only [fieldSlots,j0,j1,j2,j3,if_false,Fin.val_mk];omega
        rw [old _ (Or.inr hj),pd.fresh _ (by omega)]
        change []=AddressFields.input u clause pad position j
        simp only [AddressFields.input,h0,h1,h2,h3,if_false]) f hf
  have lastH : last.final.heads=finalHeads D:=by
    funext i
    by_cases hi : ∃ j,fieldSlots D j=i
    · obtain ⟨j,rfl⟩:=hi
      by_cases hj : j=19
      · subst j
        rw [finalHeads,if_pos rfl]
        exact (lh 19).trans (by rw [fh];rfl)
      · have hs : fieldSlots D j≠fieldSlots D 19:=fun h=>hj (field_injective D h)
        rw [finalHeads,if_neg hs]
        have low:=field_high D j
        simp only [heads,show (fieldSlots D j).val≠13 by omega,
          show (fieldSlots D j).val≠14 by omega,or_self,if_false]
        exact (lh j).trans (by rw [fh];exact if_neg hj)
    · have hn : i≠fieldSlots D 19:=by intro h;subst i;exact hi ⟨19,rfl⟩
      rw [finalHeads,if_neg hn]
      exact (keep i (by intro j hj;exact hi ⟨j,hj⟩)).1.trans (congrFun middleH i)
  have prior:=Composition.run_join (prepare D block) (crop D) _ _ _ p middle hp hm
  have whole:=Composition.run_join (Composition.machine (prepare D block) (crop D)) (fields D)
    _ _ _ _ last prior hl
  have live (i : Fin (tapes D)) (hi : i.val<58 ∧ i.val≠53 ∧ i.val≠57) :
      last.final.tapes i=p.final.tapes i:=
    (keep i (field_outside D i ⟨hi.1,hi.2.1⟩)).2.trans (old i (Or.inl ⟨hi.1,hi.2.2⟩))
  refine ⟨_,whole,?_,lastH,?_⟩
  · change p.steps+1+middle.steps+1+last.steps ≤ _
    rw [ls]
    unfold budget prepareBudget at *
    omega
  · change Result D a r u clause position address last.final.tapes
    constructor
    · intro j
      exact (live _ (by have hj:=j.isLt;simp only [base,Fin.val_castAdd];omega)).trans (pd.source j)
    · exact (lt 1).trans f1
    · exact (live _ (by simp [base])).trans pd.systematic
    · exact (live _ (by simp [base])).trans pd.request
    · rw [(keep _ (field_outside D _ (by simp [base]))).2,mt]
      exact (install_slot (cropSlots D) (crop_injective D) _ c 0).trans c0
    · exact (lt 4).trans f4
    · exact (lt 8).trans f8
    · exact (lt 19).trans f19
    · exact (lt 21).trans f21

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
