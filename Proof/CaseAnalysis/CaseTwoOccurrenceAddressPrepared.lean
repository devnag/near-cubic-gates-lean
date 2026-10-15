import Proof.CaseAnalysis.CaseTwoOccurrenceAddressInput

/-! The actual original header and fixed schedule produce all occurrence
offsets before any address is read. The complete cache and both frames remain
available, and the subsequent crop/field banks are still literally empty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def prepare (D block : ℕ):=Composition.machine (metadata D) (widths D block)
def prepareBudget (D block : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity):=
  Metadata.budget r (a.output r)+1+Widths.budget D block r.arity (a.output r).clauseBits
structure Prepared (D block : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (address : List Bool) (A : Fin (tapes D) → List Bool) : Prop where
  source : ∀ j : Fin 19,A (base D (j.castAdd 39))=cache a r j
  arity : A (base D 53)=List.replicate r.arity true
  systematic : A (base D 28)=UnaryTemplate.tape (a.output r).systematicBits
  request : A (base D 56)=frame (pcppInput r)
  address : A (base D 57)=frame address
  length : A (scalarPort D 2)=List.replicate (r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1) true
  offset : A (scalarPort D 8)=List.replicate (block*(r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity+1)) true
  position : A (scalarPort D 14)=List.replicate (r.arity+RepairSource.CloseoutLanguage.clauseWidth D r.arity) true
  clause : A (scalarPort D 18)=List.replicate (a.output r).clauseBits true
  fresh : ∀ i,58+Widths.tapes D ≤ i.val → A i=[]

theorem prepared_run (D block : ℕ) (hD : 1 ≤ D) (a : PointwisePCPPAlgorithm)
    (r : PCPPRequest a.minimumArity) (address : List Bool) : ∃ out,
    runFrom (prepare D block) (prepareBudget D block a r)
      ⟨(prepare D block).start,heads D,input D a r address⟩=some out ∧
      out.steps ≤ prepareBudget D block a r ∧ out.final.heads=heads D ∧
      Prepared D block a r address out.final.tapes:=by
  obtain ⟨m,hm,ms,mh,mc,m52,m53,m28,_,m48⟩:=Metadata.metadata_run r (a.output r)
    PCPPQueryClauseReuse.heads (cache a r) (by rfl) (by rfl)
    (by simp [cache,PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data])
    (by simp [cache,PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data])
  obtain ⟨first,hfirst,_,fs,fh,ft,fkeep⟩:=RecoveryFocus.dock (metadataSlots D) (metadata_injective D)
    Metadata.machine _ (heads D) (input D a r address) _ (metadata_heads D)
    (metadata_input D a r address) m hm
  have firstH : first.final.heads=heads D:=by
    funext i
    by_cases hi : ∃ j,metadataSlots D j=i
    · obtain ⟨j,rfl⟩:=hi
      exact (fh j).trans ((congrFun mh j).trans (metadata_heads D j).symm)
    · exact (fkeep i (by intro j hj;exact hi ⟨j,hj⟩)).1
  have fresh (i : Fin (tapes D)) (hi : 56 ≤ i.val) :
      first.final.tapes i=input D a r address i:=
    (fkeep i (metadata_outside D i hi)).2
  obtain ⟨w,hw,w2,w8,w14,w18⟩:=Widths.widths_run D block r.arity (a.output r).clauseBits hD
  obtain ⟨last,hl,lh,lt,ls⟩:=hw.focus_at (widthSlots D) (width_injective D)
    first.final.heads first.final.tapes
    (by intro j
        by_cases h0 : j.val=0
        · simp only [widthSlots,h0,if_true,Widths.input]
          exact (ft 52).trans m52
        by_cases h1 : j.val=1
        · simp only [widthSlots,h1,if_true,Widths.input]
          exact (ft 48).trans m48
        have hj : 58 ≤ (widthSlots D j).val:=by
          simp only [widthSlots,h0,h1,if_false,Fin.val_mk];omega
        rw [fresh _ (by omega),new_input D a r address _ hj]
        simp only [Widths.input,h0,h1,if_false])
    (by intro j
        rw [firstH]
        by_cases h0 : j.val=0
        · simp only [widthSlots,h0,if_true];rfl
        by_cases h1 : j.val=1
        · simp only [widthSlots,h1,if_true];rfl
        exact new_head D _ (by simp only [widthSlots,h0,h1,if_false,Fin.val_mk];omega))
  have whole:=Composition.run_join (metadata D) (widths D block) _ _ _ first last hfirst hl
  have old (i : Fin (tapes D)) (hi : (i.val<58 ∧ i.val≠52 ∧ i.val≠48) ∨
      58+Widths.tapes D ≤ i.val) : last.final.tapes i=first.final.tapes i:=by
    rw [lt]
    exact install_other (widthSlots D) _ w i (width_outside D i hi)
  refine ⟨_,whole,?_,lh.trans firstH,?_⟩
  · change first.steps+1+last.steps ≤ _
    rw [fs]
    unfold prepareBudget
    omega
  · change Prepared D block a r address last.final.tapes
    constructor
    · intro j
      rw [old _ (Or.inl (by have h:=j.isLt;simp only [base,Fin.val_castAdd];omega))]
      exact (ft (j.castAdd 37)).trans (mc j)
    · rw [old _ (Or.inl (by simp [base]))]
      exact (ft 53).trans m53
    · rw [old _ (Or.inl (by simp [base]))]
      exact (ft 28).trans m28
    · rw [old _ (Or.inl (by simp [base])),fresh _ (by simp [base])]
      rfl
    · rw [old _ (Or.inl (by simp [base])),fresh _ (by simp [base])]
      rfl
    · rw [lt]
      exact (install_slot (widthSlots D) (width_injective D) _ w (Widths.scalarSlots D 2)).trans w2
    · rw [lt]
      exact (install_slot (widthSlots D) (width_injective D) _ w (Widths.scalarSlots D 8)).trans w8
    · rw [lt]
      exact (install_slot (widthSlots D) (width_injective D) _ w (Widths.scalarSlots D 14)).trans w14
    · rw [lt]
      exact (install_slot (widthSlots D) (width_injective D) _ w (Widths.scalarSlots D 18)).trans w18
    · intro i hi
      rw [old i (Or.inr hi),fresh i (by omega)]
      exact new_input D a r address i (by omega)

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
