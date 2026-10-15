import Proof.CaseAnalysis.CaseTwoWholeBlockInput

/-! The whole original Case 2 block: paid source reconstruction, paid cache,
actual occurrence address and original unsigned honest assignment bit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
private theorem cache_heads (i : Fin 19) :
    PCPPQueryClauseReuse.heads i=if i.val=13 ∨ i.val=14 then 1 else 0:=by
  fin_cases i <;>rfl
private theorem cache_entry_heads (D : ℕ) (a : PointwisePCPPAlgorithm) (i : Fin 19) :
    Occurrence.heads D a (Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)))=
      PCPPQueryClauseReuse.heads i:=by
  simp only [Occurrence.heads,Occurrence.old,Fin.addCases_left,OccurrenceAddress.heads,
    OccurrenceAddress.base,Fin.val_castAdd]
  exact (cache_heads i).symm
def request {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)):=
  PCPPRequestBoundary.request a
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
def budget {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad)
    (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D block : ℕ) (u : BitInput (request source a H Cpad hpad r oracle).arity)
    (clause : BitInput (a.output (request source a H Cpad hpad r oracle)).clauseBits)
    (position : Bool) (padding : ℕ):=
  SourceBlock.budget source a H Cpad hpad r oracle+1+
    Occurrence.budget D block a (request source a H Cpad hpad r oracle) u clause position padding

theorem block_run {k : ℕ} (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ)
    (hcoeff : H.coefficient≤Cpad) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (D block : ℕ) (hD : 1≤D)
    (u : BitInput (request source a H Cpad hpad r oracle).arity)
    (clause : BitInput (a.output (request source a H Cpad hpad r oracle)).clauseBits)
    (pad pre tail : List Bool) (position : Bool)
    (hcap : (a.output (request source a H Cpad hpad r oracle)).clauseBits+pad.length=
      CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity)
    (hpre : pre.length=block*((request source a H Cpad hpad r oracle).arity+
      CloseoutLanguage.clauseWidth D (request source a H Cpad hpad r oracle).arity+1)) :
    let address:=pre++AddressFields.word u clause pad position++tail
    let req:=request source a H Cpad hpad r oracle
    ∃ out,run (machine source a k D block H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (budget source a H Cpad hpad r oracle D block u clause position pad.length)
      (input source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address)=some out ∧
      out.steps≤budget source a H Cpad hpad r oracle D block u clause position pad.length ∧
      out.final.tapes (outputSlot source a k D)=
        [(a.output req).assignment u ((a.output req).honestAuxiliary u)
          (OccurrenceBit.named a req (binaryAddress clause) position)] ∧
      ∀ i : Fin 3,out.final.tapes (old source a k D (SourceBlock.old source a k (i.castAdd 5)))=
        ![frame (HierarchySourceInput.hierarchyInput H r),frame (PCPPNative.descriptor oracle),frame address] i:=by
  dsimp only
  let req:=request source a H Cpad hpad r oracle
  let address:=pre++AddressFields.word u clause pad position++tail
  obtain ⟨sr,hsr,ss,sc,sh,srq,srqh,ret,retH⟩:=SourceBlock.block_run source a H Cpad hcoeff hpad r oracle address
  obtain ⟨p,hp,_,ps,ph,pt,pkeep⟩:=RecoveryFocus.dock (old source a k D) (old_injective source a k D)
    (SourceBlock.machine source a k H.coefficient Cpad (VerifierEncoding.code H.verifier)) _
    (fun _=>0) (input source a k D (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) address) _
    (by intro j;rfl) (by intro j;exact Fin.addCases_left j) sr hsr
  have fresh (j : Fin (Occurrence.tapes D a)) :
      p.final.heads (j.natAdd (SourceBlock.tapes source a k))=0 ∧
      p.final.tapes (j.natAdd (SourceBlock.tapes source a k))=[]:=by
    have outside : ∀ i,old source a k D i≠j.natAdd (SourceBlock.tapes source a k):=by
      intro i he
      have hv:=congrArg Fin.val he
      have hi:=i.isLt
      simp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simpa only [input,Fin.addCases_right] using pkeep _ outside
  obtain ⟨occ,ho,os,obit,oa⟩:=Occurrence.run D block hD a req u clause pad pre tail position hcap hpre
  obtain ⟨lastReceipt,hl,_,ls,_,lt,keep⟩:=RecoveryFocus.dock (slots source a k D) (slots_injective source a k D)
    (Occurrence.machine D block a) _ p.final.heads p.final.tapes _
    (by intro j
        change p.final.heads (slots source a k D j)=Occurrence.heads D a j
        by_cases h19 : j.val<19
        · let i : Fin 19:=⟨j.val,h19⟩
          have he : j=Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)):=Fin.ext rfl
          rw [he,cache_slot,cache_entry_heads]
          exact (ph _).trans (sh i)
        by_cases h56 : j.val=56
        · have he : j=Occurrence.old D a (OccurrenceAddress.base D 56):=Fin.ext h56
          rw [he,request_slot]
          exact (ph _).trans srqh
        by_cases h57 : j.val=57
        · have he : j=Occurrence.old D a (OccurrenceAddress.base D 57):=Fin.ext h57
          rw [he,address_slot]
          exact (ph _).trans (retH 2)
        · have hn : ¬shared j:=by unfold shared;omega
          rw [slots,if_neg hn,(fresh j).1]
          exact (fresh_input a D req address j hn).2.symm)
    (by intro j
        change p.final.tapes (slots source a k D j)=Occurrence.input D a req address j
        by_cases h19 : j.val<19
        · let i : Fin 19:=⟨j.val,h19⟩
          have he : j=Occurrence.old D a (OccurrenceAddress.base D (i.castAdd 39)):=Fin.ext rfl
          rw [he,cache_slot,input_flat]
          simp only [Occurrence.old,OccurrenceAddress.base,Fin.val_castAdd]
          rw [dif_pos i.isLt]
          exact (pt _).trans (sc i)
        by_cases h56 : j.val=56
        · have he : j=Occurrence.old D a (OccurrenceAddress.base D 56):=Fin.ext h56
          rw [he,request_slot]
          exact (pt _).trans srq
        by_cases h57 : j.val=57
        · have he : j=Occurrence.old D a (OccurrenceAddress.base D 57):=Fin.ext h57
          rw [he,address_slot]
          exact (pt _).trans (ret 2)
        · have hn : ¬shared j:=by unfold shared;omega
          rw [slots,if_neg hn,(fresh j).2]
          exact (fresh_input a D req address j hn).1.symm) occ ho
  have whole:=Composition.run_join (first source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (last source a k D block) _ _ _ p lastReceipt hp hl
  refine ⟨_,whole,?_,(lt (Occurrence.outputSlot D a)).trans obit,?_⟩
  · change p.steps+1+lastReceipt.steps≤_
    rw [ps,ls]
    change sr.steps+1+occ.steps≤SourceBlock.budget source a H Cpad hpad r oracle+1+
      Occurrence.budget D block a req u clause position pad.length
    exact Nat.add_le_add (Nat.add_le_add_right ss 1) os
  · intro i
    by_cases hi : i.val<2
    · let j : Fin 2:=⟨i.val,hi⟩
      exact (keep _ (slots_away source a k D j)).2.trans ((pt _).trans (ret i))
    · have he : i=2:=Fin.ext (by have hb:=i.isLt;omega)
      subst i
      change lastReceipt.final.tapes (old source a k D (SourceBlock.old source a k 2))=frame address
      rw [←address_slot]
      exact (lt _).trans oa

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.WholeBlock
