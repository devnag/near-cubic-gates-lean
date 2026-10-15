import Proof.Amplification.RecoveryValuationResume

/-! The cold execution now returns at zero on every scalar tape, retaining
only the actual certificate cursor on tape23. Syntax rejection retains its
false gate, and successful return exposes the physically written count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem resumed_run (bits word : List Bool) :
    ∃ c s base,Returned bits word base ∧
      ∃ r,run resumedMachine (resumedBudget bits word) (input bits word)=some r ∧
        r.final.heads=resumedHeads
          (RecoveryFocus.config slots positioned (after bits word c s) base.final).heads ∧
        r.final.tapes=(RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes := by
  obtain ⟨c,s,base,_,hb,first,hfirst,hh,ht⟩ := cold_retained bits word
  obtain ⟨last,hlast,hlh,hlt⟩ := resume_run first.final.heads first.final.tapes
  have h := Composition.run_join coldMachine resumeMachine (coldBudget bits word) 1
    _ first last hfirst hlast
  let r := Composition.joinedReceipt first last
  change run resumedMachine (coldBudget bits word+1+1) (input bits word)=some r at h
  have hr : run resumedMachine (resumedBudget bits word) (input bits word)=some r := by
    simpa only [resumedBudget,Nat.add_assoc] using h
  refine ⟨c,s,base,hb,r,hr,?_,?_⟩
  · exact hlh.trans (congrArg resumedHeads hh)
  · exact hlt.trans ht

theorem resumed_success (bits word : List Bool) :
    ∃ c s r,run resumedMachine (resumedBudget bits word) (input bits word)=some r ∧
      r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (cap bits) (readEntry (width bits)) word).isSome] ∧
      ∀ table tail,readList (cap bits) (readEntry (width bits)) word=some (table,tail) →
        ∃ count,count≤cap bits ∧ tail=word.drop (count*(width bits+2)+1) ∧
          r.final.heads=Function.update (fun _ : Fin 32=>0) 23 (2*(count*(width bits+2)+1)) ∧
          r.final.tapes 23=frame word ∧ r.final.tapes 31=CompareMachine.word count ∧
          r.final.tapes 14=CompareMachine.word (width bits+1) ∧
          r.final.tapes 21=CompareMachine.word (cap bits) ∧
          r.final.tapes 10=frame (RecoveryColdHeader.zeroWord bits) ∧
          ∀ i,(∀ j,slots j≠i) → r.final.tapes i=after bits word c s i := by
  obtain ⟨c,s,base,hb,r,hr,hh,ht⟩ := resumed_run bits word
  refine ⟨c,s,r,hr,?_,?_,?_⟩
  · rw [hh]
    change resumedHeads (RecoveryFocus.config slots positioned (after bits word c s) base.final).heads (slots 7)=0
    simpa only [resumedHeads,show ¬moves (slots 7) by decide,if_false,
      RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hb.1
  · rw [ht]
    change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 7)=_
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective] using hb.2.1
  · intro table tail hparse
    obtain ⟨count,out,hc,hw,hi,hs,hpos,htail,hp⟩ := hb.2.2 table tail hparse
    refine ⟨count,hc,htail,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hh,returned_heads bits word c s count base out hp,hpos]
    · rw [ht]
      change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 0)=_
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact (returned_tape bits base out count hp 0 (by decide)).trans hs
    · rw [ht]
      change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 8)=_
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact returned_tape bits base out count hp 8 (by decide)
    · rw [ht]
      change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 2)=_
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      have h := returned_tape bits base out count hp 2 (by decide)
      change base.final.tapes 2=CompareMachine.word (out.width+1) at h
      exact h.trans (congrArg (fun n=>CompareMachine.word (n+1)) hw)
    · rw [ht]
      change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 9)=_
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact returned_tape bits base out count hp 9 (by decide)
    · rw [ht]
      change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 3)=_
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      have h := returned_tape bits base out count hp 3 (by decide)
      change base.final.tapes 3=frame out.index at h
      exact h.trans (congrArg frame hi)
    · intro i houtside
      rw [ht]
      have hn : ¬∃j,slots j=i := by rintro ⟨j,hj⟩; exact houtside j hj
      simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
