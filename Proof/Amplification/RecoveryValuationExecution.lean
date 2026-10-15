import Proof.Amplification.RecoveryValuationSetup

/-! Execute the first certificate parser after its paid setup, retaining
the literal Boolean parse result on global tape30 at head0. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focused_run (bits word : List Bool) (c s : Nat) :
    ∃ r,runFrom parserMachine (RecoveryValuationCount.limit (width bits) (cap bits))
        ⟨parserMachine.start,positioned,after bits word c s⟩=some r ∧
      r.final.heads 30=0 ∧ r.final.tapes 30=[(readList (cap bits) (readEntry (width bits)) word).isSome] := by
  obtain ⟨base,hbase,_,hh,ht⟩ := parser_run bits word
  obtain ⟨r,hr,hf,_⟩ := RecoveryFocus.run_config slots slots_injective machine
    positioned (after bits word c s) (RecoveryValuationCount.limit (width bits) (cap bits)) _ base hbase
  rw [parser_input] at hr
  refine ⟨r,hr,?_,?_⟩
  · rw [hf]
    change (RecoveryFocus.config slots positioned (after bits word c s) base.final).heads (slots 7)=0
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact hh
  · rw [hf]
    change (RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes (slots 7)=_
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    exact ht

noncomputable def entryMachine := Composition.machine setupMachine parserMachine

theorem entry_run (bits word : List Bool) (c s : Nat) :
    ∃ r,run entryMachine (RecoveryValuationCount.limit (width bits) (cap bits)+2)
        (before bits word c s)=some r ∧
      r.final.heads 30=0 ∧ r.final.tapes 30=[(readList (cap bits) (readEntry (width bits)) word).isSome] := by
  obtain ⟨first,hfirst,hfh,hft⟩ := setup_run bits word c s
  obtain ⟨last,hlast,hlh,hlt⟩ := focused_run bits word c s
  have hi : Composition.restart first.final parserMachine.start=
      (⟨parserMachine.start,positioned,after bits word c s⟩ : Configuration 32 _) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hi] at hlast
  have h := Composition.run_join setupMachine parserMachine 1
    (RecoveryValuationCount.limit (width bits) (cap bits)) _ first last hfirst hlast
  rw [show 1+1+RecoveryValuationCount.limit (width bits) (cap bits)=
      RecoveryValuationCount.limit (width bits) (cap bits)+2 by omega] at h
  exact ⟨Composition.joinedReceipt first last,h,hlh,hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
