import Proof.Amplification.RecoveryColdValuationRetained

/-! The whole cold parser returns its actual native receipt and exact
ambient tape/head view. Its successful count/cursor evidence therefore
belongs to the same execution that prepared the original input tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev NativeReceipt := ExecutionReceipt 10 (Fintype.card (RecoveryCalls.Control RecoveryValuationCount.graphSizes))
def Returned (bits word : List Bool) (base : NativeReceipt) : Prop :=
  base.final.heads 7=0 ∧
  base.final.tapes 7=[(readList (cap bits) (readEntry (width bits)) word).isSome] ∧
  ∀ table tail,readList (cap bits) (readEntry (width bits)) word=some (table,tail) →
    ∃ count out,count≤cap bits ∧ out.width=width bits ∧ out.index=RecoveryColdHeader.zeroWord bits ∧
      out.source=frame word ∧ out.pos=2*(count*(width bits+2)+1) ∧
      tail=word.drop (count*(width bits+2)+1) ∧
      ZeroPadding.config (caps bits) base.final=RecoveryValuationCount.cfg out count (cap bits)
        (RecoveryCalls.controlCode RecoveryValuationCount.graphSizes none)

theorem cold_retained (bits word : List Bool) :
    ∃ c s base,runFrom machine (RecoveryValuationCount.limit (width bits) (cap bits))
        ⟨machine.start,heads,tapes bits word⟩=some base ∧ Returned bits word base ∧
      ∃ r,run coldMachine (coldBudget bits word) (input bits word)=some r ∧
        r.final.heads=(RecoveryFocus.config slots positioned (after bits word c s) base.final).heads ∧
        r.final.tapes=(RecoveryFocus.config slots positioned (after bits word c s) base.final).tapes := by
  obtain ⟨c,s,_,_,pre,hpre,hph,hpt⟩ := prefix_run bits word
  obtain ⟨base,hbase,hh,ht,hreturned⟩ := parser_retained bits word
  obtain ⟨scan,hscan,hf,_⟩ := RecoveryFocus.run_config slots slots_injective machine
    positioned (after bits word c s) (RecoveryValuationCount.limit (width bits) (cap bits)) _ base hbase
  rw [parser_input] at hscan
  obtain ⟨setup,hsetup,hsh,hst⟩ := setup_run bits word c s
  have hi : Composition.restart setup.final parserMachine.start=
      (⟨parserMachine.start,positioned,after bits word c s⟩ : Configuration 32 _) := by
    apply configuration_ext
    · rfl
    · exact hsh
    · exact hst
  rw [←hi] at hscan
  have he := Composition.run_join setupMachine parserMachine 1
    (RecoveryValuationCount.limit (width bits) (cap bits)) _ setup scan hsetup hscan
  rw [show 1+1+RecoveryValuationCount.limit (width bits) (cap bits)=
      RecoveryValuationCount.limit (width bits) (cap bits)+2 by omega] at he
  let entry := Composition.joinedReceipt setup scan
  have hentry : run entryMachine (RecoveryValuationCount.limit (width bits) (cap bits)+2)
      (before bits word c s)=some entry := he
  have hj : Composition.restart pre.final entryMachine.start=
      initialConfiguration entryMachine (before bits word c s) := by
    apply configuration_ext
    · rfl
    · exact hph
    · exact hpt
  unfold run at hentry
  rw [←hj] at hentry
  have h := Composition.run_join prefixMachine entryMachine (RecoveryColdPreliminary.budget bits word)
    (RecoveryValuationCount.limit (width bits) (cap bits)+2) _ pre entry hpre hentry
  let r := Composition.joinedReceipt pre entry
  have hr : run coldMachine (coldBudget bits word) (input bits word)=some r := h
  exact ⟨c,s,base,hbase,⟨hh,ht,hreturned⟩,r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf⟩

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
