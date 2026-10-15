import Proof.Amplification.RecoveryViewWholeBound

/-! The original witness and its physically produced length remain available
for the next valuation-bank copy. These are consequences of the same cold
execution, with no new input field or runtime work. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem boot_low (bits : List Bool) (a : Fin 100→List Bool) (i : Fin 100)
    (hi : i.val<32) : bootTapes bits a i=a i := by
  have hf : ¬bootFlag i := by
    intro h
    have hh := (flag_geometry i h).1
    omega
  have hn : i≠32 ∧ i≠63 ∧ i≠68 ∧ i≠62 ∧ i≠96 ∧ i≠53 ∧ i≠89 ∧ i≠98 := by
    simp only [ne_eq,Fin.ext_iff]
    omega
  simp only [bootTapes,hf,if_false,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
  simp only [Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
    Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2]

theorem prefix_retained (bits word : List Bool) (r : ExecutionReceipt 100 _)
    (hr : run prefixProgram (RecoveryColdValuation.resumedBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 1=frame word ∧ r.final.tapes 24=CompareMachine.word word.length ∧
      r.final.tapes 14=CompareMachine.word (width bits+1) := by
  obtain ⟨c,s,base,hbase,_,_,hgood⟩ := RecoveryColdValuation.resumed_success bits word
  obtain ⟨count,_,_,_,_,_,hw,_,_,hout⟩ := hgood table tail hp
  have he := embed_run RecoveryColdValuation.resumedMachine
    (RecoveryColdValuation.resumedBudget bits word) _ base hbase
  have heq := Option.some.inj (hr.symm.trans he)
  rw [heq]
  refine ⟨?_,?_,hw⟩
  · change base.final.tapes 1=frame word
    rw [hout 1 (by intro j; fin_cases j <;> decide)]
    exact RecoveryColdPreliminary.witness_retained bits word c s 0
  · change base.final.tapes 24=CompareMachine.word word.length
    rw [hout 24 (by intro j; fin_cases j <;> decide)]
    exact RecoveryColdPreliminary.witness_retained bits word c s 2

theorem cold_retained (bits word : List Bool) (r : ExecutionReceipt 100 _)
    (hr : run coldProgram (coldBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 1=frame word ∧ r.final.tapes 24=CompareMachine.word word.length ∧
      r.final.tapes 14=CompareMachine.word (width bits+1) := by
  obtain ⟨first,hfirst,hfh,hft,hgood⟩ := prefix_run bits word
  obtain ⟨count,_,_,hheads,hsrc,_,_⟩ := hgood table tail hp
  have hkeep := prefix_retained bits word first hfirst table tail hp
  have htrue : first.final.tapes 30=[true] := by simpa only [hp,Option.isSome_some] using hft
  obtain ⟨last,hlast,hlh,hlt⟩ := prepared_run bits (2*(count*(width bits+2)+1)) first.final.tapes hsrc
  rw [←hheads] at hlast
  obtain ⟨out,hout,_,_,hresult⟩ := initial_accept prefixProgram preparedProgram 30
    (RecoveryColdValuation.resumedBudget bits word) (bankBudget bits+2) _ first last hfirst hfh htrue hlast
  have he : RecoveryColdValuation.resumedBudget bits word+(bankBudget bits+2)+2=coldBudget bits word := by
    unfold coldBudget
    omega
  rw [he] at hout
  have hsame := Option.some.inj (hr.symm.trans hout)
  rw [hsame,hresult,hlt]
  simpa only [boot_low bits first.final.tapes 1 (by decide),
    boot_low bits first.final.tapes 24 (by decide),boot_low bits first.final.tapes 14 (by decide)] using hkeep

end NearCubicWires.RepairOrdinary.RecoveryColdView
