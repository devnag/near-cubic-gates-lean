import Proof.Amplification.RecoverySATBound

/-! Original binary input retention for reuse of the checked cold scanner.
No fresh copy of code bits or certificate grammar implementation is needed. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem preliminary_original (bits word : List Bool) (c s : Nat) :
    RecoveryColdPreliminary.output bits word c s 0=frame bits := by
  have hp := RecoveryColdPreliminary.header_retained bits word c s 0
  have hc := cap_kept bits c s 0 (by decide)
  have hh : RecoveryColdHeader.output bits c s 0=frame bits :=
    install_other RecoveryColdHeader.driverSlots _ _ _ (by intro k; fin_cases k <;> decide)
  exact hp.trans (hc.trans hh)

theorem prefix_original (bits word : List Bool) (r : ExecutionReceipt 100 _)
    (hr : run prefixProgram (RecoveryColdValuation.resumedBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 0=frame bits := by
  obtain ⟨c,s,base,hbase,_,_,hgood⟩ := RecoveryColdValuation.resumed_success bits word
  obtain ⟨_,_,_,_,_,_,_,_,_,hout⟩ := hgood table tail hp
  have he := embed_run RecoveryColdValuation.resumedMachine
    (RecoveryColdValuation.resumedBudget bits word) _ base hbase
  have heq := Option.some.inj (hr.symm.trans he)
  rw [heq]
  change base.final.tapes 0=frame bits
  rw [hout 0 (by intro j; fin_cases j <;> decide)]
  exact preliminary_original bits word c s

theorem cold_original (bits word : List Bool) (r : ExecutionReceipt 100 _)
    (hr : run coldProgram (coldBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 0=frame bits := by
  obtain ⟨first,hfirst,hfh,hft,hgood⟩ := prefix_run bits word
  obtain ⟨count,_,_,hheads,hsrc,_,_⟩ := hgood table tail hp
  have hkeep := prefix_original bits word first hfirst table tail hp
  have htrue : first.final.tapes 30=[true] := by simpa only [hp,Option.isSome_some] using hft
  obtain ⟨last,hlast,_,hlt⟩ := prepared_run bits (2*(count*(width bits+2)+1)) first.final.tapes hsrc
  rw [←hheads] at hlast
  obtain ⟨out,hout,_,_,hresult⟩ := initial_accept prefixProgram preparedProgram 30
    (RecoveryColdValuation.resumedBudget bits word) (bankBudget bits+2) _ first last hfirst hfh htrue hlast
  have he : RecoveryColdValuation.resumedBudget bits word+(bankBudget bits+2)+2=coldBudget bits word := by
    unfold coldBudget
    omega
  rw [he] at hout
  have hsame := Option.some.inj (hr.symm.trans hout)
  rw [hsame,hresult,hlt,boot_low bits first.final.tapes 0 (by decide)]
  exact hkeep
end NearCubicWires.RepairOrdinary.RecoveryColdView

namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_original (bits word : List Bool) (r : ExecutionReceipt 172 _)
    (hr : run prefixProgram (RecoveryColdView.coldBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 0=frame bits := by
  obtain ⟨base,hbase,_,_,_,_⟩ := RecoveryColdView.cold_run bits word
  have hk := RecoveryColdView.cold_original bits word base hbase table tail hp
  have he := embed_run RecoveryColdView.coldProgram (RecoveryColdView.coldBudget bits word) _ base hbase
  have heq := Option.some.inj (hr.symm.trans he)
  rw [heq]
  exact hk

theorem cold_original (bits word : List Bool) (r : ExecutionReceipt 172 _)
    (hr : run coldProgram (coldBudget bits word) (input bits word)=some r)
    (table : List (Nat×Bool)) (tail : List Bool)
    (hp : readList (limit bits) (readEntry (width bits)) word=some (table,tail)) :
    r.final.tapes 0=frame bits := by
  obtain ⟨first,hfirst,hfh,hft,hgood⟩ := prefix_run bits word
  obtain ⟨pos,hheads,hsrc,_⟩ := hgood table tail hp
  have hkeep := prefix_original bits word first hfirst table tail hp
  have htrue : first.final.tapes 30=[true] := by simpa only [hp,Option.isSome_some] using hft
  obtain ⟨last,hlast,_,hlt,_⟩ := bank_run bits word pos first.final.tapes hsrc
  rw [←hheads] at hlast
  obtain ⟨out,hout,_,_,hresult⟩ := initial_accept prefixProgram bankProgram 30
    (RecoveryColdView.coldBudget bits word) (bankBudget bits word) _ first last hfirst hfh htrue hlast
  have hsame := Option.some.inj (hr.symm.trans hout)
  rw [hsame,hresult,hlt,low_retained bits word first.final.tapes 0 (by decide)]
  exact hkeep

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
