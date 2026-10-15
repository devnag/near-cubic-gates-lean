import Proof.Amplification.RecoveryViewEntryCarrier

/-! The actual two-input cold prefix in the fixed raw-view bank. Successful
valuation parsing supplies every copy source and the retained stream cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prefixProgram := TapeEmbedding.machine 68 RecoveryColdValuation.resumedMachine
def input (bits word : List Bool) := lift (RecoveryColdValuation.input bits word)

theorem prefix_run (bits word : List Bool) :
    ∃ r,run prefixProgram (RecoveryColdValuation.resumedBudget bits word) (input bits word)=some r ∧
      r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (limit bits) (readEntry (width bits)) word).isSome] ∧
      ∀ table tail,readList (limit bits) (readEntry (width bits)) word=some (table,tail) →
        ∃ count,count≤limit bits ∧ tail=word.drop (count*(width bits+2)+1) ∧
          r.final.heads=bankHeads (2*(count*(width bits+2)+1)) ∧
          Sources bits r.final.tapes ∧ r.final.tapes 23=frame word ∧
          r.final.tapes 31=CompareMachine.word count := by
  obtain ⟨c,s,base,hbase,hh,ht,hgood⟩ := RecoveryColdValuation.resumed_success bits word
  let r := TapeEmbedding.receipt (fun _ : Fin 68=>0) (fun _=>[]) base
  have hr := embed_run RecoveryColdValuation.resumedMachine
    (RecoveryColdValuation.resumedBudget bits word) _ base hbase
  refine ⟨r,hr,hh,ht,?_⟩
  intro table tail hparse
  obtain ⟨count,hc,htail,hheads,hsource,hcount,_,hcap,hzero,hout⟩ := hgood table tail hparse
  refine ⟨count,hc,htail,?_,?_,hsource,hcount⟩
  · change Fin.addCases (m:=32) (n:=68) (motive:=fun _=>Nat) base.final.heads (fun _=>0)=_
    rw [hheads]
    funext i
    fin_cases i <;> rfl
  · exact sources_of_return bits word c s base.final.tapes hzero hcap hout

theorem bank_bound (bits : List Bool) : bankBudget bits≤1048576*(bits.length+1)^2 := by
  have hb : max 1 bits.length+3≤4*(bits.length+1) := by omega
  have hs := Nat.pow_le_pow_left hb 2
  change 16*(max 1 bits.length+2)+2*(3*(max 1 bits.length+1))+
    4*(8192*(max 1 bits.length+2+1)^2)+54≤1048576*(bits.length+1)^2
  nlinarith only [hs,hb]

end NearCubicWires.RepairOrdinary.RecoveryColdView
