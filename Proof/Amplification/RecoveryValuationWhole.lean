import Proof.Amplification.RecoveryValuationExecution

/-! Whole first certificate-parse phase from the actual two-input verifier
ABI and blank workspace, including dimensions, all retained buffers, the
literal cap, setup and parser. Malformed valuation prefixes report false. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits word : List Bool) (i : Fin 32) : List Bool :=
  if i.val=0 then frame bits else if i.val=1 then frame word else []
noncomputable def prefixMachine := TapeEmbedding.machine 6 RecoveryColdPreliminary.machine
noncomputable def coldMachine := Composition.machine prefixMachine entryMachine
def coldBudget (bits word : List Bool) := RecoveryColdPreliminary.budget bits word+1+
  (RecoveryValuationCount.limit (width bits) (cap bits)+2)

theorem prefix_run (bits word : List Bool) :
    ∃ c s,c ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ s ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run prefixMachine (RecoveryColdPreliminary.budget bits word) (input bits word)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=before bits word c s := by
  obtain ⟨c,s,hc,hs,b,hb,hbh,hbt,_⟩ := RecoveryColdPreliminary.preliminary_run bits word
  obtain ⟨r,hr,_,hf⟩ := RecoveryBankPair.left_run RecoveryColdPreliminary.machine
    (RecoveryColdPreliminary.budget bits word)
    (initialConfiguration RecoveryColdPreliminary.machine (RecoveryColdPreliminary.input bits word)) b hb
    (fun _ : Fin 6=>0) (fun _=>[])
  have hi : RecoveryBankPair.cfg
      (initialConfiguration RecoveryColdPreliminary.machine (RecoveryColdPreliminary.input bits word)).heads
      (initialConfiguration RecoveryColdPreliminary.machine (RecoveryColdPreliminary.input bits word)).tapes
      (fun _ : Fin 6=>0) (fun _=>[])
      (initialConfiguration RecoveryColdPreliminary.machine (RecoveryColdPreliminary.input bits word)).control=
      initialConfiguration prefixMachine (input bits word) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨c,s,hc,hs,r,hr,?_,?_⟩
  · rw [hf,hbh]
    funext i
    fin_cases i <;> rfl
  · rw [hf,hbt]
    rfl

theorem cold_run (bits word : List Bool) :
    ∃ r,run coldMachine (coldBudget bits word) (input bits word)=some r ∧
      r.steps≤coldBudget bits word ∧ r.final.heads 30=0 ∧
      r.final.tapes 30=[(readList (cap bits) (readEntry (width bits)) word).isSome] := by
  obtain ⟨c,s,_,_,first,hfirst,hfh,hft⟩ := prefix_run bits word
  obtain ⟨last,hlast,hlh,hlt⟩ := entry_run bits word c s
  have hi : Composition.restart first.final entryMachine.start=
      initialConfiguration entryMachine (before bits word c s) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h := Composition.run_join prefixMachine entryMachine (RecoveryColdPreliminary.budget bits word)
    (RecoveryValuationCount.limit (width bits) (cap bits)+2) _ first last hfirst hlast
  let r := Composition.joinedReceipt first last
  have hr : run coldMachine (coldBudget bits word) (input bits word)=some r := h
  exact ⟨r,hr,runFrom_steps_le coldMachine (coldBudget bits word) _ r hr,hlh,hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
