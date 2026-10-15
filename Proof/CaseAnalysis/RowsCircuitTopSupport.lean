import Proof.CaseAnalysis.RowsCircuitPublishedFields
import Proof.CaseAnalysis.RowsCircuitSupport

/-! The actual top banks and publication keep reusable gate scratch in C
cells and all outer private tapes in C+1 cells, including the paid log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopSupport
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit SupplierPipeline
open CloseoutRowsCircuitColdEntry
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_support_at {t u : ℕ} (slots : Fin t → Fin u) (inj : Function.Injective slots)
    (P : Fin u → Prop) (C : ℕ) (A : Fin u → List Bool) (B : Fin t → List Bool)
    (ha : ∀ i,P i → (A i).length ≤ C) (hb : ∀ j,P (slots j) → (B j).length ≤ C) :
    ∀ i,P i → (install slots A B i).length ≤ C:=by
  intro i hi
  by_cases hit:∃ j,slots j=i
  · obtain ⟨j,rfl⟩:=hit
    rw [install_slot slots inj];exact hb j hi
  · rw [install_other _ _ _ _ (by simpa only [not_exists] using hit)]
    exact ha i hi

theorem publication_support (C a b : ℕ) (sources : Fin 3 → List Bool)
    (hs : ∀ j,(sources j).length ≤ C) (hab : a+b ≤ C) (i : Fin 12) :
    (CloseoutRowsCircuitTopPublish.output C a b sources i).length ≤ C+(if i=6 then 1 else 0):=by
  have s0:=hs 0
  have s1:=hs 1
  have s2:=hs 2
  fin_cases i <;> simp [CloseoutRowsCircuitTopPublish.output,CloseoutRowsCircuitTopPublish.bank,
    ZeroPadding.pad_length] <;> omega

theorem cold_gate (C core W L : ℕ) (bits out : List Bool) (bank : Fin 639 → List Bool)
    (hin : 2*bits.length+1 ≤ C) (i : Fin 1703)
    (hi : 639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) :
    (CloseoutRowsCircuitColdEntry.output C core W L bits out bank i).length ≤ C:=by
  by_cases ht:i=640
  · subst i
    rw [CloseoutRowsCircuitColdEntry.output_top,ZeroPadding.pad_length,frame_length]
    have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
      (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
    rw [width];omega
  · rw [CloseoutRowsCircuitColdEntry.output_blank _ _ _ _ _ _ _ i ⟨hi.1,hi.2.1,hi.2.2,ht⟩]
    simp

theorem symmetric_sources (C n : ℕ) (bits : List Bool) (hn : n ≤ C)
    (ht : (frame (CloseoutWitness.BitFields.payload bits)).length ≤ C) :
    ∀ j,(CloseoutRowsCircuitSymmetricTop.sources C n bits j).length ≤ C:=by
  intro j;fin_cases j
  · change (ZeroPadding.pad C (frame (CloseoutWitness.BitFields.payload bits))).length ≤ C
    rw [ZeroPadding.pad_length];omega
  · simp [CloseoutRowsCircuitSymmetricTop.sources]
  · simpa [CloseoutRowsCircuitSymmetricTop.sources] using hn

theorem symmetric_support (C n : ℕ) (bits : List Bool) (A : Fin 1703 → List Bool) (bank : Fin 181 → List Bool)
    (P : Fin 1703 → Prop) (bound : ℕ)
    (ha : ∀ i,P i → (A i).length ≤ bound)
    (hb : ∀ j,(CloseoutRowsCircuitSymmetricTop.padded C bank j).length ≤ C)
    (hn : n ≤ C) (ht : (frame (CloseoutWitness.BitFields.payload bits)).length ≤ C)
    (hc : C ≤ bound) (hlog : P 1695 → C+1 ≤ bound) :
    ∀ i,P i → (CloseoutRowsCircuitSymmetricTop.output C n bits A bank i).length ≤ bound:=by
  have mid:=install_support CloseoutRowsCircuitSymmetricTop.slots CloseoutRowsCircuitSymmetricTop.slots_injective
    P bound A (CloseoutRowsCircuitSymmetricTop.padded C bank) ha (fun j=>(hb j).trans hc)
  apply install_support_at CloseoutRowsCircuitSymmetricTop.publishSlots CloseoutRowsCircuitSymmetricTop.publish_injective
    P bound _ _ mid
  intro j hj
  have small:=publication_support C 0 0 (CloseoutRowsCircuitSymmetricTop.sources C n bits)
    (symmetric_sources C n bits hn ht) (by omega) j
  by_cases hl:j=6
  · subst j
    exact small.trans (hlog hj)
  · simp only [if_neg hl,Nat.add_zero] at small
    exact small.trans hc

theorem threshold_support {n : ℕ} (C : ℕ) (A : Fin 1703 → List Bool) (bank : Fin 1049 → List Bool)
    (g : SupportedNormalizedGate n) (P : Fin 1703 → Prop) (bound : ℕ)
    (ha : ∀ i,P i → (A i).length ≤ bound)
    (hb : ∀ j,(CloseoutRowsGateBank.padded C bank j).length ≤ C)
    (hd : CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g ≤ C)
    (hc : C ≤ bound) (hlog : P 1695 → C+1 ≤ bound) :
    ∀ i,P i → (CloseoutRowsCircuitThresholdTop.output C A bank g i).length ≤ bound:=by
  have mid:=install_support gateSlots gate_injective P bound A (CloseoutRowsGateBank.padded C bank)
    ha (fun j=>(hb j).trans hc)
  apply install_support_at topPublishSlots topPublish_injective P bound _ _ mid
  intro j hj
  have sources:∀ k,(CloseoutRowsCircuitThresholdTop.sources C bank k).length ≤ C:=by
    intro k;fin_cases k
    · exact hb 1033
    · exact hb 994
    · exact hb 1047
  have small:=publication_support C (CloseoutRowsCircuitThresholdTop.weights g) (CloseoutRowsCircuitThresholdTop.theta g)
    (CloseoutRowsCircuitThresholdTop.sources C bank) sources hd j
  by_cases hl:j=6
  · subst j
    exact small.trans (hlog hj)
  · simp only [if_neg hl,Nat.add_zero] at small
    exact small.trans hc

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTopSupport
