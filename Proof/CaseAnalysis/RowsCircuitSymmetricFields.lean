import Proof.CaseAnalysis.RowsCircuitSymmetricTopFields

/-! The original cold symmetric run retains its two exact decisions and
the actual prefix support bound needed by the successful outer reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_run_fields (C core W L : ℕ) (bits out : List Bool)
    (hin : 2*bits.length+1 ≤ C)
    (hcap : CloseoutRowsCircuitSymTop.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+1 ≤ C)
    (hm : CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2) ≤ C)
    (hc : 2 ≤ C) (hprefix : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C) :
    ∃ prefixBank topBank result,
      ReadyAt machine (budget C bits) (CloseoutRowsCircuitColdEntry.heads out)
        (CloseoutRowsCircuitColdEntry.input C core W L bits out) result ∧
      (readTapeBit (prefixBank 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid false bits) ∧
      prefixBank 297=PCPPNativeCanonicalWalk.atomStream (CloseoutRowsCircuitHeader.codeWord bits 2).length
        (PCPPNativeCanonicalTree.tree (RadixSemantics.value (CloseoutRowsCircuitHeader.codeWord bits 2))).atoms ∧
      prefixBank 622=List.replicate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) true ∧
      prefixBank 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      prefixBank 1=frame bits ∧ (∀ i,(prefixBank i).length ≤ C) ∧
      topBank 174=frame (CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)) ∧
      topBank 178=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      (∀ i : Fin 181,i.val≠178 → (CloseoutRowsCircuitSymmetricTop.padded C topBank i).length ≤ C) ∧
      (readTapeBit (topBank 179) 0=true ↔ CloseoutRowsCircuitSymTop.valid
        (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) (CloseoutRowsCircuitHeader.codeWord bits 3)) ∧
      (CloseoutRowsCircuitSymTop.valid (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) → result=CloseoutRowsCircuitSymmetricTop.output C
          (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) (CloseoutRowsCircuitHeader.codeWord bits 3)
          (CloseoutRowsCircuitColdEntry.output C core W L bits out prefixBank) topBank) ∧
      (¬CloseoutRowsCircuitSymTop.valid (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) → result=CloseoutRowsCircuitSymmetricTop.middle C
          (CloseoutRowsCircuitColdEntry.output C core W L bits out prefixBank) topBank):=by
  obtain ⟨bank,prefixRun,topWord,stream,count,template,flag,raw⟩:=CloseoutRowsCircuitPrefix.prefix_run_fields false bits
  have bound:=CloseoutRowsCircuitColdEntry.prefix_support false C bits bank hin prefixRun hprefix
  have prep:=CloseoutRowsCircuitColdEntry.from_prefix false C core W L bits out bank hin prefixRun topWord
  have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
    (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
  obtain ⟨top,result,run,table,topCount,bounds,topFlag,accepted,rejected⟩:=CloseoutRowsCircuitSymmetricTop.top_run_fields C
    (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
    (CloseoutRowsCircuitHeader.codeWord bits 3) (CloseoutRowsCircuitColdEntry.heads out)
    (CloseoutRowsCircuitColdEntry.output C core W L bits out bank) (parser_heads out)
    (parser_input C core W L bits out bank _ template) (external_heads out)
    (external_input C core W L bits out bank _ count) (by rw [width];exact hin) hcap hm hc
  have all:=CloseoutRowsGatePairHeads.joined (CloseoutRowsCircuitColdEntry.machine false)
    CloseoutRowsCircuitSymmetricTop.machine (fun _=>true) _ _ _ _ _ _ prep run rfl
  have hb:CloseoutRowsCircuitColdEntry.budget C bits+1+
      CloseoutRowsCircuitSymmetricTop.budget C (CloseoutRowsCircuitHeader.codeWord bits 3)+1=budget C bits:=by
    unfold budget;omega
  rw [hb] at all
  exact ⟨bank,top,result,all,flag,stream,count,template,raw,bound,table,topCount,bounds,topFlag,accepted,rejected⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric
