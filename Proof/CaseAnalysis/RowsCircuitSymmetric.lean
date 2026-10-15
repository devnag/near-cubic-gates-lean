import Proof.CaseAnalysis.RowsCircuitPorts

/-! Cold original circuit input reaches the complete symmetric top check.
The actual bottom-count template and table field come from that SAME
canonical prefix; the native append cursor is preserved throughout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsGateColdPair.machine (CloseoutRowsCircuitColdEntry.machine false)
  CloseoutRowsCircuitSymmetricTop.machine (fun _=>true)
def budget (cap : ℕ) (bits : List Bool):=CloseoutRowsCircuitColdEntry.budget cap bits+2+
  CloseoutRowsCircuitSymmetricTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)

theorem parser_heads (out : List Bool) (i : Fin 181) :
    CloseoutRowsCircuitColdEntry.heads out (CloseoutRowsCircuitSymmetricTop.slots i)=0:=by
  have hv:=CloseoutRowsCircuitSymmetricTop.slots_val i
  have hnative:CloseoutRowsCircuitSymmetricTop.slots i≠1688:=by
    intro h;have h':=congrArg (fun k : Fin 1703=>k.val) h
    rw [hv] at h';split_ifs at h' <;> omega
  have hcore:(CloseoutRowsCircuitSymmetricTop.slots i).val≠1674:=by
    rw [hv];split_ifs <;> omega
  simp only [CloseoutRowsCircuitColdEntry.heads,if_neg hnative,
    CloseoutRowsCircuit.heads,if_neg hcore]

theorem parser_input (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (count : ℕ) (ht : bank 624=UnaryTemplate.tape count) (i : Fin 181) :
    CloseoutRowsCircuitColdEntry.output cap core W L bits out bank (CloseoutRowsCircuitSymmetricTop.slots i)=
      CloseoutRowsCircuitSymmetricTop.padded cap
        (CloseoutRowsCircuitSymTop.input count (CloseoutRowsCircuitHeader.codeWord bits 3)) i:=by
  rw [CloseoutRowsCircuitSymmetricTop.padded,CloseoutRowsCircuitSymmetricTop.input_eq]
  by_cases hd:i.val=178
  · simp only [CloseoutRowsCircuitSymmetricTop.pads,if_pos hd,ZeroPadding.pad_zero]
    have he:CloseoutRowsCircuitSymmetricTop.slots i=CloseoutRowsCircuit.prefixSlots 624:=by
      apply Fin.ext;rw [CloseoutRowsCircuitSymmetricTop.slots_val]
      simp [hd,CloseoutRowsCircuit.prefixSlots]
    rw [he,CloseoutRowsCircuitColdEntry.output_prefix];exact ht
  · simp only [CloseoutRowsCircuitSymmetricTop.pads,if_neg hd]
    by_cases hz:i.val=0
    · rw [if_pos hz]
      have he:CloseoutRowsCircuitSymmetricTop.slots i=640:=by
        apply Fin.ext;rw [CloseoutRowsCircuitSymmetricTop.slots_val,if_pos hz];rfl
      rw [he];exact CloseoutRowsCircuitColdEntry.output_top cap core W L bits out bank
    · rw [if_neg hz]
      rw [CloseoutRowsCircuitColdEntry.output_blank _ _ _ _ _ _ _ _ (by
        have hv:=CloseoutRowsCircuitSymmetricTop.slots_val i
        have range:639 ≤ (CloseoutRowsCircuitSymmetricTop.slots i).val ∧
            (CloseoutRowsCircuitSymmetricTop.slots i).val ≤ 1687 ∧
            (CloseoutRowsCircuitSymmetricTop.slots i).val≠1674 ∧
            (CloseoutRowsCircuitSymmetricTop.slots i).val≠640:=by
          rw [hv];split_ifs <;> omega
        refine ⟨range.1,range.2.1,range.2.2.1,?_⟩
        intro h;exact range.2.2.2 (congrArg (fun k : Fin 1703=>k.val) h))]
      simp [ZeroPadding.pad]

theorem external_heads (out : List Bool) (i : Fin 11) :
    CloseoutRowsCircuitColdEntry.heads out (CloseoutRowsCircuitSymmetricTop.external i)=0:=by
  fin_cases i <;> rfl

theorem external_input (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (count : ℕ) (hc : bank 622=List.replicate count true) :
    ∀ i,CloseoutRowsCircuitColdEntry.output cap core W L bits out bank (CloseoutRowsCircuitSymmetricTop.external i)=
      CloseoutRowsCircuitSymmetricTop.externalData cap count i:=by
  have E:=CloseoutRowsCircuitColdEntry.output_external cap core W L bits out bank
  intro i;fin_cases i
  · rw [CloseoutRowsCircuitColdEntry.output,Function.update_of_ne (by decide),
      CloseoutRowsCircuitColdEntry.framed_other _ _ _ _ _ _ _ _ (by decide),
      CloseoutRowsCircuitColdEntry.seeded_other _ _ _ _ _ _ _ (by decide)]
    have h:=CloseoutRowsCircuitColdEntry.allocated_scratch cap core W L bits out ((0 : Fin 6).natAdd 1048)
    rw [CloseoutRowsCircuitAllocate.scratch_new] at h;exact h
  · exact CloseoutRowsCircuitColdEntry.output_blank _ _ _ _ _ _ _ 1680 (by decide)
  · exact CloseoutRowsCircuitColdEntry.output_blank _ _ _ _ _ _ _ 1684 (by decide)
  · exact (CloseoutRowsCircuitColdEntry.output_prefix _ _ _ _ _ _ _ 622).trans hc
  · exact E 0
  · exact E 1
  · exact E 2
  · exact E 3
  · exact E 4
  · exact E 5
  · exact E 6

theorem cold_run (cap core W L : ℕ) (bits out : List Bool)
    (hin : 2*bits.length+1 ≤ cap)
    (hcap : CloseoutRowsCircuitSymTop.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+1 ≤ cap)
    (hm : CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2) ≤ cap) (hc : 2 ≤ cap) :
    ∃ prefixBank topBank result,
      ReadyAt machine (budget cap bits) (CloseoutRowsCircuitColdEntry.heads out)
        (CloseoutRowsCircuitColdEntry.input cap core W L bits out) result ∧
      (readTapeBit (prefixBank 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid false bits) ∧
      prefixBank 297=PCPPNativeCanonicalWalk.atomStream (CloseoutRowsCircuitHeader.codeWord bits 2).length
        (PCPPNativeCanonicalTree.tree (RadixSemantics.value (CloseoutRowsCircuitHeader.codeWord bits 2))).atoms ∧
      prefixBank 622=List.replicate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) true ∧
      prefixBank 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      (∀ i : Fin 181,i.val≠178 → (CloseoutRowsCircuitSymmetricTop.padded cap topBank i).length ≤ cap) ∧
      (CloseoutRowsCircuitSymTop.valid (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) →
        result=CloseoutRowsCircuitSymmetricTop.output cap
          (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
          (CloseoutRowsCircuitHeader.codeWord bits 3)
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) topBank) ∧
      (¬CloseoutRowsCircuitSymTop.valid (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) →
        result=CloseoutRowsCircuitSymmetricTop.middle cap
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) topBank):=by
  obtain ⟨bank,prep,_top,stream,count,template,flag⟩:=CloseoutRowsCircuitColdEntry.cold_run false cap core W L bits out hin
  have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
    (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
  obtain ⟨top,result,run,_table,_count,bounds,accepted,rejected⟩:=CloseoutRowsCircuitSymmetricTop.top_run cap
    (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
    (CloseoutRowsCircuitHeader.codeWord bits 3) (CloseoutRowsCircuitColdEntry.heads out)
    (CloseoutRowsCircuitColdEntry.output cap core W L bits out bank) (parser_heads out)
    (parser_input cap core W L bits out bank _ template) (external_heads out)
    (external_input cap core W L bits out bank _ count) (by rw [width];exact hin) hcap hm hc
  have all:=CloseoutRowsGatePairHeads.joined (CloseoutRowsCircuitColdEntry.machine false)
    CloseoutRowsCircuitSymmetricTop.machine (fun _=>true) _ _ _ _ _ _ prep run rfl
  have hb:CloseoutRowsCircuitColdEntry.budget cap bits+1+
      CloseoutRowsCircuitSymmetricTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)+1=budget cap bits:=by
    unfold budget;omega
  rw [hb] at all
  exact ⟨bank,top,result,all,flag,stream,count,template,bounds,accepted,rejected⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdSymmetric
