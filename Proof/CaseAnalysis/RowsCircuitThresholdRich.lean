import Proof.CaseAnalysis.RowsCircuitPostTop

/-! Carry the original threshold bitmap through the same complete cold
receipt; the bottom supplier uses this retained mask without another scan. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
open CloseoutRowsCircuit CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem joined_rich {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H H' : Fin t → ℕ) (A B : Fin t → List Bool)
    (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,H,A⟩=some first)
    (ph : first.final.heads=H') (pt : first.final.tapes=B) (ps : first.steps ≤ fp)
    (hq : runFrom q fq ⟨q.start,H',B⟩=some last) (qs : last.steps ≤ fq) :
    ∃ r,runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,H,A⟩=some r ∧
      r.steps ≤ fp+1+fq ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=by
  have he:Composition.restart first.final q.start=⟨q.start,H',B⟩:=configuration_ext rfl ph pt
  have hlast:runFrom q fq (Composition.restart first.final q.start)=some last:=by rw [he];exact hq
  refine ⟨Composition.joinedReceipt first last,Composition.run_join p q fp fq _ first last hp hlast,?_,rfl,rfl⟩
  change first.steps+1+last.steps ≤ fp+1+fq
  omega

theorem cold_run_rich (cap core W L : ℕ) (bits out : List Bool)
    (hin : 2*bits.length+1 ≤ cap)
    (hcap : 2*CloseoutRowsGateMeasured.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+4 ≤ cap)
    (hprefix : CloseoutRowsCircuitPrefix.budget bits+1 ≤ cap) :
    ∃ prefixBank gateBank r,
      runFrom machine (budget cap bits)
        ⟨machine.start,CloseoutRowsCircuitColdEntry.heads out,
          CloseoutRowsCircuitColdEntry.input cap core W L bits out⟩=some r ∧
      r.steps ≤ budget cap bits ∧
      (readTapeBit (prefixBank 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid true bits) ∧
      prefixBank 297=PCPPNativeCanonicalWalk.atomStream (CloseoutRowsCircuitHeader.codeWord bits 2).length
        (PCPPNativeCanonicalTree.tree (value (CloseoutRowsCircuitHeader.codeWord bits 2))).atoms ∧
      prefixBank 622=List.replicate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) true ∧
      prefixBank 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      prefixBank 1=frame bits ∧ (∀ i,(prefixBank i).length ≤ cap) ∧
      CloseoutRowsGateMeasured.Output true (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3) gateBank ∧
      (∀ i : Fin 1049,i.val≠1035 → (CloseoutRowsGateBank.padded cap gateBank i).length ≤ cap) ∧
      (∀ g,decodeSupportedNormalizedGate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (value (CloseoutRowsCircuitHeader.codeWord bits 3))=some g →
        CloseoutRowsGateBank.padded cap gateBank 994=ZeroPadding.pad cap
          (frame (CloseoutRowsGateSupport.gateMembers g.support))) ∧
      (∀ g,decodeSupportedNormalizedGate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (value (CloseoutRowsCircuitHeader.codeWord bits 3))=some g →
        r.final.tapes=CloseoutRowsCircuitThresholdTop.output cap
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) gateBank g ∧
        r.final.heads=Function.update (heads out) 1689
          (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g)) ∧
      (¬(decodeSupportedNormalizedGate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (value (CloseoutRowsCircuitHeader.codeWord bits 3))).isSome →
        r.final.tapes=CloseoutRowsCircuitThresholdTop.middle cap
          (CloseoutRowsCircuitColdEntry.output cap core W L bits out prefixBank) gateBank ∧
        r.final.heads=heads out):=by
  obtain ⟨bank,prefixRun,topWord,stream,count,template,flag,raw⟩:=CloseoutRowsCircuitPrefix.prefix_run_fields true bits
  have bound:=CloseoutRowsCircuitColdEntry.prefix_support true cap bits bank hin prefixRun hprefix
  obtain ⟨p,hp,pt,ph,ps⟩:=CloseoutRowsCircuitColdEntry.from_prefix true cap core W L bits out bank hin prefixRun topWord
  let A:=CloseoutRowsCircuitColdEntry.output cap core W L bits out bank
  obtain ⟨m,hm,mh,mt,ms⟩:=CompetitorCountTable.move_run (624 : Fin 1703)
    (CloseoutRowsCircuitColdEntry.heads out) A
  have mh':m.final.heads=heads out:=by
    rw [mh];funext i
    by_cases hi:i=624
    · subst i;rfl
    · simp only [if_neg hi,heads,Function.update_of_ne hi]
  obtain ⟨start,hstart,ss,sh,st⟩:=joined_rich (CloseoutRowsCircuitColdEntry.machine true)
    (CompetitorCountTable.moveMachine (624 : Fin 1703)) _ _ _ _ _ _ p m hp ph pt ps hm ms.le
  have sh':start.final.heads=heads out:=sh.trans mh'
  have st':start.final.tapes=A:=st.trans mt
  have width:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
    (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
  obtain ⟨gates,top,toprun,tops,meaning,bounds,bitmap,accepted,rejected⟩:=CloseoutRowsCircuitThresholdTop.top_run_fields
    cap (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
    (CloseoutRowsCircuitHeader.codeWord bits 3) (heads out) A (gate_heads out)
    (CloseoutRowsCircuitColdEntry.output_gate cap core W L bits out bank _ template)
    (external_heads out) (CloseoutRowsCircuitColdEntry.output_external cap core W L bits out bank)
    (by rw [width];exact hin) hcap
  obtain ⟨actual,hr,rs,rh,rt⟩:=joined_rich positioned CloseoutRowsCircuitThresholdTop.machine
    _ _ _ _ _ _ start top hstart sh' st' ss toprun tops
  have budgetEq:(CloseoutRowsCircuitColdEntry.budget cap bits+1+1)+1+
      CloseoutRowsCircuitThresholdTop.budget cap (CloseoutRowsCircuitHeader.codeWord bits 3)=budget cap bits:=by
    unfold budget;omega
  rw [budgetEq] at hr rs
  refine ⟨bank,gates,actual,hr,rs,flag,stream,count,template,raw,bound,meaning,bounds,bitmap,?_,?_⟩
  · intro g hg;obtain ⟨gt,gh⟩:=accepted g hg
    exact ⟨rt.trans gt,rh.trans gh⟩
  · intro hn;obtain ⟨gt,gh⟩:=rejected hn
    exact ⟨rt.trans gt,rh.trans gh⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdThreshold
