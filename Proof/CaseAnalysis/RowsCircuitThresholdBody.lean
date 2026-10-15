import Proof.CaseAnalysis.RowsCircuitSymmetricBody
import Proof.CaseAnalysis.RowsCircuitBodyFields

/-! The same accepted threshold top and retained bitmap feed the complete
body, preserving original serialized descriptions and selected-bottom order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation SupplierPipeline CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuit CloseoutRowsCircuitBottom CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitPublishedFields CloseoutRowsCircuitPostTop CloseoutRowsCircuitTopSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_ready (C core W L : ℕ) (bits out : List Bool) (words : List (List Bool))
    (pb : Fin 639 → List Bool) (tb : Fin 1049 → List Bool) (g : SupportedNormalizedGate words.length)
    (hg : decodeSupportedNormalizedGate words.length (value (CloseoutRowsCircuitHeader.codeWord bits 3))=some g)
    (hinput : 2*bits.length+1 ≤ C) (prefixBound : ∀ i,(pb i).length ≤ C)
    (pstream : pb 297=words.flatMap frame) (ptemplate : pb 624=UnaryTemplate.tape words.length)
    (pn : pb 622=List.replicate words.length true) (praw : pb 1=frame bits)
    (meaning : CloseoutRowsGateMeasured.Output true words.length (CloseoutRowsCircuitHeader.codeWord bits 3) tb)
    (bitmap : CloseoutRowsGateBank.padded C tb 994=ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support)))
    (topBound : ∀ i : Fin 1049,i.val≠1035 → (CloseoutRowsGateBank.padded C tb i).length ≤ C)
    (hinitial : CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g ≤ C)
    (hin : ∀ b∈words,2*b.length+1 ≤ C)
    (hcap : ∀ b∈words,2*CloseoutRowsGateMeasured.budget b+4 ≤ C)
    (hcount : 1+2*words.length ≤ C)
    (hc : 32*(descriptions core words (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g) words.length+
      words.length+wires true core 1 (ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support)))
        words 0 words.length+3) ≤ C)
    (hheader : EquationHeaderAppend.budget g.wireCount+1 ≤ C) :
    CloseoutRowsCircuitBody.Fields true C core g.wireCount words
      (thresholdWord (CloseoutRowsGateSource.request true g).gate) out
      (ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support))) bits
      (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g) L W
      (CloseoutRowsCircuitThresholdTop.output C (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb g) :=by
  let A:=CloseoutRowsCircuitColdEntry.output C core W L bits out pb
  let B:=CloseoutRowsCircuitThresholdTop.output C A tb g
  have pubFields:=CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb
  have kept:=threshold_kept C A tb g
  have published:=threshold_publication C (CloseoutRowsCircuitHeader.codeWord bits 3) A tb g hg meaning bitmap
  have count:tb 1035=UnaryTemplate.tape words.length:=meaning.1
  have allTop:∀ i,(CloseoutRowsGateBank.padded C tb i).length ≤ C:=by
    intro i
    by_cases hi:i.val=1035
    · have he:i=1035:=Fin.ext hi;subst i
      change (ZeroPadding.pad 0 (tb 1035)).length ≤ C
      rw [ZeroPadding.pad_zero,count,←ptemplate]
      exact prefixBound 624
    · exact topBound i hi
  have topNative:tb 1033=frame (thresholdWord (CloseoutRowsGateSource.request true g).gate):=
    (meaning.2.2 g hg).1
  have retained:tb 1047=List.replicate g.wireCount true:=(meaning.2.2 g hg).2.2.2
  have topFits:(frame (thresholdWord (CloseoutRowsGateSource.request true g).gate)).length ≤ C:=by
    have h:=allTop 1033
    change (ZeroPadding.pad C (tb 1033)).length ≤ C at h
    rw [topNative,ZeroPadding.pad_length] at h
    exact (Nat.le_max_right _ _).trans h
  have countFits:g.wireCount ≤ C:=by
    have h:=allTop 1047
    change (ZeroPadding.pad C (tb 1047)).length ≤ C at h
    rw [retained,ZeroPadding.pad_length,List.length_replicate] at h
    exact (Nat.le_max_right _ _).trans h
  have gateBound:∀ j,(B (CloseoutRowsCircuitAllocate.gate j)).length ≤ C:=by
    intro j
    exact threshold_support C A tb g (fun i=>639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) C
      (cold_gate C core W L bits out pb hinput) allTop hinitial le_rfl
      (by intro h;omega) _ (CloseoutRowsCircuitAllocate.gate_range j)
  have support:∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (B i).length ≤ C+1:=by
    intro i hr hd hc' hw hl ho
    exact threshold_support C A tb g
      (fun i=>i≠1 ∧ i≠1674 ∧ i≠1694 ∧ i≠1698 ∧ i≠1699 ∧ i≠1688) (C+1)
      (by
        intro j ⟨h1,h2,h3,h4,h5,h6⟩
        exact CloseoutRowsCircuitColdEntry.cold_support C core W L bits out pb hinput prefixBound
          j h1 h2 h3 h4 h5 h6)
      allTop hinitial (by omega) (fun _=>le_rfl) i ⟨hr,hd,hc',hw,hl,ho⟩
  have fields:∀ i : Fin 7,B (![1689,1690,297,1692,1693,1697,1674] i)=
      (![List.replicate (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g) true,
        [],words.flatMap frame,ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support)),
        [true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i:=by
    intro i;fin_cases i
    · exact published 3
    · exact (kept 5).trans (pubFields 2)
    · exact (kept 1).trans ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 297).trans pstream)
    · exact published 1
    · exact (kept 6).trans (pubFields 3)
    · exact (kept 7).trans (pubFields 4)
    · exact (kept 3).trans (pubFields 0)
  have bW:B 1698=List.replicate W true:=(kept 8).trans (pubFields 5)
  have bL:B 1699=List.replicate L true:=(kept 9).trans (pubFields 6)
  have bRaw:B 1=frame bits:=(kept 0).trans
    ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 1).trans praw)
  have hinit:1 ≤ CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g:=by
    have hd:=CloseoutRowsGateWeightLength.gate_description g
    change CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g=_ at hd
    omega
  exact ⟨hin,hcap,fun _=>hinit,hc,⟨by rw [←pstream];exact prefixBound 297,hcount⟩,countFits,hheader,
    by simpa only [frame_length] using topFits,gateBound,published 4,published 5,published 2,published 0,
    (kept 4).trans (pubFields 1),published 6,threshold_count C A tb g meaning.1,fields,
    (kept 11).trans ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 622).trans pn),
    bL,bW,(kept 10).trans (pubFields 7),by rw [←bitmap];exact (allTop 994).trans (Nat.le_succ C),support,bRaw⟩

theorem body_run (C core W L : ℕ) (bits out : List Bool) (words : List (List Bool))
    (pb : Fin 639 → List Bool) (tb : Fin 1049 → List Bool) (g : SupportedNormalizedGate words.length)
    (hg : decodeSupportedNormalizedGate words.length (value (CloseoutRowsCircuitHeader.codeWord bits 3))=some g)
    (hinput : 2*bits.length+1 ≤ C) (prefixBound : ∀ i,(pb i).length ≤ C)
    (pstream : pb 297=words.flatMap frame) (ptemplate : pb 624=UnaryTemplate.tape words.length)
    (pn : pb 622=List.replicate words.length true) (praw : pb 1=frame bits)
    (meaning : CloseoutRowsGateMeasured.Output true words.length (CloseoutRowsCircuitHeader.codeWord bits 3) tb)
    (bitmap : CloseoutRowsGateBank.padded C tb 994=ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support)))
    (topBound : ∀ i : Fin 1049,i.val≠1035 → (CloseoutRowsGateBank.padded C tb i).length ≤ C)
    (hinitial : CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g ≤ C)
    (hin : ∀ b∈words,2*b.length+1 ≤ C)
    (hcap : ∀ b∈words,2*CloseoutRowsGateMeasured.budget b+4 ≤ C)
    (hcount : 1+2*words.length ≤ C)
    (hc : 32*(descriptions core words (CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g) words.length+
      words.length+wires true core 1 (ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support)))
        words 0 words.length+3) ≤ C)
    (hheader : EquationHeaderAppend.budget g.wireCount+1 ≤ C) :
    let A:=CloseoutRowsCircuitThresholdTop.output C
      (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb g
    let top:=thresholdWord (CloseoutRowsGateSource.request true g).gate
    let initial:=CloseoutRowsCircuitThresholdTop.weights g+CloseoutRowsCircuitThresholdTop.theta g
    let members:=ZeroPadding.pad C (frame (CloseoutRowsGateSupport.gateMembers g.support))
    let native:=(out++natWord g.wireCount++frame top)++
      (List.range words.length).flatMap (outputs true core 1 members words)
    ∃ r,runFrom (CloseoutRowsCircuitBody.machine true)
      (CloseoutRowsCircuitBody.budget true C g.wireCount top (descriptions core words initial words.length)
        words.length (wires true core 1 members words 0 words.length) L W)
      ⟨(CloseoutRowsCircuitBody.machine true).start,
        Function.update (CloseoutRowsCircuitColdThreshold.heads out) 1689 initial,A⟩=some r ∧
      r.steps ≤ CloseoutRowsCircuitBody.budget true C g.wireCount top (descriptions core words initial words.length)
        words.length (wires true core 1 members words 0 words.length) L W ∧
      r.final.heads=CloseoutRowsCircuitColdEntry.heads native ∧
      (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
        CloseoutRowsCircuitArithmeticDock.amount true (descriptions core words initial words.length) words.length ≤ L ∧
        wires true core 1 members words 0 words.length ≤ W) ∧
      r.final.tapes 1688=native ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate C true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=frame bits ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes i).length ≤ C+1:=by
  have F:=fields_ready C core W L bits out words pb tb g hg hinput prefixBound pstream ptemplate pn praw
    meaning bitmap topBound hinitial hin hcap hcount hc hheader
  obtain ⟨r,hr,rs,rh,verdict,native,domain,driver,capW,capL,raw,small⟩:=
    CloseoutRowsCircuitBody.body_support true C core g.wireCount words _ out _ _ L W _
      F.input F.capacity F.positive F.resource F.source F.retainedFits F.header F.topFits F.gate
      F.driver F.log F.retained F.topWord F.stream F.scratch F.count F.ports F.rawCount F.capL F.capW F.flag
      F.membersFits F.privateSupport
  rw [←threshold_heads] at hr
  exact ⟨r,hr,rs,rh,verdict,native,domain,driver,capW.trans F.capW,capL.trans F.capL,raw.trans F.raw,small⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdBody
