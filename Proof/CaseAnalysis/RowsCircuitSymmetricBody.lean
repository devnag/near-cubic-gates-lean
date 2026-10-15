import Proof.CaseAnalysis.RowsCircuitThresholdRich
import Proof.CaseAnalysis.RowsCircuitBodyFields

/-! The actual published symmetric top feeds the complete common body.
Every body field comes from the same prefix, top and paid publication. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuit CloseoutRowsCircuitBottom CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitPublishedFields CloseoutRowsCircuitPostTop CloseoutRowsCircuitTopSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fields_ready (C core W L : ℕ) (bits out : List Bool) (words : List (List Bool))
    (pb : Fin 639 → List Bool) (tb : Fin 181 → List Bool)
    (hinput : 2*bits.length+1 ≤ C) (prefixBound : ∀ i,(pb i).length ≤ C)
    (pstream : pb 297=words.flatMap frame) (ptemplate : pb 624=UnaryTemplate.tape words.length)
    (praw : pb 1=frame bits)
    (table : tb 174=frame (CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)))
    (count : tb 178=UnaryTemplate.tape words.length)
    (topBound : ∀ i : Fin 181,i.val≠178 → (CloseoutRowsCircuitSymmetricTop.padded C tb i).length ≤ C)
    (hin : ∀ b∈words,2*b.length+1 ≤ C)
    (hcap : ∀ b∈words,2*CloseoutRowsGateMeasured.budget b+4 ≤ C)
    (hcount : 1+2*words.length ≤ C)
    (hc : 32*(descriptions core words 0 words.length+words.length+
      wires false core 1 (List.replicate C false) words 0 words.length+3) ≤ C)
    (hheader : EquationHeaderAppend.budget words.length+1 ≤ C) :
    CloseoutRowsCircuitBody.Fields false C core words.length words
      (CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)) out
      (List.replicate C false) bits 0 L W
      (CloseoutRowsCircuitSymmetricTop.output C words.length (CloseoutRowsCircuitHeader.codeWord bits 3)
        (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb) :=by
  let A:=CloseoutRowsCircuitColdEntry.output C core W L bits out pb
  let B:=CloseoutRowsCircuitSymmetricTop.output C words.length (CloseoutRowsCircuitHeader.codeWord bits 3) A tb
  have pubFields:=CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb
  have kept:=symmetric_kept C words.length (CloseoutRowsCircuitHeader.codeWord bits 3) A tb
  have published:=symmetric_publication C words.length (CloseoutRowsCircuitHeader.codeWord bits 3) A tb
  have allTop:∀ i,(CloseoutRowsCircuitSymmetricTop.padded C tb i).length ≤ C:=by
    intro i
    by_cases hi:i.val=178
    · have he:i=178:=Fin.ext hi;subst i
      change (ZeroPadding.pad 0 (tb 178)).length ≤ C
      rw [ZeroPadding.pad_zero,count,←ptemplate]
      exact prefixBound 624
    · exact topBound i hi
  have topFits:(frame (CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3))).length ≤ C:=by
    have h:=allTop 174
    change (ZeroPadding.pad C (tb 174)).length ≤ C at h
    rw [table,ZeroPadding.pad_length] at h
    exact (Nat.le_max_right _ _).trans h
  have gateBound:∀ j,(B (CloseoutRowsCircuitAllocate.gate j)).length ≤ C:=by
    intro j
    exact symmetric_support C words.length (CloseoutRowsCircuitHeader.codeWord bits 3) A tb
      (fun i=>639 ≤ i.val ∧ i.val ≤ 1687 ∧ i.val≠1674) C
      (cold_gate C core W L bits out pb hinput) allTop (by omega) topFits le_rfl
      (by intro h;omega) _ (CloseoutRowsCircuitAllocate.gate_range j)
  have support:∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (B i).length ≤ C+1:=by
    intro i hr hd hc' hw hl ho
    exact symmetric_support C words.length (CloseoutRowsCircuitHeader.codeWord bits 3) A tb
      (fun i=>i≠1 ∧ i≠1674 ∧ i≠1694 ∧ i≠1698 ∧ i≠1699 ∧ i≠1688) (C+1)
      (by
        intro j ⟨h1,h2,h3,h4,h5,h6⟩
        exact CloseoutRowsCircuitColdEntry.cold_support C core W L bits out pb hinput prefixBound
          j h1 h2 h3 h4 h5 h6)
      allTop (by omega) topFits (by omega) (fun _=>le_rfl) i ⟨hr,hd,hc',hw,hl,ho⟩
  have fields:∀ i : Fin 7,B (![1689,1690,297,1692,1693,1697,1674] i)=
      (![[],[],words.flatMap frame,List.replicate C false,[true],ZeroPadding.pad C [true],
        UnaryTemplate.tape core] : Fin 7 → List Bool) i:=by
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
  exact ⟨hin,hcap,by simp,hc,⟨by rw [←pstream];exact prefixBound 297,hcount⟩,by omega,hheader,
    by simpa only [frame_length] using topFits,gateBound,published 4,published 5,published 2,published 0,
    (kept 4).trans (pubFields 1),published 6,symmetric_count C words.length _ A tb count,fields,
    published 7,bL,bW,(kept 10).trans (pubFields 7),by simp,support,bRaw⟩

theorem body_run (C core W L : ℕ) (bits out : List Bool) (words : List (List Bool))
    (pb : Fin 639 → List Bool) (tb : Fin 181 → List Bool)
    (hinput : 2*bits.length+1 ≤ C) (prefixBound : ∀ i,(pb i).length ≤ C)
    (pstream : pb 297=words.flatMap frame) (ptemplate : pb 624=UnaryTemplate.tape words.length)
    (praw : pb 1=frame bits)
    (table : tb 174=frame (CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)))
    (count : tb 178=UnaryTemplate.tape words.length)
    (topBound : ∀ i : Fin 181,i.val≠178 → (CloseoutRowsCircuitSymmetricTop.padded C tb i).length ≤ C)
    (hin : ∀ b∈words,2*b.length+1 ≤ C)
    (hcap : ∀ b∈words,2*CloseoutRowsGateMeasured.budget b+4 ≤ C)
    (hcount : 1+2*words.length ≤ C)
    (hc : 32*(descriptions core words 0 words.length+words.length+
      wires false core 1 (List.replicate C false) words 0 words.length+3) ≤ C)
    (hheader : EquationHeaderAppend.budget words.length+1 ≤ C) :
    let A:=CloseoutRowsCircuitSymmetricTop.output C words.length (CloseoutRowsCircuitHeader.codeWord bits 3)
      (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb
    let top:=CloseoutWitness.BitFields.payload (CloseoutRowsCircuitHeader.codeWord bits 3)
    let native:=(out++natWord words.length++frame top)++
      (List.range words.length).flatMap (outputs false core 1 (List.replicate C false) words)
    ∃ r,runFrom (CloseoutRowsCircuitBody.machine false)
      (CloseoutRowsCircuitBody.budget false C words.length top (descriptions core words 0 words.length)
        words.length (wires false core 1 (List.replicate C false) words 0 words.length) L W)
      ⟨(CloseoutRowsCircuitBody.machine false).start,CloseoutRowsCircuitColdEntry.heads out,A⟩=some r ∧
      r.steps ≤ CloseoutRowsCircuitBody.budget false C words.length top (descriptions core words 0 words.length)
        words.length (wires false core 1 (List.replicate C false) words 0 words.length) L W ∧
      r.final.heads=CloseoutRowsCircuitColdEntry.heads native ∧
      (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
        CloseoutRowsCircuitArithmeticDock.amount false (descriptions core words 0 words.length) words.length ≤ L ∧
        wires false core 1 (List.replicate C false) words 0 words.length ≤ W) ∧
      r.final.tapes 1688=native ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate C true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=frame bits ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes i).length ≤ C+1:=by
  have F:=fields_ready C core W L bits out words pb tb hinput prefixBound pstream ptemplate praw table count
    topBound hin hcap hcount hc hheader
  obtain ⟨r,hr,rs,rh,verdict,native,domain,driver,capW,capL,raw,small⟩:=
    CloseoutRowsCircuitBody.body_support false C core words.length words _ out _ 0 L W _
      F.input F.capacity F.positive F.resource F.source F.retainedFits F.header F.topFits F.gate
      F.driver F.log F.retained F.topWord F.stream F.scratch F.count F.ports F.rawCount F.capL F.capW F.flag
      F.membersFits F.privateSupport
  rw [←symmetric_heads] at hr
  exact ⟨r,hr,rs,rh,verdict,native,domain,driver,capW.trans F.capW,capL.trans F.capL,raw.trans F.raw,small⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricBody
