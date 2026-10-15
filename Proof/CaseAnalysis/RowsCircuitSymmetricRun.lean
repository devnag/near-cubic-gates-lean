import Proof.CaseAnalysis.RowsCircuitAliases

/-! The full symmetric circuit worker starts at the frozen cold ABI,
rejects malformed fields, and executes the common native/resource body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricRun
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsGatePairHeads CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_run (C core W L : ℕ) (bits out : List Bool)
    (hC : CloseoutRowsCircuitCapacity.capacity bits.length ≤ C) : ∃ r,
    runFrom machine (CloseoutRowsCircuitWholeBudget.budget C bits.length)
      ⟨machine.start,CloseoutRowsCircuitColdEntry.heads out,
        CloseoutRowsCircuitColdEntry.input C core W L bits out⟩=some r ∧
    r.steps ≤ CloseoutRowsCircuitWholeBudget.budget C bits.length ∧ r.final.heads 1700=0 ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ passed core W L bits) ∧
    r.final.heads 1=0 ∧ r.final.tapes 1=frame bits ∧
    r.final.heads 1694=0 ∧ r.final.tapes 1694=List.replicate C true ∧
    (passed core W L bits →
      r.final.heads=CloseoutRowsCircuitColdEntry.heads (out++native core bits) ∧
      r.final.tapes 1688=out++native core bits ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate C true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=frame bits ∧
      ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes i).length ≤ C+1):=by
  have hi:2*bits.length+1 ≤ C:=(CloseoutRowsCircuitCapacity.raw_fits _).1.trans hC
  have hp:CloseoutRowsCircuitPrefix.budget bits+1 ≤ C:=(CloseoutRowsCircuitCapacity.prefix_fits bits).trans hC
  have ht:CloseoutRowsCircuitSymTop.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+1 ≤ C:=by
    have h:=CloseoutRowsCircuitCapacity.top_fits (CloseoutRowsCircuitHeader.codeWord bits 3)
    rw [code_length] at h;exact h.trans hC
  have countBound:=CloseoutRowsCircuitWords.count_bound bits
  have rawBound:1+2*(bits.length+1) ≤ C:=(CloseoutRowsCircuitCapacity.raw_fits _).2.trans hC
  have countFits:1+2*(words bits).length ≤ C:=by omega
  obtain ⟨pb,tb,A,first,pflag,pstream,pcount,ptemplate,praw,pbound,table,tcount,tbound,tflag,yes,no⟩:=
    CloseoutRowsCircuitColdSymmetric.cold_run_fields C core W L bits out hi ht
      (by rw [←words_count];omega) ((CloseoutRowsCircuitCapacity.positive _).trans hC) hp
  have topFlag:(readTapeBit (tb 179) 0=true ↔
      CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3)):=by
    simpa only [words_count] using tflag
  have observed:(readTapeBit (A 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid false bits) ∧
      (readTapeBit (A 1676) 0=true ↔ CloseoutRowsCircuitSymTop.valid (words bits).length
        (CloseoutRowsCircuitHeader.codeWord bits 3)) ∧ A 1700=[]:=by
    by_cases h:CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3)
    · rw [yes (by simpa only [words_count] using h)]
      have kept:=CloseoutRowsCircuitPostTop.symmetric_kept C
        (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3)
        (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb
      refine ⟨?_,?_,(kept 10).trans (CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb 7)⟩
      · have same : CloseoutRowsCircuitSymmetricTop.output C
            (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
            (CloseoutRowsCircuitHeader.codeWord bits 3)
            (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb 638=pb 638 :=
          (kept 2).trans (CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 638)
        rw [same];exact pflag
      · rw [CloseoutRowsCircuitColdFlags.symmetric_output_flag];exact topFlag
    · rw [no (by simpa only [words_count] using h)]
      have kept:=CloseoutRowsCircuitColdFlags.symmetric_middle_kept C
        (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb
      refine ⟨?_,?_,(kept 1).trans (CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb 7)⟩
      · have same : CloseoutRowsCircuitSymmetricTop.middle C
            (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb 638=pb 638 :=
          (kept 0).trans (CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 638)
        rw [same];exact pflag
      · rw [CloseoutRowsCircuitColdFlags.symmetric_middle_flag];exact topFlag
  have aliases:A 1=frame bits ∧ A 1694=List.replicate C true:=by
    by_cases h:CloseoutRowsCircuitSymTop.valid
        (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2))
        (CloseoutRowsCircuitHeader.codeWord bits 3)
    · rw [yes h]
      exact ⟨(CloseoutRowsCircuitPostTop.symmetric_kept C _ _ _ tb 0).trans
        ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 1).trans praw),
        CloseoutRowsCircuitPublishedFields.symmetric_publication C _ _ _ tb 4⟩
    · rw [no h]
      exact ⟨(CloseoutRowsCircuitColdAliases.symmetric_middle C _ tb 0).trans
        ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 1).trans praw),
        (CloseoutRowsCircuitColdAliases.symmetric_middle C _ tb 1).trans
          (CloseoutRowsCircuitColdEntry.output_external C core W L bits out pb 0)⟩
  have guard:test (fun i=>readTapeBit (A i) (CloseoutRowsCircuitColdEntry.heads out i))=true ↔
      CloseoutRowsCircuitPrefix.valid false bits ∧
        CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3):=by
    change (readTapeBit (A 638) 0 && readTapeBit (A 1676) 0)=true ↔ _
    rw [Bool.and_eq_true,observed.1,observed.2.1]
  have coldBound:=CloseoutRowsCircuitWholeBudget.symmetric_cold_bound C bits hp ht
  by_cases good:CloseoutRowsCircuitPrefix.valid false bits ∧
      CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3)
  · have totals:=CloseoutRowsCircuitResourceBounds.allraw_totals false core bits.length 1 0
      (words bits).length (List.replicate C false) (words bits) countBound
      (fun b hb=>(word_length bits b hb).le) (Nat.zero_le _) le_rfl
    have resourceFits:32*(descriptions core (words bits) 0 (words bits).length+(words bits).length+
        wires false core 1 (List.replicate C false) (words bits) 0 (words bits).length+3) ≤ C:=
      (CloseoutRowsCircuitCapacity.resource_fit bits.length _ _ _ totals.1 countBound totals.2).trans hC
    have headerFits:EquationHeaderAppend.budget (words bits).length+1 ≤ C:=
      (CloseoutRowsCircuitCapacity.header_fits _ _ countBound).trans hC
    have btop:2*(top bits).length+1 ≤ C:=by
      have h:=tbound 174 (by decide)
      change (ZeroPadding.pad C (tb 174)).length ≤ C at h
      rw [table,ZeroPadding.pad_length,frame_length] at h
      exact (Nat.le_max_right _ _).trans h
    obtain ⟨body,br,bs,bh,bflag,bnative,bdomain,bdriver,bW,bL,braw,bsupport⟩:=
      CloseoutRowsCircuitSymmetricBody.body_run C core W L bits out (words bits) pb tb hi pbound
        (pstream.trans (stream bits).symm) (by simpa only [words_count] using ptemplate) praw table
        (by simpa only [words_count] using tcount) tbound
        (by intro b hb;rw [word_length bits b hb];exact hi)
        (by
          intro b hb
          have h:=CloseoutRowsCircuitCapacity.gate_fits b
          rw [word_length bits b hb] at h;exact h.trans hC)
        countFits resourceFits headerFits
    have br':runFrom (CloseoutRowsCircuitBody.machine false)
        (CloseoutRowsCircuitBody.budget false C (words bits).length (top bits)
          (descriptions core (words bits) 0 (words bits).length) (words bits).length
          (wires false core 1 [] (words bits) 0 (words bits).length) L W)
        (RecoveryCalls.restarted (CloseoutRowsCircuitBody.machine false) (CloseoutRowsCircuitColdEntry.heads out) A)=some body:=by
      have sameWire : wires false core 1 (List.replicate C false) (words bits) 0 (words bits).length=
          wires false core 1 [] (words bits) 0 (words bits).length:=by rfl
      rw [yes (by simpa only [words_count] using good.2)]
      simpa only [←words_count,top,RecoveryCalls.restarted,sameWire] using br
    obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsGateSourceCalls.joined CloseoutRowsCircuitColdSymmetric.machine
      (CloseoutRowsCircuitBody.machine false) test _ _ _ _ A first body br' (guard.mpr good)
    have paid:=CloseoutRowsCircuitWholeBudget.body_bound false C (words bits).length
      (descriptions core (words bits) 0 (words bits).length) (words bits).length
      (wires false core 1 [] (words bits) 0 (words bits).length) L W (top bits) headerFits btop resourceFits
    have bound:=CloseoutRowsCircuitWholeBudget.joined_bound C bits.length (words bits).length _ _ countBound coldBound paid
    have more:=runFrom_moreFuel machine _ (CloseoutRowsCircuitWholeBudget.budget C bits.length-
      (CloseoutRowsCircuitColdSymmetric.budget C bits+1+
        CloseoutRowsCircuitBody.budget false C (words bits).length (top bits)
          (descriptions core (words bits) 0 (words bits).length) (words bits).length
          (wires false core 1 [] (words bits) 0 (words bits).length) L W+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    have tape (i : Fin 1703):r.final.tapes i=body.final.tapes i:=congrFun rt i
    have sameOutput : outputs false core 1 (List.replicate C false) (words bits)=
        outputs false core 1 [] (words bits):=by funext j;rfl
    have endHeads:r.final.heads=CloseoutRowsCircuitColdEntry.heads (out++native core bits):=by
      rw [rh,bh,sameOutput];simp only [native,top,List.append_assoc]
    refine ⟨r,more,rs.trans bound,by rw [endHeads];rfl,?_,
      by rw [endHeads];rfl,(tape 1).trans braw,by rw [endHeads];rfl,(tape 1694).trans bdriver,fun _=>?_⟩
    · rw [tape 1700,bflag]
      exact ⟨fun h=>⟨good.1,good.2,h⟩,fun h=>h.2.2⟩
    · refine ⟨endHeads,?_,(tape 1674).trans bdomain,(tape 1694).trans bdriver,
        (tape 1698).trans bW,(tape 1699).trans bL,(tape 1).trans braw,?_⟩
      · rw [tape 1688,bnative,sameOutput];simp only [native,top,List.append_assoc]
      · intro i h1 h2 h3 h4 h5 h6
        rw [tape i];exact bsupport i h1 h2 h3 h4 h5 h6
  · have bad:test (fun i=>readTapeBit (A i) (CloseoutRowsCircuitColdEntry.heads out i))=false:=
      Bool.eq_false_iff.mpr (fun h=>good (guard.mp h))
    obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsGatePairHeads.rejected CloseoutRowsCircuitColdSymmetric.machine
      (CloseoutRowsCircuitBody.machine false) test _ _ _ _ first bad
    have bound:CloseoutRowsCircuitColdSymmetric.budget C bits+1 ≤
        CloseoutRowsCircuitWholeBudget.budget C bits.length:=by
      unfold CloseoutRowsCircuitWholeBudget.budget;nlinarith
    have more:=runFrom_moreFuel machine _ (CloseoutRowsCircuitWholeBudget.budget C bits.length-
      (CloseoutRowsCircuitColdSymmetric.budget C bits+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    have noPass:¬passed core W L bits:=fun h=>good ⟨h.1,h.2.1⟩
    refine ⟨r,more,rs.trans bound,by rw [rh];rfl,?_,
      by rw [rh];rfl,(congrFun rt 1).trans aliases.1,
      by rw [rh];rfl,(congrFun rt 1694).trans aliases.2,fun h=>False.elim (noPass h)⟩
    rw [rt,observed.2.2]
    change false=true ↔ passed core W L bits
    simp only [Bool.false_eq_true,noPass]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymmetricRun
