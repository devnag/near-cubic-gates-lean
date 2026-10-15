import Proof.CaseAnalysis.RowsCircuitAliases

/-! Complete threshold circuit decision and retained native output, from
the frozen cold entry. Both malformed top and malformed bottom fields halt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdRun
open LocalBitMultitape RecoveryRootRound RepairRepresentation SupplierPipeline CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
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
  have ht:2*CloseoutRowsGateMeasured.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+4 ≤ C:=by
    have h:=CloseoutRowsCircuitCapacity.gate_fits (CloseoutRowsCircuitHeader.codeWord bits 3)
    rw [code_length] at h;exact h.trans hC
  have countBound:=CloseoutRowsCircuitWords.count_bound bits
  have rawBound:1+2*(bits.length+1) ≤ C:=(CloseoutRowsCircuitCapacity.raw_fits _).2.trans hC
  have countFits:1+2*(words bits).length ≤ C:=by omega
  obtain ⟨pb,tb,first,fr,fs,pflag,pstream,pcount,ptemplate,praw,pbound,meaning,tbound,bitmap,yes,no⟩:=
    CloseoutRowsCircuitColdThreshold.cold_run_rich C core W L bits out hi ht hp
  rw [←words_count] at pcount ptemplate meaning bitmap yes no
  have topFlag:(readTapeBit (tb 1037) 0=true ↔ (decoded bits).isSome):=meaning.2.1
  have observed:(readTapeBit (first.final.tapes 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid true bits) ∧
      (readTapeBit (first.final.tapes 1676) 0=true ↔ (decoded bits).isSome) ∧
      first.final.tapes 1700=[] ∧ ∀ i : Fin 3,first.final.heads (![638,1676,1700] i)=0:=by
    cases hd:decoded bits with
    | none=>
      have hn:¬(decoded bits).isSome:=by rw [hd];simp
      have ft:=(no hn).1
      have fh:=(no hn).2
      rw [ft]
      have kept:=CloseoutRowsCircuitColdFlags.threshold_middle_kept C
        (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb
      refine ⟨?_,?_,(kept 1).trans (CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb 7),?_⟩
      · have same:CloseoutRowsCircuitThresholdTop.middle C
            (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb 638=pb 638:=
          (kept 0).trans (CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 638)
        rw [same];exact pflag
      · rw [CloseoutRowsCircuitColdFlags.threshold_middle_flag]
        simpa only [hd] using topFlag
      · intro i;rw [fh];fin_cases i <;> rfl
    | some g=>
      have ft:=(yes g hd).1
      have fh:=(yes g hd).2
      rw [ft]
      have kept:=CloseoutRowsCircuitPostTop.threshold_kept C
        (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb g
      refine ⟨?_,?_,(kept 10).trans (CloseoutRowsCircuitColdEntry.public_fields C core W L bits out pb 7),?_⟩
      · have same:CloseoutRowsCircuitThresholdTop.output C
            (CloseoutRowsCircuitColdEntry.output C core W L bits out pb) tb g 638=pb 638:=
          (kept 2).trans (CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 638)
        rw [same];exact pflag
      · rw [CloseoutRowsCircuitColdFlags.threshold_output_flag]
        simpa only [hd] using topFlag
      · intro i;rw [fh];exact CloseoutRowsCircuitColdFlags.threshold_heads out _ i
  have aliases:first.final.heads 1=0 ∧ first.final.tapes 1=frame bits ∧
      first.final.heads 1694=0 ∧ first.final.tapes 1694=List.replicate C true:=by
    cases hd:decoded bits with
    | none=>
      have hn:¬(decoded bits).isSome:=by rw [hd];simp
      rw [(no hn).1,(no hn).2]
      refine ⟨rfl,?_,rfl,?_⟩
      · exact (CloseoutRowsCircuitColdAliases.threshold_middle C _ tb 0).trans
          ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 1).trans praw)
      · exact (CloseoutRowsCircuitColdAliases.threshold_middle C _ tb 1).trans
          (CloseoutRowsCircuitColdEntry.output_external C core W L bits out pb 0)
    | some g=>
      rw [(yes g hd).1,(yes g hd).2]
      refine ⟨rfl,?_,rfl,CloseoutRowsCircuitColdAliases.threshold_driver C _ tb g⟩
      exact (CloseoutRowsCircuitPostTop.threshold_kept C _ tb g 0).trans
        ((CloseoutRowsCircuitColdEntry.output_prefix C core W L bits out pb 1).trans praw)
  have guard:test first.final.scanned=true ↔ CloseoutRowsCircuitPrefix.valid true bits ∧ (decoded bits).isSome:=by
    have h638:first.final.heads 638=0:=observed.2.2.2 0
    have h1676:first.final.heads 1676=0:=observed.2.2.2 1
    simp only [test,Configuration.scanned,h638,h1676,Bool.and_eq_true,observed.1,observed.2.1]
  have coldBound:=CloseoutRowsCircuitWholeBudget.threshold_cold_bound C bits hp ht
  by_cases good:CloseoutRowsCircuitPrefix.valid true bits ∧ (decoded bits).isSome
  · obtain ⟨g,hg⟩:=Option.isSome_iff_exists.mp good.2
    have counters:=CloseoutRowsCircuitResourceBounds.gate_counters g
      (CloseoutRowsCircuitHeader.codeWord bits 3) hg
    rw [code_length] at counters
    have initialBound:initial g ≤ 2*CloseoutRowsCircuitResourceBounds.counterBound bits.length:=by
      unfold initial CloseoutRowsCircuitThresholdTop.weights CloseoutRowsCircuitThresholdTop.theta
      omega
    have initialFits:initial g ≤ C:=initialBound.trans
      ((CloseoutRowsCircuitCapacity.counters_fit bits.length).trans hC)
    have totals:=CloseoutRowsCircuitResourceBounds.allraw_totals true core bits.length 1 (initial g)
      (words bits).length (ZeroPadding.pad C (members g)) (words bits) countBound
      (fun b hb=>(word_length bits b hb).le) initialBound le_rfl
    have resourceFits:32*(descriptions core (words bits) (initial g) (words bits).length+(words bits).length+
        wires true core 1 (ZeroPadding.pad C (members g)) (words bits) 0 (words bits).length+3) ≤ C:=
      (CloseoutRowsCircuitCapacity.resource_fit bits.length _ _ _ totals.1 countBound totals.2).trans hC
    have retainedBound:g.wireCount ≤ bits.length+1:=by
      have small:g.wireCount ≤ (words bits).length:=by
        simpa only [SupportedNormalizedGate.wireCount,Fintype.card_fin] using Finset.card_le_univ g.support
      exact small.trans countBound
    have headerFits:EquationHeaderAppend.budget g.wireCount+1 ≤ C:=
      (CloseoutRowsCircuitCapacity.header_fits _ _ retainedBound).trans hC
    have btop:2*(top g).length+1 ≤ C:=by
      have h:=tbound 1033 (by decide)
      have nativeField:tb 1033=frame (top g):=(meaning.2.2 g hg).1
      change (ZeroPadding.pad C (tb 1033)).length ≤ C at h
      rw [nativeField,ZeroPadding.pad_length,frame_length] at h
      exact (Nat.le_max_right _ _).trans h
    obtain ⟨body,br,bs,bh,bflag,bnative,bdomain,bdriver,bW,bL,braw,bsupport⟩:=
      CloseoutRowsCircuitThresholdBody.body_run C core W L bits out (words bits) pb tb g hg hi pbound
        (pstream.trans (stream bits).symm) ptemplate pcount praw meaning (bitmap g hg) tbound initialFits
        (by intro b hb;rw [word_length bits b hb];exact hi)
        (by
          intro b hb
          have h:=CloseoutRowsCircuitCapacity.gate_fits b
          rw [word_length bits b hb] at h;exact h.trans hC)
        countFits resourceFits headerFits
    have br':runFrom (CloseoutRowsCircuitBody.machine true)
        (CloseoutRowsCircuitBody.budget true C g.wireCount (top g)
          (descriptions core (words bits) (initial g) (words bits).length) (words bits).length
          (wires true core 1 (members g) (words bits) 0 (words bits).length) L W)
        (RecoveryCalls.restarted (CloseoutRowsCircuitBody.machine true) first.final.heads first.final.tapes)=some body:=by
      rw [(yes g hg).1,(yes g hg).2]
      simpa only [RecoveryCalls.restarted,top,initial,members,wires_pad] using br
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted CloseoutRowsCircuitColdThreshold.machine
      (CloseoutRowsCircuitBody.machine true) test _ _ _ _ first body fr br' (guard.mpr good)
    have paid:=CloseoutRowsCircuitWholeBudget.body_bound true C g.wireCount
      (descriptions core (words bits) (initial g) (words bits).length) (words bits).length
      (wires true core 1 (members g) (words bits) 0 (words bits).length) L W (top g) headerFits btop
      (by simpa only [wires_pad] using resourceFits)
    have bound:=CloseoutRowsCircuitWholeBudget.joined_bound C bits.length (words bits).length _ _ countBound coldBound paid
    have more:=runFrom_moreFuel machine _ (CloseoutRowsCircuitWholeBudget.budget C bits.length-
      (CloseoutRowsCircuitColdThreshold.budget C bits+1+CloseoutRowsCircuitBody.budget true C g.wireCount (top g)
        (descriptions core (words bits) (initial g) (words bits).length) (words bits).length
        (wires true core 1 (members g) (words bits) 0 (words bits).length) L W+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    have tape (i : Fin 1703):r.final.tapes i=body.final.tapes i:=congrFun rt i
    have endHeads:r.final.heads=CloseoutRowsCircuitColdEntry.heads (out++native core bits):=by
      rw [rh,bh]
      simp only [native,hg,top,members,outputs_pad,List.append_assoc]
    refine ⟨r,more,rs.trans bound,by rw [endHeads];rfl,?_,
      by rw [endHeads];rfl,(tape 1).trans braw,by rw [endHeads];rfl,(tape 1694).trans bdriver,fun _=>?_⟩
    · rw [tape 1700,bflag,passed_decode core W L bits g hg]
      simp only [initial,members,wires_pad,good.1,true_and]
    · refine ⟨endHeads,?_,(tape 1674).trans bdomain,(tape 1694).trans bdriver,
        (tape 1698).trans bW,(tape 1699).trans bL,(tape 1).trans braw,?_⟩
      · rw [tape 1688,bnative]
        simp only [native,hg,top,members,outputs_pad,List.append_assoc]
      · intro i h1 h2 h3 h4 h5 h6
        rw [tape i];exact bsupport i h1 h2 h3 h4 h5 h6
  · have bad:test first.final.scanned=false:=Bool.eq_false_iff.mpr (fun h=>good (guard.mp h))
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.rejected CloseoutRowsCircuitColdThreshold.machine
      (CloseoutRowsCircuitBody.machine true) test _ _ _ first fr bad
    have bound:CloseoutRowsCircuitColdThreshold.budget C bits+1 ≤
        CloseoutRowsCircuitWholeBudget.budget C bits.length:=by
      unfold CloseoutRowsCircuitWholeBudget.budget;nlinarith
    have more:=runFrom_moreFuel machine _ (CloseoutRowsCircuitWholeBudget.budget C bits.length-
      (CloseoutRowsCircuitColdThreshold.budget C bits+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    have noPass:¬passed core W L bits:=by
      rintro ⟨pre,g,hg,_⟩
      exact good ⟨pre,Option.isSome_iff_exists.mpr ⟨g,hg⟩⟩
    refine ⟨r,more,rs.trans bound,?_,?_,
      (congrFun rh 1).trans aliases.1,(congrFun rt 1).trans aliases.2.1,
      (congrFun rh 1694).trans aliases.2.2.1,(congrFun rt 1694).trans aliases.2.2.2,
      fun h=>False.elim (noPass h)⟩
    · rw [rh];exact observed.2.2.2 2
    · rw [rt,observed.2.2.1]
      change false=true ↔ passed core W L bits
      simp only [Bool.false_eq_true,noPass]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitThresholdRun
