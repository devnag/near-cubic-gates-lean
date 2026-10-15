import Proof.CaseAnalysis.RowsSupportCircuitJoin
import Proof.CaseAnalysis.RowsCircuitSymmetricRun

/-! The full symmetric circuit worker starts at the frozen cold ABI,
rejects malformed fields, and executes the common native/resource body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric
open LocalBitMultitape RecoveryRootRound RepairRepresentation ExtDecompositionBatch
open CloseoutRowsCircuitSymmetricRun
open CloseoutRowsGatePairHeads CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def test (scanned : Fin 1704 → Bool):=CloseoutRowsCircuitSymmetricRun.test (fun i=>scanned (i.castAdd 1))
noncomputable def program : Σ s,Machine 1704 s:=
  ⟨_,CloseoutRowsGateColdPair.machine
    (TapeEmbedding.machine 1 CloseoutRowsCircuitColdSymmetric.machine) (body false) test⟩
noncomputable def machine : Machine 1704 program.1:=program.2
def support (core : ℕ) (bits : List Bool):=(List.range (words bits).length).flatMap
  (supportOutput false core 1 [] (words bits))
def heads (native supports : List Bool) : Fin 1704 → ℕ:=Fin.addCases (m:=1703) (n:=1)
  (CloseoutRowsCircuitColdEntry.heads native) (fun _=>supports.length)
def input (C core W L : ℕ) (bits out supports : List Bool) : Fin 1704 → List Bool:=Fin.addCases (m:=1703) (n:=1)
  (CloseoutRowsCircuitColdEntry.input C core W L bits out) (fun _=>supports)

theorem cold_run (C core W L : ℕ) (bits out supports : List Bool)
    (hC : CloseoutRowsCircuitCapacity.capacity bits.length ≤ C) : ∃ r : ExecutionReceipt 1704 program.1,
    runFrom machine (circuitBudget C core bits.length)
      ⟨machine.start,heads out supports,
        input C core W L bits out supports⟩=some r ∧
    r.steps ≤ circuitBudget C core bits.length ∧ r.final.heads 1700=0 ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ passed core W L bits) ∧
    r.final.heads 1=0 ∧ r.final.tapes 1=frame bits ∧
    r.final.heads 1694=0 ∧ r.final.tapes 1694=List.replicate C true ∧
    (passed core W L bits →
      r.final.heads=heads (out++native core bits) (supports++support core bits) ∧
      r.final.tapes 1688=out++native core bits ∧ r.final.tapes 1674=UnaryTemplate.tape core ∧
      r.final.tapes 1694=List.replicate C true ∧ r.final.tapes 1698=List.replicate W true ∧
      r.final.tapes 1699=List.replicate L true ∧ r.final.tapes 1=frame bits ∧
      r.final.tapes 1703=supports++support core bits ∧
      ∀ i : Fin 1703,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (r.final.tapes (i.castAdd 1)).length ≤ C+1):=by
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
  have guard:CloseoutRowsCircuitSymmetricRun.test (fun i=>readTapeBit (A i) (CloseoutRowsCircuitColdEntry.heads out i))=true ↔
      CloseoutRowsCircuitPrefix.valid false bits ∧
        CloseoutRowsCircuitSymTop.valid (words bits).length (CloseoutRowsCircuitHeader.codeWord bits 3):=by
    change (readTapeBit (A 638) 0 && readTapeBit (A 1676) 0)=true ↔ _
    rw [Bool.and_eq_true,observed.1,observed.2.1]
  have coldBound:=CloseoutRowsCircuitWholeBudget.symmetric_cold_bound C bits hp ht
  obtain ⟨firstReceipt,firstRun,firstTapes,firstHeads,_firstSteps⟩:=first
  have lifted:Step (TapeEmbedding.machine 1 CloseoutRowsCircuitColdSymmetric.machine)
      (CloseoutRowsCircuitColdSymmetric.budget C bits) (heads out supports) (input C core W L bits out supports)
      (heads out supports) (Fin.addCases (m:=1703) (n:=1) A (fun _=>supports)):=
    (Step.of_run firstRun firstHeads firstTapes).embed (fun _ : Fin 1=>supports.length) (fun _ : Fin 1=>supports)
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
    have F:=
      CloseoutRowsCircuitSymmetricBody.fields_ready C core W L bits out (words bits) pb tb hi pbound
        (pstream.trans (stream bits).symm) (by simpa only [words_count] using ptemplate) praw table
        (by simpa only [words_count] using tcount) tbound
        (by intro b hb;rw [word_length bits b hb];exact hi)
        (by
          intro b hb
          have h:=CloseoutRowsCircuitCapacity.gate_fits b
          rw [word_length bits b hb] at h;exact h.trans hC)
        countFits resourceFits headerFits
    obtain ⟨B,bodyRun,result,small,bW,bL,braw⟩:=published_run false C core (words bits).length (words bits)
      _ out supports _ bits 0 L W _ F
    have sameSupport:supportPrefix false core 1 (List.replicate C false) (words bits) supports (words bits).length=
        supports++support core bits:=by rfl
    have sameOutput:outputs false core 1 (List.replicate C false) (words bits)=
        outputs false core 1 [] (words bits):=by rfl
    have actualBody:Step (body false)
        (bodyBudget false C core (words bits).length (top bits)
          (descriptions core (words bits) 0 (words bits).length) (words bits).length
          (wires false core 1 (List.replicate C false) (words bits) 0 (words bits).length) L W)
        (heads out supports) (Fin.addCases (m:=1703) (n:=1) A (fun _=>supports))
        (heads (out++native core bits) (supports++support core bits))
        (Fin.addCases (m:=1703) (n:=1) B (fun _=>supports++support core bits)):=by
      unfold Symmetric.heads
      rw [yes (by simpa only [words_count] using good.2)]
      simpa only [←words_count,←CloseoutRowsCircuitPostTop.symmetric_heads,sameSupport,
        sameOutput,Symmetric.heads,native,top,List.append_assoc] using bodyRun
    have all:=guarded_step lifted actualBody test (by
      simpa only [test,heads,Fin.addCases_left] using guard.mpr good)
    have paid:=body_bound false C core (words bits).length _ (words bits).length _ L W (top bits)
      headerFits btop resourceFits
    have bound:=joined_bound C core bits.length (words bits).length _ _ countBound coldBound paid
    change Step machine _ _ _ _ _ at all
    obtain ⟨r,hr,rh,rt,rs⟩:=all.enlarge bound
    have oldTape (i : Fin 1703):r.final.tapes (i.castAdd 1)=B i:=by rw [rt];simp only [Fin.addCases_left]
    refine ⟨r,hr,rs,by rw [rh];rfl,?_,by rw [rh];rfl,(oldTape 1).trans braw,
      by rw [rh];rfl,(oldTape 1694).trans result.driver,fun _=>?_⟩
    · rw [show r.final.tapes 1700=B 1700 from oldTape 1700,result.flag]
      exact ⟨fun h=>⟨good.1,good.2,h⟩,fun h=>h.2.2⟩
    · refine ⟨rh,?_,(oldTape 1674).trans result.domain,(oldTape 1694).trans result.driver,
        (oldTape 1698).trans bW,(oldTape 1699).trans bL,(oldTape 1).trans braw,by rw [rt];rfl,?_⟩
      · rw [show r.final.tapes 1688=B 1688 from oldTape 1688,result.stream,sameOutput]
        simp only [native,top,List.append_assoc]
      · intro i h1 h2 h3 h4 h5 h6
        rw [oldTape i];exact small i h1 h2 h3 h4 h5 h6
  · have bad:CloseoutRowsCircuitSymmetricRun.test (fun i=>readTapeBit (A i) (CloseoutRowsCircuitColdEntry.heads out i))=false:=
      Bool.eq_false_iff.mpr (fun h=>good (guard.mp h))
    have rejected:=rejected_step (body false) lifted test (by
      simpa only [test,heads,Fin.addCases_left] using bad)
    have bound:CloseoutRowsCircuitColdSymmetric.budget C bits+1 ≤ circuitBudget C core bits.length:=by
      unfold circuitBudget
      nlinarith
    change Step machine _ _ _ _ _ at rejected
    obtain ⟨r,hr,rh,rt,rs⟩:=rejected.enlarge bound
    have noPass:¬passed core W L bits:=fun h=>good ⟨h.1,h.2.1⟩
    have oldTape (i : Fin 1703):r.final.tapes (i.castAdd 1)=A i:=by rw [rt];simp only [Fin.addCases_left]
    refine ⟨r,hr,rs,by rw [rh];rfl,?_,by rw [rh];rfl,(oldTape 1).trans aliases.1,
      by rw [rh];rfl,(oldTape 1694).trans aliases.2,fun h=>False.elim (noPass h)⟩
    rw [show r.final.tapes 1700=A 1700 from oldTape 1700,observed.2.2]
    change false=true ↔ passed core W L bits
    simp only [Bool.false_eq_true,noPass]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Symmetric
