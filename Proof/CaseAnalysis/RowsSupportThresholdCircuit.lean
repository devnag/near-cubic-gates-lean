import Proof.CaseAnalysis.RowsSupportCircuitJoin
import Proof.CaseAnalysis.RowsCircuitThresholdRun

/-! Complete threshold circuit decision and retained native output, from
the frozen cold entry. Both malformed top and malformed bottom fields halt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold
open LocalBitMultitape RecoveryRootRound RepairRepresentation SupplierPipeline CanonicalWitnessCodec RadixSemantics
open ExtDecompositionBatch CloseoutRowsCircuitThresholdRun
open CloseoutRowsCircuitWords CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def test (scanned : Fin 1704 → Bool):=CloseoutRowsCircuitThresholdRun.test (fun i=>scanned (i.castAdd 1))
noncomputable def program : Σ s,Machine 1704 s:=
  ⟨_,CloseoutRowsGateColdPair.machine
    (TapeEmbedding.machine 1 CloseoutRowsCircuitColdThreshold.machine) (body true) test⟩
noncomputable def machine : Machine 1704 program.1:=program.2
def support (core : ℕ) (bits : List Bool):=match decoded bits with
  | none=>[]
  | some g=>(List.range (words bits).length).flatMap (supportOutput true core 1 (members g) (words bits))
def heads (native supports : List Bool) : Fin 1704 → ℕ:=Fin.addCases (m:=1703) (n:=1)
  (CloseoutRowsCircuitColdEntry.heads native) (fun _=>supports.length)
def input (C core W L : ℕ) (bits out supports : List Bool) : Fin 1704 → List Bool:=Fin.addCases (m:=1703) (n:=1)
  (CloseoutRowsCircuitColdEntry.input C core W L bits out) (fun _=>supports)

theorem support_pad (C core pos : ℕ) (m : List Bool) (ws : List (List Bool)) :
    supportOutput true core pos (ZeroPadding.pad C m) ws=supportOutput true core pos m ws:=by
  funext j
  simp [supportOutput,choose,CloseoutRowsCircuitBottom.kept,ZeroPadding.read_pad]

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
  have guard:CloseoutRowsCircuitThresholdRun.test first.final.scanned=true ↔ CloseoutRowsCircuitPrefix.valid true bits ∧ (decoded bits).isSome:=by
    have h638:first.final.heads 638=0:=observed.2.2.2 0
    have h1676:first.final.heads 1676=0:=observed.2.2.2 1
    simp only [CloseoutRowsCircuitThresholdRun.test,Configuration.scanned,h638,h1676,Bool.and_eq_true,observed.1,observed.2.1]
  have coldBound:=CloseoutRowsCircuitWholeBudget.threshold_cold_bound C bits hp ht
  have lifted:Step (TapeEmbedding.machine 1 CloseoutRowsCircuitColdThreshold.machine)
      (CloseoutRowsCircuitColdThreshold.budget C bits) (heads out supports) (input C core W L bits out supports)
      (Fin.addCases (m:=1703) (n:=1) first.final.heads (fun _=>supports.length))
      (Fin.addCases (m:=1703) (n:=1) first.final.tapes (fun _=>supports)):=
    (Step.of_run fr rfl rfl).embed (fun _ : Fin 1=>supports.length) (fun _ : Fin 1=>supports)
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
    have F:=
      CloseoutRowsCircuitThresholdBody.fields_ready C core W L bits out (words bits) pb tb g hg hi pbound
        (pstream.trans (stream bits).symm) ptemplate pcount praw meaning (bitmap g hg) tbound initialFits
        (by intro b hb;rw [word_length bits b hb];exact hi)
        (by
          intro b hb
          have h:=CloseoutRowsCircuitCapacity.gate_fits b
          rw [word_length bits b hb] at h;exact h.trans hC)
        countFits resourceFits headerFits
    obtain ⟨B,bodyRun,result,small,bW,bL,braw⟩:=published_run true C core g.wireCount (words bits)
      _ out supports _ bits _ L W _ F
    have sameSupport:supportPrefix true core 1 (ZeroPadding.pad C (members g)) (words bits) supports (words bits).length=
        supports++support core bits:=by
      simp only [supportPrefix,support_pad,support,hg]
    have sameNative:(out++natWord g.wireCount++frame (top g))++
        (List.range (words bits).length).flatMap
          (outputs true core 1 (ZeroPadding.pad C (members g)) (words bits))=out++native core bits:=by
      simp only [native,hg,outputs_pad,List.append_assoc]
    have actualBody:Step (body true)
        (bodyBudget true C core g.wireCount (top g)
          (descriptions core (words bits) (initial g) (words bits).length) (words bits).length
          (wires true core 1 (ZeroPadding.pad C (members g)) (words bits) 0 (words bits).length) L W)
        (Fin.addCases (m:=1703) (n:=1) first.final.heads (fun _=>supports.length))
        (Fin.addCases (m:=1703) (n:=1) first.final.tapes (fun _=>supports))
        (heads (out++native core bits) (supports++support core bits))
        (Fin.addCases (m:=1703) (n:=1) B (fun _=>supports++support core bits)):=by
      unfold Threshold.heads
      rw [(yes g hg).1,(yes g hg).2]
      rw [CloseoutRowsCircuitPostTop.threshold_heads,←sameSupport,←sameNative]
      exact bodyRun
    have all:=guarded_step lifted actualBody test (by
      change CloseoutRowsCircuitThresholdRun.test first.final.scanned=true
      exact guard.mpr good)
    have paid:=body_bound true C core g.wireCount _ (words bits).length _ L W (top g)
      headerFits btop resourceFits
    have bound:=joined_bound C core bits.length (words bits).length _ _ countBound coldBound paid
    change Step machine _ _ _ _ _ at all
    obtain ⟨r,hr,rh,rt,rs⟩:=all.enlarge bound
    have oldTape (i : Fin 1703):r.final.tapes (i.castAdd 1)=B i:=by rw [rt];simp only [Fin.addCases_left]
    refine ⟨r,hr,rs,by rw [rh];rfl,?_,by rw [rh];rfl,(oldTape 1).trans braw,
      by rw [rh];rfl,(oldTape 1694).trans result.driver,fun _=>?_⟩
    · rw [show r.final.tapes 1700=B 1700 from oldTape 1700,result.flag,passed_decode core W L bits g hg]
      simp only [initial,members,wires_pad,good.1,true_and]
    · refine ⟨rh,?_,(oldTape 1674).trans result.domain,(oldTape 1694).trans result.driver,
        (oldTape 1698).trans bW,(oldTape 1699).trans bL,(oldTape 1).trans braw,by rw [rt];rfl,?_⟩
      · rw [show r.final.tapes 1688=B 1688 from oldTape 1688,result.stream]
        simp only [native,hg,top,members,outputs_pad,List.append_assoc]
      · intro i h1 h2 h3 h4 h5 h6
        rw [oldTape i];exact small i h1 h2 h3 h4 h5 h6
  · have bad:CloseoutRowsCircuitThresholdRun.test first.final.scanned=false:=Bool.eq_false_iff.mpr (fun h=>good (guard.mp h))
    have rejected:=rejected_step (body true) lifted test (by
      change CloseoutRowsCircuitThresholdRun.test first.final.scanned=false
      exact bad)
    have bound:CloseoutRowsCircuitColdThreshold.budget C bits+1 ≤ circuitBudget C core bits.length:=by
      unfold circuitBudget
      nlinarith
    change Step machine _ _ _ _ _ at rejected
    obtain ⟨r,hr,rh,rt,rs⟩:=rejected.enlarge bound
    have noPass:¬passed core W L bits:=by
      rintro ⟨pre,g,hg,_⟩
      exact good ⟨pre,Option.isSome_iff_exists.mpr ⟨g,hg⟩⟩
    have oldTape (i : Fin 1703):r.final.tapes (i.castAdd 1)=first.final.tapes i:=by rw [rt];simp only [Fin.addCases_left]
    have oldHead (i : Fin 1703):r.final.heads (i.castAdd 1)=first.final.heads i:=by rw [rh];simp only [Fin.addCases_left]
    refine ⟨r,hr,rs,?_,?_,(oldHead 1).trans aliases.1,(oldTape 1).trans aliases.2.1,
      (oldHead 1694).trans aliases.2.2.1,(oldTape 1694).trans aliases.2.2.2,fun h=>False.elim (noPass h)⟩
    · rw [show r.final.heads 1700=first.final.heads 1700 from oldHead 1700];exact observed.2.2.2 2
    · rw [show r.final.tapes 1700=first.final.tapes 1700 from oldTape 1700,observed.2.2.1]
      change false=true ↔ passed core W L bits
      simp only [Bool.false_eq_true,noPass]

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Threshold
