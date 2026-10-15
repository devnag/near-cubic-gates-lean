import Proof.CaseAnalysis.WitnessSumTail

/-! One complete raw sum: exact header and actual count, retained count
record, counted original terms, fixed mass check, and successful reset.
Every failure stops before the next stage and needs no restored layout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def worker {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  SumWork.enter (SumDock.body circuit k q)
noncomputable def tail {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  SumTail.machine (worker circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  RecoveryGatedSequence.machine SumDock.reader (tail circuit k q) 724
def budget (P H B T k cost : ℕ) (bits arity : List Bool):=
  SumPrefix.budget bits arity T+
    SumTail.budget H (SumBody.budget P B k cost (SumHeader.words bits).length+2)+2
def passed (C T : ℕ) (q : ℚ) (bits arity : List Bool) (circuitPass : List Bool → Bool):=
  SumHeader.flag bits arity T && SumBody.passed C q (SumHeader.words bits) circuitPass

theorem sum_run {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (bits arity out native counts : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hraw : 2*bits.length+1 ≤ H)
    (hguard : SumGuard.budget bits arity T+1 ≤ H)
    (happend : SumHeader.flag bits arity T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H)
    (hread : ∀ word∈SumHeader.words bits,TermCoefficient.budget C word+1 ≤ P)
    (hword : ∀ word∈SumHeader.words bits,2*word.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ word∈SumHeader.words bits,TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel word ≤ cost)
    (hcircuit : TermLoop.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words bits) circuitPass nativeWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (machine circuit k q) (budget P H (width T (natBitLength C)) T k cost bits arity)
      ⟨(machine circuit k q).start,SumDock.heads out native counts,
        SumDock.input P H (natBitLength C) core W L T bits arity out native counts ambient⟩=some r ∧
      r.steps ≤ budget P H (width T (natBitLength C)) T k cost bits arity ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[passed C T q bits arity circuitPass] ∧
      (passed C T q bits arity circuitPass=true → ∃ after,
        r.final.heads=SumDock.heads
          (TermLoop.emitted (TermLoop.coefficientWord C) (SumHeader.words bits) out (SumHeader.words bits).length)
          (TermLoop.emitted nativeWord (SumHeader.words bits) native (SumHeader.words bits).length)
          (counts++RepairRepresentation.natWord (SumFields.count bits)) ∧
        r.final.tapes=SumStorage.data P H (natBitLength C) core W L T arity
          (TermLoop.emitted (TermLoop.coefficientWord C) (SumHeader.words bits) out (SumHeader.words bits).length)
          (TermLoop.emitted nativeWord (SumHeader.words bits) native (SumHeader.words bits).length)
          (counts++RepairRepresentation.natWord (SumFields.count bits)) after ∧
        Store (width T (natBitLength C)) zero [] after) := by
  classical
  let B:=width T (natBitLength C)
  let words:=SumHeader.words bits
  let source:=words.flatMap frame++SumHeader.tail H bits
  let nextCounts:=counts++RepairRepresentation.natWord words.length
  let nextOut:=TermLoop.emitted (TermLoop.coefficientWord C) words out words.length
  let nextNative:=TermLoop.emitted nativeWord words native words.length
  let firstFuel:=SumPrefix.budget bits arity T
  let bodyFuel:=SumBody.budget P B k cost words.length+2
  let lastFuel:=SumTail.budget H bodyFuel
  obtain ⟨reader,readRun,_readSteps,readHead,readFlag,readGood⟩:=SumDock.reader_run P H (natBitLength C)
    core W L T bits arity out native counts ambient hraw hguard happend
  cases hf:SumHeader.flag bits arity T with
  | false =>
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.reject_run SumDock.reader (tail circuit k q) 724 firstFuel
      _ reader readRun readHead (by rw [readFlag,hf])
    have hb:firstFuel+1 ≤ budget P H B T k cost bits arity:=by unfold budget;dsimp only [firstFuel];omega
    have more:=runFrom_moreFuel (machine circuit k q) _
      (budget P H B T k cost bits arity-(firstFuel+1)) _ r run
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨r,more,rs.trans hb,by rw [rh];exact readHead,?_,?_⟩
    · rw [rt,readFlag];simp only [passed,hf,Bool.false_and]
    · intro impossible;simp only [passed,hf,Bool.false_and,Bool.false_eq_true] at impossible
  | true =>
    obtain ⟨bank,readerHeads,readerTapes,b501,b502,b526,bankBound⟩:=readGood hf
    have countEq : SumFields.count bits=words.length:=(SumHeader.words_count bits).symm
    rw [countEq] at readerHeads readerTapes b526
    have hK : words.length ≤ T := by
      have hpass:SumGuard.Passes bits arity T:=of_decide_eq_true hf
      rw [←countEq];exact hpass.2.2.2
    have holes : ∀ i : Fin 528,(i.val=357 ∨ i.val=368 ∨ i.val=499) → bank i=List.replicate H false := by
      intro i hi
      have retained:=SumWork.hole_retained SumPrefix.machine firstFuel _ reader readRun i hi
      have value:=congrFun readerTapes (i.natAdd 2533)
      simp only [Fin.addCases_right] at value
      rw [←value,retained]
      change SumDock.input P H (natBitLength C) core W L T bits arity out native counts ambient (i.natAdd 2533)=_
      rw [SumDock.input,Fin.addCases_right]
      simp only [SumDock.extra,if_neg (show i.val≠1 by omega),if_neg (show i.val≠501 by omega),
        if_neg (show i.val≠502 by omega),if_neg (show i.val≠526 by omega)]
    obtain ⟨body,bodyRun,bodySteps,bodyHead,bodyFlag,bodyGood⟩:=SumWork.prepared_run circuit
      P H C T core W L circuitFuel cost k q words (SumHeader.tail H bits) out native nextCounts
      circuitPass nativeWord ambient bank hC hK hread hword hwidth hcap hbits hnative hcost hcircuit
      hstore hq hk hp hd hcheck
    obtain ⟨entered,enteredRun,_enteredSteps,enteredHeads,enteredTapes⟩:=SumWork.enter_run
      (SumDock.body circuit k q) (SumBody.budget P B k cost words.length) 0 out native nextCounts
      (SumWork.data P H (natBitLength C) core W L words.length source out native ambient bank) body bodyRun bodySteps
    have enteredGood : SumBody.passed C q words circuitPass=true → ∃ after,
        entered.final.heads=SumWork.heads (words.flatMap frame).length 1 nextOut nextNative nextCounts ∧
        entered.final.tapes=SumWork.data P H (natBitLength C) core W L words.length source nextOut nextNative after bank ∧
        Store B zero [] after := by
      intro accepted
      obtain ⟨after,ah,atapes,store⟩:=bodyGood accepted
      exact ⟨after,enteredHeads.trans ah,enteredTapes.trans atapes,store⟩
    obtain ⟨sourceBound,countBound⟩:=SumWork.header_bounds H T bits arity hraw hguard
    rw [countEq] at countBound
    have posBound : (words.flatMap frame).length ≤ H := by
      change ((words.flatMap frame)++SumHeader.tail H bits).length ≤ H at sourceBound
      rw [List.length_append] at sourceBound
      omega
    obtain ⟨last,lastRun,_lastSteps,lastHead,lastFlag,lastGood⟩:=SumTail.tail_run (worker circuit k q)
      P H (natBitLength C) B core W L words.length T bodyFuel (words.flatMap frame).length
      source arity out native nextCounts nextOut nextNative (SumBody.passed C q words circuitPass) ambient bank
      entered enteredRun (by rw [enteredHeads];exact bodyHead)
      (by rw [enteredTapes];exact bodyFlag) enteredGood posBound sourceBound countBound b501 b502 b526 bankBound holes
    have actualLast : runFrom (tail circuit k q) lastFuel
        (RecoveryCalls.restarted (tail circuit k q) reader.final.heads reader.final.tapes)=some last := by
      rw [readerHeads,readerTapes];exact lastRun
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.accept_run SumDock.reader (tail circuit k q) 724 firstFuel lastFuel
      _ reader last readRun readHead (by rw [readFlag,hf]) actualLast
    refine ⟨r,run,rs,by rw [rh];exact lastHead,?_,?_⟩
    · rw [rt,lastFlag];simp only [passed,hf,Bool.true_and];rfl
    · intro accepted
      have hb:SumBody.passed C q words circuitPass=true:=by
        simpa only [passed,hf,Bool.true_and] using accepted
      obtain ⟨after,ah,atapes,store⟩:=lastGood hb
      refine ⟨after,?_,?_,store⟩
      · rw [rh,ah,countEq]
      · rw [rt,atapes,countEq]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
