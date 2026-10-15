import Proof.CaseAnalysis.RowsSupportFamilyWork
import Proof.CaseAnalysis.RowsSupportFamilyLoop
import Proof.CaseAnalysis.WitnessFamilyProgram

/-! The original family code is checked once, then its actual count and
field stream drive the complete rejecting sum loop. Failed headers stop
before any sum; successful runs retain the three ordered native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRun
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open CloseoutWitness.SupportDock (lift)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def workerProgram {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3242 z:=
  ⟨_,FamilyWork.machine (FamilyRound.machine circuit k q)⟩
def worker {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Machine 3242 (workerProgram circuit k q).1:=
  (workerProgram circuit k q).2
def program {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Σ z,Machine 3242 z:=
  ⟨_,RecoveryGatedSequence.machine (TapeEmbedding.machine 1 FamilyDock.reader) (worker circuit k q) 724⟩
def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) : Machine 3242 (program circuit k q).1:=
  (program circuit k q).2

def budget (V cost : ℕ) (bits : List Bool):=FamilyCount.budget bits V+FamilyWork.budget cost V+2
def passed (V C T : ℕ) (q : ℚ) (bits arity : List Bool) (circuitPass : List Bool → Bool):=
  FamilyCount.accepted bits V && FamilyLoop.passed C T q (FamilyFields.words bits) arity circuitPass
def input (P H V C T core W L : ℕ) (bits arity out native counts supports : List Bool) (ambient : Fin 94 → List Bool):=
  lift (FamilyDock.input H V bits
    (Function.update (SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient) 724 [false])) supports

theorem family_run {s : ℕ} (circuit : Machine 1704 s) (P H V C T core W L circuitFuel termCost sumCost k : ℕ) (q : ℚ)
    (bits arity out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (word supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hinput : 2*bits.length+1 ≤ H) (hheader : FamilyCount.budget bits V+1 ≤ H)
    (hraw : ∀ field∈FamilyFields.words bits,2*field.length+1 ≤ H)
    (hguard : ∀ field∈FamilyFields.words bits,SumGuard.budget field arity T+1 ≤ H)
    (happend : ∀ field∈FamilyFields.words bits,SumHeader.flag field arity T=true → EquationHeaderAppend.budget (SumFields.count field)+1 ≤ H)
    (hread : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,TermCoefficient.budget C term+1 ≤ P)
    (hword : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,2*term.length+1 ≤ P)
    (hwidth : natBitLength C ≤ P) (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hterm : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,
      TermAll.budget P H C (width T (natBitLength C)) circuitFuel term ≤ termCost)
    (hcircuit : ∀ field∈FamilyFields.words bits,
      Term.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words field) circuitPass word supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P)
    (hsum : ∀ field∈FamilyFields.words bits,FamilyRound.budget P H (width T (natBitLength C)) T k termCost field arity ≤ sumCost) :
    ∃ extra r,runFrom (machine circuit k q) (budget V sumCost bits)
      ⟨(machine circuit k q).start,lift (FamilyDock.heads (SumDock.heads out native counts)) supports.length,
        input P H V C T core W L bits arity out native counts supports ambient⟩=some r ∧
      r.steps ≤ budget V sumCost bits ∧ r.final.heads 724=0 ∧
      r.final.tapes 724=[passed V C T q bits arity circuitPass] ∧ extra 174=List.replicate V true ∧
      (passed V C T q bits arity circuitPass=true → ∃ after,
        r.final.heads=FamilyWork.heads
          (FamilyLoop.entry circuit P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            out native counts supports word supportWord V after) 1 ∧
        r.final.tapes=FamilyWork.tapes H V
          (FamilyLoop.entry circuit P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            out native counts supports word supportWord V after) extra ∧ Store (width T (natBitLength C)) zero [] after) := by
  classical
  let words:=FamilyFields.words bits
  let B:=width T (natBitLength C)
  let ready:=SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient
  let source:=FamilyLoop.entry circuit P H C T core W L k q words arity [] (FamilyFields.tail H bits) out native counts supports word supportWord
  obtain ⟨extra,oldFirst,oldRun,_firstSteps,firstHeads,firstTapes,actualV,oldHead,oldFlag⟩:=
    FamilyDock.header_run H V bits (SumDock.heads out native counts) (Function.update ready 724 [false])
      rfl (Function.update_self _ _ _) hinput hheader
  let first:=TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) oldFirst
  have firstRun:=TapeEmbedding.run_embed FamilyDock.reader (fun _ : Fin 1=>supports.length)
    (fun _=>supports) _ _ oldFirst oldRun
  have firstHead:first.final.heads 724=0:=oldHead
  have firstFlag:first.final.tapes 724=[FamilyCount.accepted bits V]:=oldFlag
  cases hf:FamilyCount.accepted bits V with
  | false =>
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.reject_run (TapeEmbedding.machine 1 FamilyDock.reader) (worker circuit k q) 724
      (FamilyCount.budget bits V) _ first firstRun firstHead (by rw [firstFlag,hf])
    have hb:FamilyCount.budget bits V+1 ≤ budget V sumCost bits:=by unfold budget;omega
    have more:=runFrom_moreFuel (machine circuit k q) _
      (budget V sumCost bits-(FamilyCount.budget bits V+1)) _ r run
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨extra,r,more,rs.trans hb,by rw [rh];exact firstHead,?_,actualV,?_⟩
    · rw [rt,firstFlag];simp only [passed,hf,Bool.false_and]
    · intro impossible;simp only [passed,hf,Bool.false_and,Bool.false_eq_true] at impossible
  | true =>
    have countEq:FamilyCount.count bits=V:=by
      have h:=hf
      rw [FamilyCount.accepted,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.2
    have len:words.length=V:=(FamilyFields.words_count bits).trans countEq
    have unprime:Function.update (Function.update ready 724 [false]) 724 [true]=ready:=by
      funext i
      by_cases hi:i=724
      · subst i;rw [Function.update_self];rfl
      · simp only [Function.update_of_ne hi]
    have initialHeads:lift (FamilyDock.heads (SumDock.heads out native counts)) supports.length=FamilyWork.heads (source 0 ambient) 0:=by
      simp only [FamilyWork.heads,FamilyWork.core,source,FamilyLoop.entry,lift,Fin.addCases_left,CloseoutWitness.TermLoop.emitted,CloseoutWitness.TermLoop.position,List.take_zero,List.flatMap_nil,
        List.append_nil,List.nil_append,List.length_nil,Nat.add_zero]
      rfl
    have initialTapes:lift (Fin.addCases (m:=3064) (n:=177) (motive:=fun _=>List Bool)
        (FamilyDock.coreData H ready (words.flatMap frame++FamilyFields.tail H bits)
          (ZeroPadding.pad H (CompareMachine.word V))) extra) supports=FamilyWork.tapes H V (source 0 ambient) extra:=by
      simp only [FamilyWork.tapes,FamilyWork.core,source,FamilyLoop.entry,lift,Fin.addCases_left,CloseoutWitness.TermLoop.emitted,List.take_zero,List.flatMap_nil,List.append_nil,List.nil_append]
      rfl
    have complete:=FamilyLoop.family_run circuit P H C T core W L circuitFuel termCost sumCost k q
      words arity [] (FamilyFields.tail H bits) out native counts supports circuitPass word supportWord ambient hC hraw hguard happend
      hread hword hwidth hcap hbits hnative hterm hcircuit hstore hq hk hp hd hcheck hsum
    have padded:=CountedFamily.padded_run (FamilyRound.machine circuit k q) source
      (fun _ bank=>Store B zero [] bank) H sumCost words.length 724 ambient
      (FamilyLoop.passed C T q words arity circuitPass) complete
    rw [len] at padded
    obtain ⟨last,lastRun,_lastSteps,lastHead,lastFlag,lastGood⟩:=FamilyWork.work_run
      (FamilyRound.machine circuit k q) source (fun _ bank=>Store B zero [] bank) H sumCost V ambient
      (FamilyLoop.passed C T q words arity circuitPass) extra padded
    have actualLast:runFrom (worker circuit k q) (FamilyWork.budget sumCost V)
        (RecoveryCalls.restarted (worker circuit k q) first.final.heads first.final.tapes)=some last:=by
      change runFrom (worker circuit k q) (FamilyWork.budget sumCost V)
        ⟨(worker circuit k q).start,lift oldFirst.final.heads supports.length,lift oldFirst.final.tapes supports⟩=some last
      rw [firstHeads,firstTapes,hf,unprime,countEq,initialHeads,initialTapes]
      exact lastRun
    obtain ⟨r,run,rs,rh,rt⟩:=SumControl.accept_run (TapeEmbedding.machine 1 FamilyDock.reader) (worker circuit k q) 724
      (FamilyCount.budget bits V) (FamilyWork.budget sumCost V) _ first last firstRun firstHead
      (by rw [firstFlag,hf]) actualLast
    refine ⟨extra,r,run,rs,by rw [rh];exact lastHead,?_,actualV,?_⟩
    · rw [rt,lastFlag];simp only [passed,hf,Bool.true_and];rfl
    · intro accepted
      have bodyGood:FamilyLoop.passed C T q words arity circuitPass=true:=by
        simpa only [passed,hf,Bool.true_and] using accepted
      obtain ⟨after,ah,atapes,store⟩:=lastGood bodyGood
      exact ⟨after,rh.trans ah,rt.trans atapes,store⟩

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRun
