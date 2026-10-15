import Proof.CaseAnalysis.RowsSupportSumFinish
import Proof.CaseAnalysis.WitnessSumControl

/-! One complete prepared sum: the actual counted term loop rejects
immediately, or the original final mass test runs once and resets the
accumulator. Both retained record streams keep their logical cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ) :=
  RecoveryGatedSequence.machine (TermLoop.machine circuit) (ending k q) 724
def budget (P B k cost K : ℕ) := TermLoop.budget cost K+SumFinish.budget P B k+2
def passed (C : ℕ) (q : ℚ) (words : List (List Bool)) (circuitPass : List Bool → Bool) : Bool :=
  TermLoop.passed C words circuitPass && decide ((CloseoutWitness.TermLoop.mass C words words.length).value ≤ q)

theorem sum_run {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (words : List (List Bool)) (pre tail out native supports : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hK : words.length ≤ T)
    (hread : ∀ bits∈words,TermCoefficient.budget C bits+1 ≤ P)
    (hraw : ∀ bits∈words,2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ bits∈words,TermAll.budget P H C (width T (natBitLength C)) circuitFuel bits ≤ cost)
    (worker : Term.CircuitSupplier circuit P H core W L circuitFuel words circuitPass nativeWord supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (machine circuit k q) (budget P (width T (natBitLength C)) k cost words.length)
      (SumControl.start (TermLoop.machine circuit) (ending k q)
        (RepeatMachine.cfg 0 (TermLoop.entry circuit P H C core W L words pre tail out native supports nativeWord supportWord 0 ambient)
          words.length 1))=some r ∧
      r.steps ≤ budget P (width T (natBitLength C)) k cost words.length ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[passed C q words circuitPass] ∧
      (passed C q words circuitPass=true → ∃ after,
        r.final.heads=heads (CloseoutWitness.TermLoop.position words pre words.length)
          (CloseoutWitness.TermLoop.emitted (CloseoutWitness.TermLoop.coefficientWord C) words out words.length)
          (TermEnvironment.heads (CloseoutWitness.TermLoop.emitted nativeWord words native words.length))
          (CloseoutWitness.TermLoop.emitted supportWord words supports words.length) ∧
        r.final.tapes=data P words.length
          (TermRead.data P (natBitLength C) [] (pre++words.flatMap frame++tail) true) after
          (CloseoutWitness.TermLoop.emitted (CloseoutWitness.TermLoop.coefficientWord C) words out words.length)
          (TermEnvironment.tapes H core W L (CloseoutWitness.TermLoop.emitted nativeWord words native words.length))
          (CloseoutWitness.TermLoop.emitted supportWord words supports words.length) ∧
        Store (width T (natBitLength C)) zero [] after) := by
  classical
  let B:=width T (natBitLength C)
  let loopFuel:=TermLoop.budget cost words.length
  let endFuel:=SumFinish.budget P B k
  obtain ⟨loop,hr,_rs,result,positive,negative⟩ := TermLoop.indexed_run circuit P H C T core W L circuitFuel cost
    words pre tail out native supports circuitPass nativeWord supportWord ambient hC hK hread hraw hwidth hcap hbits hnative hcost worker hstore
  obtain ⟨lh,lt,good⟩ := TermLoop.decision circuit P H C T core W L cost words pre tail out native supports
    circuitPass nativeWord supportWord ambient loop.final result positive negative
  let initial:=RepeatMachine.cfg 0
    (TermLoop.entry circuit P H C core W L words pre tail out native supports nativeWord supportWord 0 ambient) words.length 1
  cases accepted : TermLoop.passed C words circuitPass with
  | false =>
    obtain ⟨r,run,rs,rh,rt⟩ := SumControl.reject_run (TermLoop.machine circuit) (ending k q) 724 loopFuel
      initial loop hr lh (by rw [lt,accepted])
    have bound : loopFuel+1 ≤ budget P B k cost words.length := by unfold budget;dsimp only [loopFuel];omega
    have more := runFrom_moreFuel (machine circuit k q) (loopFuel+1)
      (budget P B k cost words.length-(loopFuel+1)) _ r run
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨r,more,rs.trans bound,?_,?_,?_⟩
    · rw [rh];exact lh
    · rw [rt,lt];simp only [passed,accepted,Bool.false_and]
    · intro impossible;simp only [passed,accepted,Bool.false_and,Bool.false_eq_true] at impossible
  | true =>
    obtain ⟨bank,finalEq,store⟩ := good accepted
    let pos:=CloseoutWitness.TermLoop.position words pre words.length
    let coeffs:=CloseoutWitness.TermLoop.emitted (CloseoutWitness.TermLoop.coefficientWord C) words out words.length
    let natives:=CloseoutWitness.TermLoop.emitted nativeWord words native words.length
    let retained:=CloseoutWitness.TermLoop.emitted supportWord words supports words.length
    obtain ⟨after,last,hlast,lastSteps,lastHeads,lastTapes,afterStore⟩ := finish_run P B (natBitLength C) k pos
      words.length q (CloseoutWitness.TermLoop.mass C words words.length) (pre++words.flatMap frame++tail) coeffs bank
      (TermEnvironment.heads natives) (TermEnvironment.tapes H core W L natives) retained store
      (CloseoutWitness.TermLoop.mass_valid T C words words.length hK) (by unfold B width;nlinarith) hq hk hp hd hcheck
      (fun i=>(MassCapacity.store_length B _ bank store i).trans hnative)
    have sourceHeads : loop.final.heads=heads pos coeffs (TermEnvironment.heads natives) retained := by
      rw [finalEq];rfl
    have sourceTapes : loop.final.tapes=data P words.length
        (TermRead.data P (natBitLength C) [] (pre++words.flatMap frame++tail) true) bank coeffs
          (TermEnvironment.tapes H core W L natives) retained := by rw [finalEq];rfl
    have finishRun : runFrom (ending k q) endFuel
        (RecoveryCalls.restarted (ending k q) loop.final.heads loop.final.tapes)=some last := by
      rw [sourceHeads,sourceTapes];exact hlast
    obtain ⟨r,run,rs,rh,rt⟩ := SumControl.accept_run (TermLoop.machine circuit) (ending k q) 724 loopFuel endFuel
      initial loop last hr lh (by rw [lt,accepted]) finishRun
    refine ⟨r,run,rs,?_,?_,?_⟩
    · rw [rh,lastHeads];rfl
    · rw [rt,lastTapes]
      change [decide ((CloseoutWitness.TermLoop.mass C words words.length).value ≤ q)]=[passed C q words circuitPass]
      simp only [passed,accepted,Bool.true_and]
    · intro hpass
      have hm : decide ((CloseoutWitness.TermLoop.mass C words words.length).value ≤ q)=true := by
        simpa only [passed,accepted,Bool.true_and] using hpass
      refine ⟨after,rh.trans lastHeads,?_,afterStore⟩
      rw [rt,lastTapes,hm]

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumBody
