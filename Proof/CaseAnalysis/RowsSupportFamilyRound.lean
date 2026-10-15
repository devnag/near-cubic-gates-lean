import Proof.CaseAnalysis.RowsSupportSumRound
import Proof.CaseAnalysis.CloseoutWitnessFamilyLayout

/-! One complete original family field: the paid loader and verdict
prime feed the already-checked whole sum directly. Successful output
returns the same reusable bank and three ordered logical streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open CloseoutWitness.SupportDock (lift)
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def body {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  AppendBank.machine (e:=2) (SumRound.machine circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  Composition.machine (TapeEmbedding.machine 1 FamilyLoad.prepare) (body circuit k q)
def budget (P H B T k cost : ℕ) (bits arity : List Bool):=
  FamilyLoad.budget bits+1+SumRound.budget P H B T k cost bits arity
def coefficientWord (C : ℕ) (bits : List Bool):=
  (SumHeader.words bits).flatMap (CloseoutWitness.TermLoop.coefficientWord C)
def nativeWord (word : List Bool → List Bool) (bits : List Bool):=
  (SumHeader.words bits).flatMap word
def countWord (bits : List Bool):=RepairRepresentation.natWord (SumFields.count bits)

theorem round_run {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (bits arity pre tail out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (word supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hraw : 2*bits.length+1 ≤ H)
    (hguard : SumGuard.budget bits arity T+1 ≤ H)
    (happend : SumHeader.flag bits arity T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H)
    (hread : ∀ term∈SumHeader.words bits,TermCoefficient.budget C term+1 ≤ P)
    (hword : ∀ term∈SumHeader.words bits,2*term.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ term∈SumHeader.words bits,TermAll.budget P H C (width T (natBitLength C)) circuitFuel term ≤ cost)
    (hcircuit : Term.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words bits) circuitPass word supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (machine circuit k q) (budget P H (width T (natBitLength C)) T k cost bits arity)
      ⟨(machine circuit k q).start,lift (FamilyLoad.heads pre.length (SumDock.heads out native counts)) supports.length,
        lift (FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient)
          (pre++frame bits++tail)) supports⟩=some r ∧
      r.steps ≤ budget P H (width T (natBitLength C)) T k cost bits arity ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[SumRound.passed C T q bits arity circuitPass] ∧
      (SumRound.passed C T q bits arity circuitPass=true → ∃ after,
        r.final.heads=lift (FamilyLoad.heads (pre.length+2*bits.length+1)
          (SumDock.heads (out++coefficientWord C bits) (native++nativeWord word bits) (counts++countWord bits)))
          (supports++nativeWord supportWord bits).length ∧
        r.final.tapes=lift (FamilyLoad.data H
          (SumStorage.data P H (natBitLength C) core W L T arity
            (out++coefficientWord C bits) (native++nativeWord word bits) (counts++countWord bits) after)
          (pre++frame bits++tail)) (supports++nativeWord supportWord bits) ∧ Store (width T (natBitLength C)) zero [] after) := by
  let B:=width T (natBitLength C)
  let source:=pre++frame bits++tail
  let pos:=pre.length+2*bits.length+1
  obtain ⟨oldFirst,oldRun,fs,oh,ot⟩:=FamilyLoad.prepare_run H bits pre tail (SumDock.heads out native counts)
    (SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient)
    rfl rfl rfl rfl hraw
  let first:=TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) oldFirst
  have hfirst:=TapeEmbedding.run_embed FamilyLoad.prepare (fun _ : Fin 1=>supports.length)
    (fun _=>supports) _ _ oldFirst oldRun
  obtain ⟨base,hbase,bs,bh,bt,good⟩:=SumRound.sum_run circuit P H C T core W L circuitFuel cost k q
    bits arity out native counts supports circuitPass word supportWord ambient hC hraw hguard happend
    hread hword hwidth hcap hbits hnative hcost hcircuit hstore hq hk hp hd hcheck
  obtain ⟨last,embedded,ls,lh,lt⟩:=AppendBank.run_any (SumRound.machine circuit k q) _ _
    ![pos,0] ![source,List.replicate H false] base hbase
  simp only [AppendBank.push_lift] at embedded
  have lastRun : runFrom (body circuit k q) (SumRound.budget P H B T k cost bits arity)
      ⟨(body circuit k q).start,first.final.heads,first.final.tapes⟩=some last:=by
    change runFrom (body circuit k q) _
      ⟨(body circuit k q).start,lift oldFirst.final.heads supports.length,lift oldFirst.final.tapes supports⟩=some last
    rw [oh,ot,FamilyLoad.loaded_input]
    exact embedded
  obtain ⟨r,run,rs,rh,rt⟩:=joined (TapeEmbedding.machine 1 FamilyLoad.prepare) (body circuit k q)
    (FamilyLoad.budget bits) (SumRound.budget P H B T k cost bits arity) _ _ first last hfirst lastRun fs (by rw [ls];exact bs)
  refine ⟨r,run,rs,?_,?_,?_⟩
  · rw [rh,lh];exact bh
  · rw [rt,lt];exact bt
  · intro accepted
    obtain ⟨after,ah,atapes,store⟩:=good accepted
    refine ⟨after,?_,?_,store⟩
    · rw [rh,lh,ah,AppendBank.push_lift]
      simp only [FamilyLoad.heads,CloseoutWitness.TermLoop.emitted,List.take_length,coefficientWord,nativeWord,countWord]
      rfl
    · rw [rt,lt,atapes,AppendBank.push_lift]
      simp only [FamilyLoad.data,CloseoutWitness.TermLoop.emitted,List.take_length,coefficientWord,nativeWord,countWord]
      rfl

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRound
