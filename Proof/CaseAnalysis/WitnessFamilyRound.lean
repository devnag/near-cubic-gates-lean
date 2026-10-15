import Proof.CaseAnalysis.CloseoutWitnessFamilyLayout

/-! One complete original family field: the paid loader and verdict
prime feed the already-checked whole sum directly. Successful output
returns the same reusable bank and three ordered logical streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def body {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  TapeEmbedding.machine 2 (SumRound.machine circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  Composition.machine FamilyLoad.prepare (body circuit k q)
def budget (P H B T k cost : ℕ) (bits arity : List Bool):=
  FamilyLoad.budget bits+1+SumRound.budget P H B T k cost bits arity
def coefficientWord (C : ℕ) (bits : List Bool):=
  (SumHeader.words bits).flatMap (TermLoop.coefficientWord C)
def nativeWord (word : List Bool → List Bool) (bits : List Bool):=
  (SumHeader.words bits).flatMap word
def countWord (bits : List Bool):=RepairRepresentation.natWord (SumFields.count bits)

theorem round_run {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L circuitFuel cost k : ℕ) (q : ℚ)
    (bits arity pre tail out native counts : List Bool)
    (circuitPass : List Bool → Bool) (word : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hraw : 2*bits.length+1 ≤ H)
    (hguard : SumGuard.budget bits arity T+1 ≤ H)
    (happend : SumHeader.flag bits arity T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H)
    (hread : ∀ term∈SumHeader.words bits,TermCoefficient.budget C term+1 ≤ P)
    (hword : ∀ term∈SumHeader.words bits,2*term.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ term∈SumHeader.words bits,TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel term ≤ cost)
    (hcircuit : TermLoop.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words bits) circuitPass word)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P) :
    ∃ r,runFrom (machine circuit k q) (budget P H (width T (natBitLength C)) T k cost bits arity)
      ⟨(machine circuit k q).start,FamilyLoad.heads pre.length (SumDock.heads out native counts),
        FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient)
          (pre++frame bits++tail)⟩=some r ∧
      r.steps ≤ budget P H (width T (natBitLength C)) T k cost bits arity ∧
      r.final.heads 724=0 ∧ r.final.tapes 724=[SumRound.passed C T q bits arity circuitPass] ∧
      (SumRound.passed C T q bits arity circuitPass=true → ∃ after,
        r.final.heads=FamilyLoad.heads (pre.length+2*bits.length+1)
          (SumDock.heads (out++coefficientWord C bits) (native++nativeWord word bits) (counts++countWord bits)) ∧
        r.final.tapes=FamilyLoad.data H
          (SumStorage.data P H (natBitLength C) core W L T arity
            (out++coefficientWord C bits) (native++nativeWord word bits) (counts++countWord bits) after)
          (pre++frame bits++tail) ∧ Store (width T (natBitLength C)) zero [] after) := by
  let B:=width T (natBitLength C)
  let source:=pre++frame bits++tail
  let pos:=pre.length+2*bits.length+1
  obtain ⟨first,hfirst,fs,fh,ft⟩:=FamilyLoad.prepare_run H bits pre tail (SumDock.heads out native counts)
    (SumStorage.data P H (natBitLength C) core W L T arity out native counts ambient)
    rfl rfl rfl rfl hraw
  obtain ⟨base,hbase,bs,bh,bt,good⟩:=SumRound.sum_run circuit P H C T core W L circuitFuel cost k q
    bits arity out native counts circuitPass word ambient hC hraw hguard happend hread hword hwidth hcap hbits hnative
    hcost hcircuit hstore hq hk hp hd hcheck
  let last:=TapeEmbedding.receipt ![pos,0] ![source,List.replicate H false] base
  have embedded:=TapeEmbedding.run_embed (SumRound.machine circuit k q) ![pos,0] ![source,List.replicate H false]
    _ _ base hbase
  have lastRun : runFrom (body circuit k q) (SumRound.budget P H B T k cost bits arity)
      ⟨(body circuit k q).start,first.final.heads,first.final.tapes⟩=some last := by
    rw [fh,ft,FamilyLoad.loaded_input]
    exact embedded
  obtain ⟨r,run,rs,rh,rt⟩:=joined FamilyLoad.prepare (body circuit k q) (FamilyLoad.budget bits)
    (SumRound.budget P H B T k cost bits arity) _ _ first last hfirst lastRun fs bs
  refine ⟨r,run,rs,?_,?_,?_⟩
  · rw [rh];exact bh
  · rw [rt];exact bt
  · intro accepted
    obtain ⟨after,ah,atapes,store⟩:=good accepted
    refine ⟨after,?_,?_,store⟩
    · rw [rh]
      change Fin.addCases (m:=3061) (n:=2) (motive:=fun _=>ℕ) base.final.heads ![pos,0]=_
      rw [ah]
      simp only [FamilyLoad.heads,TermLoop.emitted,List.take_length,coefficientWord,nativeWord,countWord]
      rfl
    · rw [rt]
      change Fin.addCases (m:=3061) (n:=2) (motive:=fun _=>List Bool) base.final.tapes ![source,List.replicate H false]=_
      rw [atapes]
      simp only [FamilyLoad.data,TermLoop.emitted,List.take_length,coefficientWord,nativeWord,countWord]
      rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRound
