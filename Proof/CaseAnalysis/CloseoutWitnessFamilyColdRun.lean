import Proof.CaseAnalysis.WitnessFamilyReady
import Proof.CaseAnalysis.WitnessFamilyHeads
import Proof.CaseAnalysis.WitnessFamilyMode

/-! Actual cold family validation in either mode: paid workspace setup,
canonical exact-V header, every original sum and term, actual circuit
worker, coefficient guard, exact mass test and retained native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def body (sym : Bool) (k : ℕ) (q : ℚ):=TapeEmbedding.machine 2 (FamilyRun.machine (FamilyMode.machine sym) k q)
def program (sym : Bool) (k : ℕ) (q : ℚ) : Σ s,Machine 3243 s:=
  ⟨_,Composition.machine FamilyPrepare.machine (body sym k q)⟩
def machine (sym : Bool) (k : ℕ) (q : ℚ) : Machine 3243 (program sym k q).1:=(program sym k q).2
def budget (P H V sumCost : ℕ) (bits : List Bool):=FamilyPrepare.budget P H+1+FamilyRun.budget V sumCost bits
def input (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94 → List Bool):=
  FamilyPrepare.tapes (natBitLength C) bits (FamilyInput.blanked
    (FamilyInput.target P H (natBitLength C) V T core W L bits arity [] [] [] ambient))
def passed (sym : Bool) (V C T core W L : ℕ) (q : ℚ) (bits arity : List Bool):=
  FamilyRun.passed V C T q bits arity (FamilyMode.flag sym core W L)

theorem family_run (sym : Bool) (P H V C T core W L termCost sumCost k : ℕ) (q : ℚ)
    (bits arity : List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hH : P+1 ≤ H) (hcapacity : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hinput : 2*bits.length+1 ≤ H) (hterms : 2*bits.length+1 ≤ P)
    (hheader : FamilyCount.budget bits V+1 ≤ H)
    (hguard : ∀ field∈FamilyFields.words bits,SumGuard.budget field arity T+1 ≤ H)
    (happend : ∀ field∈FamilyFields.words bits,SumHeader.flag field arity T=true → EquationHeaderAppend.budget (SumFields.count field)+1 ≤ H)
    (hread : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,TermCoefficient.budget C term+1 ≤ P)
    (hwidth : natBitLength C ≤ P) (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hterm : ∀ field∈FamilyFields.words bits,∀ term∈SumHeader.words field,
      TermRoundAll.budget P H C (width T (natBitLength C)) (FamilyMode.fuel P bits.length) term ≤ termCost)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P)
    (hsum : ∀ field∈FamilyFields.words bits,FamilyRound.budget P H (width T (natBitLength C)) T k termCost field arity ≤ sumCost) :
    ∃ extra r,runFrom (machine sym k q) (budget P H V sumCost bits)
      ⟨(machine sym k q).start,FamilyPrepare.heads FamilyHeads.heads,input P H V C T core W L bits arity ambient⟩=some r ∧
      r.steps ≤ budget P H V sumCost bits ∧ r.final.heads 724=0 ∧
      r.final.tapes 724=[passed sym V C T core W L q bits arity] ∧ extra 174=List.replicate V true ∧
      (passed sym V C T core W L q bits arity=true → ∃ after,
        r.final.heads=FamilyPrepare.heads (FamilyWork.heads
          (FamilyLoop.entry (FamilyMode.machine sym) P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            [] [] [] (FamilyMode.native sym core) V after) 1) ∧
        r.final.tapes=FamilyPrepare.tapes (natBitLength C) bits (FamilyWork.tapes H V
          (FamilyLoop.entry (FamilyMode.machine sym) P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            [] [] [] (FamilyMode.native sym core) V after) extra) ∧ Store (width T (natBitLength C)) zero [] after):=by
  obtain ⟨first,firstRun,firstSteps,firstHeads,firstTapes⟩:=FamilyReady.prepare_run P H (natBitLength C)
    V T core W L bits arity [] [] [] ambient FamilyHeads.heads (by omega) hwidth hinput
    FamilyHeads.private_heads rfl
  obtain ⟨extra,last,lastRun,lastSteps,lastHead,lastFlag,actualV,lastGood⟩:=FamilyRun.family_run
    (FamilyMode.machine sym) P H V C T core W L (FamilyMode.fuel P bits.length) termCost sumCost k q
    bits arity [] [] [] (FamilyMode.flag sym core W L) (FamilyMode.native sym core) ambient hC hinput hheader
    (by intro field hf;rw [FamilyMode.field_width bits field hf];exact hinput) hguard happend hread
    (by intro field hf term ht;rw [FamilyMode.term_width field term ht,FamilyMode.field_width bits field hf];exact hterms)
    hwidth hcap hbits hnative hterm
    (by
      intro field hf
      exact FamilyMode.supplier sym P H core W L bits.length (SumHeader.words field) hH hcapacity
        (by intro term ht;rw [FamilyMode.term_width field term ht,FamilyMode.field_width bits field hf]))
    hstore hq hk hp hd hcheck hsum
  have lifted:=TapeEmbedding.run_embed (FamilyRun.machine (FamilyMode.machine sym) k q) (fun _ : Fin 2=>0)
    (![List.replicate (natBitLength C) true,frame bits] : Fin 2→List Bool) _ _ last lastRun
  let final:=TapeEmbedding.receipt (fun _ : Fin 2=>0)
    (![List.replicate (natBitLength C) true,frame bits] : Fin 2→List Bool) last
  have next:runFrom (body sym k q) (FamilyRun.budget V sumCost bits)
      ⟨(body sym k q).start,first.final.heads,first.final.tapes⟩=some final:=by
    rw [firstHeads,firstTapes]
    exact lifted
  obtain ⟨r,run,rs,rh,rt⟩:=joined FamilyPrepare.machine (body sym k q) (FamilyPrepare.budget P H)
    (FamilyRun.budget V sumCost bits) (FamilyPrepare.heads FamilyHeads.heads)
    (input P H V C T core W L bits arity ambient) first final firstRun next firstSteps lastSteps
  refine ⟨extra,r,run,rs,?_,?_,actualV,?_⟩
  · rw [rh];exact lastHead
  · rw [rt];exact lastFlag
  · intro accepted
    obtain ⟨after,ah,atapes,store⟩:=lastGood accepted
    refine ⟨after,?_,?_,store⟩
    · rw [rh]
      change Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>ℕ) last.final.heads (fun _=>0)=_
      rw [ah];rfl
    · rw [rt]
      change Fin.addCases (m:=3241) (n:=2) (motive:=fun _=>List Bool) last.final.tapes
        (![List.replicate (natBitLength C) true,frame bits] : Fin 2→List Bool)=_
      rw [atapes];rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
