import Proof.CaseAnalysis.RowsSupportFamilyProjection
import Proof.CaseAnalysis.RowsSupportFamilyMode
import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun

/-! Actual cold family validation in either mode: paid workspace setup,
canonical exact-V header, every original sum and term, actual circuit
worker, coefficient guard, exact mass test and retained native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCold
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth CloseoutWitness
open CloseoutWitness.SupportDock (lift)
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def body (sym : Bool) (k : ℕ) (q : ℚ):=AppendBank.machine (e:=2) (FamilyRun.machine (FamilyMode.machine sym) k q)
def prepare:=TapeEmbedding.machine 1 FamilyPrepare.machine
def program (sym : Bool) (k : ℕ) (q : ℚ) : Σ s,Machine 3244 s:=
  ⟨_,Composition.machine prepare (body sym k q)⟩
def machine (sym : Bool) (k : ℕ) (q : ℚ) : Machine 3244 (program sym k q).1:=(program sym k q).2
def budget (P H V sumCost : ℕ) (bits : List Bool):=FamilyPrepare.budget P H+1+FamilyRun.budget V sumCost bits
def input (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94 → List Bool) (supports : List Bool):=
  lift (CloseoutWitness.FamilyCold.input P H V C T core W L bits arity ambient) supports
def heads (supports : List Bool):=lift (FamilyPrepare.heads FamilyHeads.heads) supports.length
def passed:=CloseoutWitness.FamilyCold.passed
def support (sym : Bool) (core : ℕ) (bits supports : List Bool):=
  supports++(FamilyFields.words bits).flatMap (fun field=>(SumHeader.words field).flatMap (FamilyMode.support sym core))

theorem family_run (sym : Bool) (P H V C T core W L termCost sumCost k : ℕ) (q : ℚ)
    (bits arity : List Bool) (ambient : Fin 94 → List Bool) (supports : List Bool)
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
      TermAll.budget P H C (width T (natBitLength C)) (FamilyMode.fuel P core bits.length) term ≤ termCost)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P)
    (hsum : ∀ field∈FamilyFields.words bits,FamilyRound.budget P H (width T (natBitLength C)) T k termCost field arity ≤ sumCost) :
    ∃ extra r,runFrom (machine sym k q) (budget P H V sumCost bits)
      ⟨(machine sym k q).start,heads supports,input P H V C T core W L bits arity ambient supports⟩=some r ∧
      r.steps ≤ budget P H V sumCost bits ∧ r.final.heads 724=0 ∧
      r.final.tapes 724=[passed sym V C T core W L q bits arity] ∧ extra 174=List.replicate V true ∧
      (passed sym V C T core W L q bits arity=true → ∃ after,
        r.final.heads=lift (FamilyPrepare.heads (CloseoutWitness.FamilyWork.heads
          (CloseoutWitness.FamilyLoop.entry (CloseoutWitness.FamilyMode.machine sym) P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            [] [] [] (CloseoutWitness.FamilyMode.native sym core) V after) 1)) (support sym core bits supports).length ∧
        r.final.tapes=lift (FamilyPrepare.tapes (natBitLength C) bits (CloseoutWitness.FamilyWork.tapes H V
          (CloseoutWitness.FamilyLoop.entry (CloseoutWitness.FamilyMode.machine sym) P H C T core W L k q (FamilyFields.words bits) arity [] (FamilyFields.tail H bits)
            [] [] [] (CloseoutWitness.FamilyMode.native sym core) V after) extra)) (support sym core bits supports) ∧ Store (width T (natBitLength C)) zero [] after):=by
  obtain ⟨oldFirst,oldRun,firstSteps,firstHeads,firstTapes⟩:=FamilyReady.prepare_run P H (natBitLength C)
    V T core W L bits arity [] [] [] ambient FamilyHeads.heads (by omega) hwidth hinput
    FamilyHeads.private_heads rfl
  let first:=TapeEmbedding.receipt (fun _ : Fin 1=>supports.length) (fun _=>supports) oldFirst
  have firstRun:=TapeEmbedding.run_embed FamilyPrepare.machine (fun _ : Fin 1=>supports.length)
    (fun _=>supports) _ _ oldFirst oldRun
  obtain ⟨extra,last,lastRun,lastSteps,lastHead,lastFlag,actualV,lastGood⟩:=FamilyRun.family_run
    (FamilyMode.machine sym) P H V C T core W L (FamilyMode.fuel P core bits.length) termCost sumCost k q
    bits arity [] [] [] supports (CloseoutWitness.FamilyMode.flag sym core W L)
    (CloseoutWitness.FamilyMode.native sym core) (FamilyMode.support sym core) ambient hC hinput hheader
    (by intro field hf;rw [CloseoutWitness.FamilyMode.field_width bits field hf];exact hinput) hguard happend hread
    (by intro field hf term ht;rw [CloseoutWitness.FamilyMode.term_width field term ht,CloseoutWitness.FamilyMode.field_width bits field hf];exact hterms)
    hwidth hcap hbits hnative hterm
    (by
      intro field hf
      exact FamilyMode.supplier sym P H core W L bits.length (SumHeader.words field) hH hcapacity
        (by intro term ht;rw [CloseoutWitness.FamilyMode.term_width field term ht,CloseoutWitness.FamilyMode.field_width bits field hf]))
    hstore hq hk hp hd hcheck hsum
  obtain ⟨final,lifted,fs,fh,ft⟩:=AppendBank.run_any (FamilyRun.machine (FamilyMode.machine sym) k q)
    _ _ (fun _ : Fin 2=>0) (![List.replicate (natBitLength C) true,frame bits] : Fin 2→List Bool) last lastRun
  simp only [FamilyRun.input,AppendBank.push_lift] at lifted
  have next:runFrom (body sym k q) (FamilyRun.budget V sumCost bits)
      ⟨(body sym k q).start,first.final.heads,first.final.tapes⟩=some final:=by
    change runFrom (body sym k q) _
      ⟨(body sym k q).start,lift oldFirst.final.heads supports.length,lift oldFirst.final.tapes supports⟩=some final
    rw [firstHeads,firstTapes]
    exact lifted
  obtain ⟨r,run,rs,rh,rt⟩:=joined prepare (body sym k q) (FamilyPrepare.budget P H)
    (FamilyRun.budget V sumCost bits) (heads supports)
    (input P H V C T core W L bits arity ambient supports) first final firstRun next firstSteps
    (by rw [fs];exact lastSteps)
  refine ⟨extra,r,run,rs,?_,?_,actualV,?_⟩
  · rw [rh,fh];exact lastHead
  · rw [rt,ft];exact lastFlag
  · intro accepted
    have accept:FamilyRun.passed V C T q bits arity (CloseoutWitness.FamilyMode.flag sym core W L)=true:=accepted
    obtain ⟨after,ah,atapes,store⟩:=lastGood accept
    have countEq:FamilyCount.count bits=V:=by
      have h:=accept
      rw [FamilyRun.passed,Bool.and_eq_true,FamilyCount.accepted,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.1.2
    have len:(FamilyFields.words bits).length=V:=(FamilyFields.words_count bits).trans countEq
    refine ⟨after,?_,?_,store⟩
    · rw [rh,fh,ah,FamilyWork.entry_heads _ (CloseoutWitness.FamilyMode.machine sym),AppendBank.push_lift]
      rw [←len]
      simp only [CloseoutWitness.TermLoop.emitted,List.take_length]
      rfl
    · rw [rt,ft,atapes,FamilyWork.entry_tapes _ (CloseoutWitness.FamilyMode.machine sym),AppendBank.push_lift]
      rw [←len]
      simp only [CloseoutWitness.TermLoop.emitted,List.take_length]
      rfl

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyCold
