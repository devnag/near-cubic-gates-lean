import Proof.CaseAnalysis.RowsSupportFamilyRound
import Proof.CaseAnalysis.WitnessCountedFamily

/-! The exact outer list addresses one sum per source variable. Its
invariant carries only the zero accumulator and the three ordered
logical streams. The successor bank is projected from the same receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open CloseoutWitness.SupportDock (lift)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def entry {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L k : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts supports : List Bool)
    (word supportWord : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  let coeffs:=CloseoutWitness.TermLoop.emitted (FamilyRound.coefficientWord C) words out j
  let natives:=CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord word) words native j
  let counters:=CloseoutWitness.TermLoop.emitted FamilyRound.countWord words counts j
  let retained:=CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord supportWord) words supports j
  (⟨(FamilyRound.machine circuit k q).start,
    lift (FamilyLoad.heads (CloseoutWitness.TermLoop.position words pre j) (SumDock.heads coeffs natives counters)) retained.length,
    lift (FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity coeffs natives counters ambient)
      (pre++words.flatMap frame++tail)) retained⟩ : Configuration 3064 _)

def project (tapes : Fin 3064 → List Bool) (i : Fin 94) :=
  tapes ((((((SumFinish.nativeSlots i).castAdd 1705).castAdd 1).castAdd 528).castAdd 2).castAdd 1)

theorem project_data (P H b core W L T : ℕ) (arity out native counts source : List Bool)
    (ambient : Fin 94 → List Bool) (supports : List Bool) :
    project (lift (FamilyLoad.data H (SumStorage.data P H b core W L T arity out native counts ambient) source) supports)=ambient := by
  funext i
  simp only [project,lift,FamilyLoad.data,Fin.addCases_left,SumStorage.data,SumDock.coreData,
    TermRound.data,SumFinish.data_native]

def successor {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L k sumCost : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (word supportWord : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  (SumRound.passed C T q (words.getD j []) arity circuitPass,
    match runFrom (FamilyRound.machine circuit k q) sumCost
      (entry circuit P H C T core W L k q words arity pre tail out native counts supports word supportWord j ambient) with
    | none=>ambient
    | some r=>project r.final.tapes)

noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  RepeatMachine.machine (FamilyRound.machine circuit k q) (fun _ bits=>bits 724)
def budget (sumCost V : ℕ):=V*(sumCost+3)+3
def passed (C T : ℕ) (q : ℚ) (words : List (List Bool)) (arity : List Bool) (circuitPass : List Bool → Bool):=
  words.all (fun bits=>SumRound.passed C T q bits arity circuitPass)

theorem successor_flags {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L k sumCost : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (word supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool) :
    (RepeatMachine.iterate
      (CountedReject.advance (successor circuit P H C T core W L k sumCost q words arity pre tail out native counts supports circuitPass word supportWord))
      words.length (0,ambient)).1=passed C T q words arity circuitPass := by
  rw [CloseoutWitness.TermLoop.iterate_flag _ (fun j=>SumRound.passed C T q (words.getD j []) arity circuitPass)
    (by intro j bank;rfl)]
  exact CloseoutWitness.TermLoop.range_all words (fun bits=>SumRound.passed C T q bits arity circuitPass)

theorem family_run {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L circuitFuel termCost sumCost k : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts supports : List Bool)
    (circuitPass : List Bool → Bool) (word supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hraw : ∀ bits∈words,2*bits.length+1 ≤ H)
    (hguard : ∀ bits∈words,SumGuard.budget bits arity T+1 ≤ H)
    (happend : ∀ bits∈words,SumHeader.flag bits arity T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H)
    (hread : ∀ bits∈words,∀ term∈SumHeader.words bits,TermCoefficient.budget C term+1 ≤ P)
    (hword : ∀ bits∈words,∀ term∈SumHeader.words bits,2*term.length+1 ≤ P)
    (hwidth : natBitLength C ≤ P) (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hterm : ∀ bits∈words,∀ term∈SumHeader.words bits,
      TermAll.budget P H C (width T (natBitLength C)) circuitFuel term ≤ termCost)
    (hcircuit : ∀ bits∈words,
      Term.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words bits) circuitPass word supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P)
    (hsum : ∀ bits∈words,FamilyRound.budget P H (width T (natBitLength C)) T k termCost bits arity ≤ sumCost) :
    CountedFamily.Run (FamilyRound.machine circuit k q)
      (entry circuit P H C T core W L k q words arity pre tail out native counts supports word supportWord)
      (fun _ bank=>Store (width T (natBitLength C)) zero [] bank) sumCost words.length 724 ambient
      (passed C T q words arity circuitPass) := by
  let B:=width T (natBitLength C)
  let source:=entry circuit P H C T core W L k q words arity pre tail out native counts supports word supportWord
  let next:=successor circuit P H C T core W L k sumCost q words arity pre tail out native counts supports circuitPass word supportWord
  let Inv:=fun (_ : ℕ) (bank : Fin 94 → List Bool)=>Store B zero [] bank
  have supplier : ∀ j<words.length,∀ bank,Inv j bank → ∃ r,
      runFrom (FamilyRound.machine circuit k q) sumCost (source j bank)=some r ∧ r.steps ≤ sumCost ∧
      r.final.scanned 724=(next j bank).1 ∧
      ((next j bank).1=true → r.final.heads=(source (j+1) (next j bank).2).heads ∧
        r.final.tapes=(source (j+1) (next j bank).2).tapes ∧ Inv (j+1) (next j bank).2) ∧
      ((next j bank).1=false → r.final.heads 724=0 ∧ r.final.tapes 724=[false]) := by
    intro j hj bank store
    let bits:=words.getD j []
    have mem:bits∈words:=by
      dsimp only [bits]
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let fieldPre:=pre++(words.take j).flatMap frame
    let fieldTail:=(words.drop (j+1)).flatMap frame++tail
    let coeffs:=CloseoutWitness.TermLoop.emitted (FamilyRound.coefficientWord C) words out j
    let natives:=CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord word) words native j
    let counters:=CloseoutWitness.TermLoop.emitted FamilyRound.countWord words counts j
    let retained:=CloseoutWitness.TermLoop.emitted (FamilyRound.nativeWord supportWord) words supports j
    have split:fieldPre++frame bits++fieldTail=pre++words.flatMap frame++tail:=by
      rw [CloseoutRowsFamilyLoop.split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,bits,List.append_assoc]
    obtain ⟨r,hr,rs,rh,rt,good⟩:=FamilyRound.round_run circuit P H C T core W L circuitFuel termCost k q
      bits arity fieldPre fieldTail coeffs natives counters retained circuitPass word supportWord bank hC (hraw bits mem)
      (hguard bits mem) (happend bits mem) (hread bits mem) (hword bits mem) hwidth hcap hbits hnative
      (hterm bits mem) (hcircuit bits mem) store hq hk hp hd hcheck
    have inputEq : (⟨(FamilyRound.machine circuit k q).start,lift (FamilyLoad.heads fieldPre.length (SumDock.heads coeffs natives counters)) retained.length,
        lift (FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity coeffs natives counters bank)
          (fieldPre++frame bits++fieldTail)) retained⟩ : Configuration 3064 _)=source j bank := by
      rw [split]
      simp only [source,entry,fieldPre,List.length_append,CloseoutWitness.TermLoop.position,coeffs,natives,counters,retained]
    rw [inputEq] at hr
    have more:=runFrom_moreFuel (FamilyRound.machine circuit k q) _
      (sumCost-FamilyRound.budget P H B T k termCost bits arity) _ r hr
    rw [Nat.add_sub_of_le (hsum bits mem)] at more
    have nextBank:(next j bank).2=project r.final.tapes:=by
      simp only [next,successor,source] at more ⊢
      rw [more]
    have flag:r.final.scanned 724=(next j bank).1:=by
      change readTapeBit (r.final.tapes 724) (r.final.heads 724)=_
      rw [rh,rt]
      rfl
    refine ⟨r,more,rs.trans (hsum bits mem),flag,?_,?_⟩
    · intro accepted
      obtain ⟨after,ah,atapes,afterStore⟩:=good accepted
      have projected:(next j bank).2=after:=by rw [nextBank,atapes,project_data]
      rw [projected]
      refine ⟨?_,?_,afterStore⟩
      · rw [ah]
        simp only [source,entry]
        rw [CloseoutWitness.TermLoop.position_succ words pre j hj]
        simp only [CloseoutWitness.TermLoop.emitted_succ _ words _ j hj,fieldPre,List.length_append,CloseoutWitness.TermLoop.position,
          coeffs,natives,counters,retained,bits]
      · rw [atapes,split]
        simp only [source,entry,CloseoutWitness.TermLoop.emitted_succ _ words _ j hj,coeffs,natives,counters,retained,bits]
    · intro rejected
      refine ⟨rh,?_⟩
      rw [rt]
      exact congrArg (fun b=>[b]) rejected
  have complete:=CountedFamily.complete_run (FamilyRound.machine circuit k q) source next Inv sumCost words.length 724
    (fun j=>SumRound.passed C T q (words.getD j []) arity circuitPass) (by intro j bank;rfl)
    (by intro j hj bank hb;rfl) supplier (by intro j bank;exact ⟨rfl,rfl⟩) ambient hstore
  rw [CloseoutWitness.TermLoop.range_all words (fun bits=>SumRound.passed C T q bits arity circuitPass)] at complete
  exact complete

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyLoop
