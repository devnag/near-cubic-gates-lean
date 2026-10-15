import Proof.CaseAnalysis.WitnessFamilyLoopData
import Proof.CaseAnalysis.WitnessCountedFamily

/-! The original exact-V stream drives the actual complete sum machine.
Only successful sums reach a later index; the final decision is exactly
the conjunction of the original sum decisions and all three streams
remain in source-variable order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem family_run {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L circuitFuel termCost sumCost k : ℕ) (q : ℚ)
    (words : List (List Bool)) (arity pre tail out native counts : List Bool)
    (circuitPass : List Bool → Bool) (word : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hraw : ∀ bits∈words,2*bits.length+1 ≤ H)
    (hguard : ∀ bits∈words,SumGuard.budget bits arity T+1 ≤ H)
    (happend : ∀ bits∈words,SumHeader.flag bits arity T=true → EquationHeaderAppend.budget (SumFields.count bits)+1 ≤ H)
    (hread : ∀ bits∈words,∀ term∈SumHeader.words bits,TermCoefficient.budget C term+1 ≤ P)
    (hword : ∀ bits∈words,∀ term∈SumHeader.words bits,2*term.length+1 ≤ P)
    (hwidth : natBitLength C ≤ P) (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hterm : ∀ bits∈words,∀ term∈SumHeader.words bits,
      TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel term ≤ termCost)
    (hcircuit : ∀ bits∈words,
      TermLoop.CircuitSupplier circuit P H core W L circuitFuel (SumHeader.words bits) circuitPass word)
    (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0 ≤ q) (hk : k ≤ width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q < 2^k) (hd : q.den < 2^k)
    (hcheck : MassCheck.budget (width T (natBitLength C)) k+1 ≤ P)
    (hsum : ∀ bits∈words,FamilyRound.budget P H (width T (natBitLength C)) T k termCost bits arity ≤ sumCost) :
    CountedFamily.Run (FamilyRound.machine circuit k q)
      (entry circuit P H C T core W L k q words arity pre tail out native counts word)
      (fun _ bank=>Store (width T (natBitLength C)) zero [] bank) sumCost words.length 724 ambient
      (passed C T q words arity circuitPass) := by
  let B:=width T (natBitLength C)
  let source:=entry circuit P H C T core W L k q words arity pre tail out native counts word
  let next:=successor circuit P H C T core W L k sumCost q words arity pre tail out native counts circuitPass word
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
    let coeffs:=TermLoop.emitted (FamilyRound.coefficientWord C) words out j
    let natives:=TermLoop.emitted (FamilyRound.nativeWord word) words native j
    let counters:=TermLoop.emitted FamilyRound.countWord words counts j
    have split:fieldPre++frame bits++fieldTail=pre++words.flatMap frame++tail:=by
      rw [CloseoutRowsFamilyLoop.split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,bits,List.append_assoc]
    obtain ⟨r,hr,rs,rh,rt,good⟩:=FamilyRound.round_run circuit P H C T core W L circuitFuel termCost k q
      bits arity fieldPre fieldTail coeffs natives counters circuitPass word bank hC (hraw bits mem)
      (hguard bits mem) (happend bits mem) (hread bits mem) (hword bits mem) hwidth hcap hbits hnative
      (hterm bits mem) (hcircuit bits mem) store hq hk hp hd hcheck
    have inputEq : (⟨(FamilyRound.machine circuit k q).start,FamilyLoad.heads fieldPre.length (SumDock.heads coeffs natives counters),
        FamilyLoad.data H (SumStorage.data P H (natBitLength C) core W L T arity coeffs natives counters bank)
          (fieldPre++frame bits++fieldTail)⟩ : Configuration 3063 _)=source j bank := by
      rw [split]
      simp only [source,entry,fieldPre,List.length_append,TermLoop.position,coeffs,natives,counters]
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
        rw [TermLoop.position_succ words pre j hj]
        simp only [TermLoop.emitted_succ _ words _ j hj,fieldPre,List.length_append,TermLoop.position,
          coeffs,natives,counters,bits]
      · rw [atapes,split]
        simp only [source,entry,TermLoop.emitted_succ _ words _ j hj,coeffs,natives,counters,bits]
    · intro rejected
      refine ⟨rh,?_⟩
      rw [rt]
      exact congrArg (fun b=>[b]) rejected
  have complete:=CountedFamily.complete_run (FamilyRound.machine circuit k q) source next Inv sumCost words.length 724
    (fun j=>SumRound.passed C T q (words.getD j []) arity circuitPass) (by intro j bank;rfl)
    (by intro j hj bank hb;rfl) supplier (by intro j bank;exact ⟨rfl,rfl⟩) ambient hstore
  rw [TermLoop.range_all words (fun bits=>SumRound.passed C T q bits arity circuitPass)] at complete
  exact complete

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyLoop
