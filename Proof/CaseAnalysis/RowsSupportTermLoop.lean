import Proof.CaseAnalysis.RowsSupportTermAll
import Proof.CaseAnalysis.WitnessTermLoopDriver

/-! The actual canonical term count drives the complete term controller.
The accumulator state below is only proof bookkeeping extracted from its
same receipt; no second interpreter or coefficient pass is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
open CloseoutWitness.TermLoop (emitted coefficientWord mass position emitted_succ position_succ mass_succ mass_valid)
open private iterate_invariant from Proof.CaseAnalysis.WitnessTermLoopDriver
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def entry {s : ℕ} (circuit : Machine 1704 s) (P H C core W L : ℕ)
    (words : List (List Bool)) (pre tail out native supports : List Bool) (nativeWord supportWord : List Bool → List Bool)
    (j : ℕ) (ambient : Fin 94 → List Bool) :=
  let coeffs:=emitted (coefficientWord C) words out j
  let natives:=emitted nativeWord words native j
  let retained:=emitted supportWord words supports j
  (⟨(Term.machine circuit).start,Term.lift (TermRound.heads (position words pre j) coeffs (TermEnvironment.heads natives)) retained.length,
    Term.lift (TermRound.data P (TermRead.data P (natBitLength C) [] (pre++words.flatMap frame++tail) true) ambient coeffs
      (TermEnvironment.tapes H core W L natives)) retained⟩ :
    Configuration 2533 (Fintype.card (RecoveryCalls.Control (Term.sizes s))))
def project (tapes : Fin 2533 → List Bool) (i : Fin 94) := tapes (((SumFinish.nativeSlots i).castAdd 1705).castAdd 1)
theorem project_data (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) (supports : List Bool) :
    project (Term.lift (TermRound.data P terms ambient out extra) supports)=ambient := by
  funext i
  simp only [project,Term.lift,TermRound.data,Fin.addCases_left,SumFinish.data_native]

def successor {s : ℕ} (circuit : Machine 1704 s) (P H C core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native supports : List Bool)
    (passed : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  (TermAll.accepted C (words.getD j []) (passed (words.getD j [])),
    match runFrom (Term.machine circuit) cost
      (entry circuit P H C core W L words pre tail out native supports nativeWord supportWord j ambient) with
    | none => ambient
    | some r => project r.final.tapes)
def machine {s : ℕ} (circuit : Machine 1704 s) :=
  RepeatMachine.machine (Term.machine circuit) (fun _ bits=>bits 724)
def budget (cost count : ℕ) := count*(cost+3)+3

theorem indexed_run {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L circuitFuel cost : ℕ)
    (words : List (List Bool)) (pre tail out native supports : List Bool)
    (passed : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hk : words.length ≤ T)
    (hread : ∀ bits∈words,TermCoefficient.budget C bits+1 ≤ P)
    (hraw : ∀ bits∈words,2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ bits∈words,TermAll.budget P H C (width T (natBitLength C)) circuitFuel bits ≤ cost)
    (worker : Term.CircuitSupplier circuit P H core W L circuitFuel words passed nativeWord supportWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient) :
    ∃ r,runFrom (machine circuit) (budget cost words.length)
      (RepeatMachine.cfg 0 (entry circuit P H C core W L words pre tail out native supports nativeWord supportWord 0 ambient)
        words.length 1)=some r ∧ r.steps ≤ budget cost words.length ∧
      RepeatMachine.Result (fun x=>entry circuit P H C core W L words pre tail out native supports nativeWord supportWord x.1 x.2)
        words.length (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord))
          words.length (0,ambient)) r.final ∧
      ((RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord))
          words.length (0,ambient)).1=true →
        (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord))
          words.length (0,ambient)).2.1=words.length ∧
        Store (width T (natBitLength C)) (mass C words words.length) []
          (RepeatMachine.iterate
            (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord))
            words.length (0,ambient)).2.2) ∧
      ((RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord))
          words.length (0,ambient)).1=false → r.final.heads 724=0 ∧ r.final.tapes 724=[false]) := by
  let source:=entry circuit P H C core W L words pre tail out native supports nativeWord supportWord
  let next:=successor circuit P H C core W L cost words pre tail out native supports passed nativeWord supportWord
  let Inv:=fun j bank=>Store (width T (natBitLength C)) (mass C words j) [] bank
  have supplier : ∀ j<words.length,∀ bank,Inv j bank → ∃ r,
      runFrom (Term.machine circuit) cost (source j bank)=some r ∧ r.steps ≤ cost ∧
      r.final.scanned 724=(next j bank).1 ∧
      ((next j bank).1=true → r.final.heads=(source (j+1) (next j bank).2).heads ∧
        r.final.tapes=(source (j+1) (next j bank).2).tapes ∧ Inv (j+1) (next j bank).2) ∧
      ((next j bank).1=false → r.final.heads 724=0 ∧ r.final.tapes 724=[false]) := by
    intro j hj bank hinv
    let bits:=words.getD j []
    have hmem : bits∈words := by
      dsimp only [bits]
      rw [List.getD_eq_getElem words [] hj]
      exact List.getElem_mem hj
    let fieldPre:=pre++(words.take j).flatMap frame
    let fieldTail:=(words.drop (j+1)).flatMap frame++tail
    let coeffs:=emitted (coefficientWord C) words out j
    let natives:=emitted nativeWord words native j
    let retained:=emitted supportWord words supports j
    have split : fieldPre++frame bits++fieldTail=pre++words.flatMap frame++tail := by
      rw [CloseoutRowsFamilyLoop.split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,List.append_assoc,bits]
    obtain ⟨r,hr,rs,flag,good,bad⟩ := TermAll.term_run circuit P H C (width T (natBitLength C)) core W L
      circuitFuel bits fieldPre fieldTail coeffs natives (nativeWord bits) retained (supportWord bits) (passed bits) (mass C words j) bank
      hC (hread bits hmem) (hraw bits hmem) hwidth hinv (mass_valid T C words j hk)
      (by unfold width;nlinarith) hcap hbits hnative
      (by
        intro word hw pos output ns su a terms raw driver
        have eq:word=bits:=by simpa only [List.mem_singleton] using hw
        subst word
        exact worker bits hmem pos output ns su a terms raw driver)
    have inputEq : (⟨(Term.machine circuit).start,
        Term.lift (TermRound.heads fieldPre.length coeffs (TermEnvironment.heads natives)) retained.length,
        Term.lift (TermRound.data P (TermRead.data P (natBitLength C) [] (fieldPre++frame bits++fieldTail) true) bank coeffs
          (TermEnvironment.tapes H core W L natives)) retained⟩ :
        Configuration 2533 (Fintype.card (RecoveryCalls.Control (Term.sizes s))))=source j bank := by
      rw [split]
      simp only [source,entry,fieldPre,List.length_append,position,coeffs,natives,retained]
    rw [inputEq] at hr
    have more := runFrom_moreFuel (Term.machine circuit) _
      (cost-TermAll.budget P H C (width T (natBitLength C)) circuitFuel bits) _ r hr
    rw [Nat.add_sub_of_le (hcost bits hmem)] at more
    have nextBank : (next j bank).2=project r.final.tapes := by
      simp only [next,successor,source] at more ⊢
      rw [more]
    refine ⟨r,more,rs.trans (hcost bits hmem),flag,?_,bad⟩
    intro hg
    obtain ⟨after,rh,rt,store⟩ := good hg
    have projected : (next j bank).2=after := by rw [nextBank,rt,project_data]
    rw [projected]
    refine ⟨?_,?_,?_⟩
    · rw [rh]
      simp only [source,entry]
      rw [position_succ words pre j hj]
      simp only [emitted_succ _ words _ j hj,fieldPre,List.length_append,position,coefficientWord,coeffs,natives,retained,bits]
    · rw [rt,split]
      simp only [source,entry,emitted_succ _ words _ j hj,coefficientWord,coeffs,natives,retained,bits]
    · change Store (width T (natBitLength C)) (mass C words (j+1)) [] after
      rw [mass_succ C words j hj]
      exact store
  have initial : Inv 0 ambient := by
    simpa only [Inv,mass,List.take_zero,List.map_nil,folded] using hstore
  obtain ⟨r,hr,rs,result,reject⟩ := CountedReject.counted_run (Term.machine circuit) (fun _ bits=>bits 724) source next Inv
    cost words.length 724 (by intro j hj bank hbank;rfl) supplier ambient initial
  refine ⟨r,hr,rs,result,?_,reject⟩
  intro hgood
  have h := iterate_invariant next Inv words.length (by
    intro j hj bank hinv hpass
    obtain ⟨r,_hr,_rs,_flag,good,_bad⟩ := supplier j hj bank hinv
    exact (good hpass).2.2) words.length 0 ambient initial (by omega) hgood
  simpa only [Nat.zero_add,Inv] using h

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
