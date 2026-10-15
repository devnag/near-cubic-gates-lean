import Proof.CaseAnalysis.WitnessTermLoopData
import Proof.CaseAnalysis.WitnessTermRoundAll

/-! The actual canonical term count drives the complete term controller.
The accumulator state below is only proof bookkeeping extracted from its
same receipt; no second interpreter or coefficient pass is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def CircuitSupplier {s : ℕ} (circuit : Machine 1703 s) (P H core W L fuel : ℕ)
    (words : List (List Bool)) (passed : List Bool → Bool) (nativeWord : List Bool → List Bool) : Prop :=
  ∀ bits∈words,∀ pos out native (ambient : Fin 94 → List Bool) (terms : Fin 725 → List Bool),
    terms 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) →
    terms 720=List.replicate P true →
    ∃ eh et result,runFrom (TermRound.programs circuit 1) fuel
      (RecoveryCalls.restarted (TermRound.programs circuit 1) (TermRound.heads pos out (TermEnvironment.heads native))
        (TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native)))=some result ∧
      result.final.heads=TermRound.heads pos out eh ∧ result.final.tapes=TermRound.data P terms ambient out et ∧
      TermRound.heads pos out eh 2527=0 ∧ readTapeBit (TermRound.data P terms ambient out et 2527) 0=passed bits ∧
      (passed bits=true → eh=TermEnvironment.heads (native++nativeWord bits) ∧
        (∀ i : Fin 1703,TermCircuitReset.retained i →
          et (i.castAdd 2)=TermEnvironment.tapes H core W L (native++nativeWord bits) (i.castAdd 2)) ∧
        et 1703=List.replicate H true ∧ et 1704=List.replicate (H+1) false ∧
        (∀ i,(et ((TermCircuitReset.privateSlot i).castAdd 2)).length ≤ H))

def entry {s : ℕ} (circuit : Machine 1703 s) (P H C core W L : ℕ)
    (words : List (List Bool)) (pre tail out native : List Bool) (nativeWord : List Bool → List Bool)
    (j : ℕ) (ambient : Fin 94 → List Bool) :=
  let coeffs:=emitted (coefficientWord C) words out j
  let natives:=emitted nativeWord words native j
  (⟨(TermRound.machine circuit).start,TermRound.heads (position words pre j) coeffs (TermEnvironment.heads natives),
    TermRound.data P (TermRead.data P (natBitLength C) [] (pre++words.flatMap frame++tail) true) ambient coeffs
      (TermEnvironment.tapes H core W L natives)⟩ :
    Configuration 2532 (Fintype.card (RecoveryCalls.Control (TermRound.sizes s))))
def project (tapes : Fin 2532 → List Bool) (i : Fin 94) := tapes ((SumFinish.nativeSlots i).castAdd 1705)
theorem project_data (P : ℕ) (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (out : List Bool) (extra : Fin 1705 → List Bool) : project (TermRound.data P terms ambient out extra)=ambient := by
  funext i
  simp only [project,TermRound.data,Fin.addCases_left,SumFinish.data_native]

def successor {s : ℕ} (circuit : Machine 1703 s) (P H C core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native : List Bool)
    (passed : List Bool → Bool) (nativeWord : List Bool → List Bool) (j : ℕ) (ambient : Fin 94 → List Bool) :=
  (TermRoundAll.accepted C (words.getD j []) (passed (words.getD j [])),
    match runFrom (TermRound.machine circuit) cost
      (entry circuit P H C core W L words pre tail out native nativeWord j ambient) with
    | none => ambient
    | some r => project r.final.tapes)
def machine {s : ℕ} (circuit : Machine 1703 s) :=
  RepeatMachine.machine (TermRound.machine circuit) (fun _ bits=>bits 724)
def budget (cost count : ℕ) := count*(cost+3)+3

private theorem iterate_invariant {α : Type} (next : ℕ → α → Bool×α) (Inv : ℕ → α → Prop)
    (total : ℕ)
    (step : ∀ j<total,∀ x,Inv j x → (next j x).1=true → Inv (j+1) (next j x).2)
    (n pos : ℕ) (x : α) (hx : Inv pos x) (hbound : pos+n ≤ total)
    (hgood : (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).1=true) :
    (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).2.1=pos+n ∧
      Inv (pos+n) (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).2.2 := by
  induction n generalizing pos x with
  | zero => simpa only [RepeatMachine.iterate,Nat.add_zero] using And.intro (rfl : pos=pos) hx
  | succ n ih =>
    cases hp : (next pos x).1 with
    | false => simp only [RepeatMachine.iterate,CountedReject.advance,hp,Bool.false_eq_true,↓reduceIte] at hgood
    | true =>
      simp only [RepeatMachine.iterate,CountedReject.advance,hp,↓reduceIte] at hgood ⊢
      have hnext := step pos (by omega) x hx hp
      have h := ih (pos+1) (next pos x).2 hnext (by omega) hgood
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem indexed_run {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L circuitFuel cost : ℕ)
    (words : List (List Bool)) (pre tail out native : List Bool)
    (passed : List Bool → Bool) (nativeWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (hC : 0 < C) (hk : words.length ≤ T)
    (hread : ∀ bits∈words,TermCoefficient.budget C bits+1 ≤ P)
    (hraw : ∀ bits∈words,2*bits.length+1 ≤ P) (hwidth : natBitLength C ≤ P)
    (hcap : MassStep.budget (width T (natBitLength C))+1 ≤ P)
    (hbits : 2*natBitLength C+1 ≤ P)
    (hnative : CompetitorReusableDecision.capacity (width T (natBitLength C))+1 ≤ P)
    (hcost : ∀ bits∈words,TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel bits ≤ cost)
    (worker : CircuitSupplier circuit P H core W L circuitFuel words passed nativeWord)
    (hstore : Store (width T (natBitLength C)) zero [] ambient) :
    ∃ r,runFrom (machine circuit) (budget cost words.length)
      (RepeatMachine.cfg 0 (entry circuit P H C core W L words pre tail out native nativeWord 0 ambient)
        words.length 1)=some r ∧ r.steps ≤ budget cost words.length ∧
      RepeatMachine.Result (fun x=>entry circuit P H C core W L words pre tail out native nativeWord x.1 x.2)
        words.length (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native passed nativeWord))
          words.length (0,ambient)) r.final ∧
      ((RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native passed nativeWord))
          words.length (0,ambient)).1=true →
        (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native passed nativeWord))
          words.length (0,ambient)).2.1=words.length ∧
        Store (width T (natBitLength C)) (mass C words words.length) []
          (RepeatMachine.iterate
            (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native passed nativeWord))
            words.length (0,ambient)).2.2) ∧
      ((RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native passed nativeWord))
          words.length (0,ambient)).1=false → r.final.heads 724=0 ∧ r.final.tapes 724=[false]) := by
  let source:=entry circuit P H C core W L words pre tail out native nativeWord
  let next:=successor circuit P H C core W L cost words pre tail out native passed nativeWord
  let Inv:=fun j bank=>Store (width T (natBitLength C)) (mass C words j) [] bank
  have supplier : ∀ j<words.length,∀ bank,Inv j bank → ∃ r,
      runFrom (TermRound.machine circuit) cost (source j bank)=some r ∧ r.steps ≤ cost ∧
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
    have split : fieldPre++frame bits++fieldTail=pre++words.flatMap frame++tail := by
      rw [CloseoutRowsFamilyLoop.split_word words [] frame j hj]
      simp only [fieldPre,fieldTail,List.append_assoc,bits]
    obtain ⟨r,hr,rs,flag,good,bad⟩ := TermRoundAll.term_run circuit P H C (width T (natBitLength C)) core W L
      circuitFuel bits fieldPre fieldTail coeffs natives (nativeWord bits) (passed bits) (mass C words j) bank
      hC (hread bits hmem) (hraw bits hmem) hwidth hinv (mass_valid T C words j hk)
      (by unfold width;nlinarith) hcap hbits hnative
      (worker bits hmem _ coeffs natives bank)
    have inputEq : (⟨(TermRound.machine circuit).start,
        TermRound.heads fieldPre.length coeffs (TermEnvironment.heads natives),
        TermRound.data P (TermRead.data P (natBitLength C) [] (fieldPre++frame bits++fieldTail) true) bank coeffs
          (TermEnvironment.tapes H core W L natives)⟩ :
        Configuration 2532 (Fintype.card (RecoveryCalls.Control (TermRound.sizes s))))=source j bank := by
      rw [split]
      simp only [source,entry,fieldPre,List.length_append,position,coeffs,natives]
    rw [inputEq] at hr
    have more := runFrom_moreFuel (TermRound.machine circuit) _
      (cost-TermRoundAll.budget P H C (width T (natBitLength C)) circuitFuel bits) _ r hr
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
      simp only [emitted_succ _ words _ j hj,fieldPre,List.length_append,position,coefficientWord,coeffs,natives,bits]
    · rw [rt,split]
      simp only [source,entry,emitted_succ _ words _ j hj,coefficientWord,coeffs,natives,bits]
    · change Store (width T (natBitLength C)) (mass C words (j+1)) [] after
      rw [mass_succ C words j hj]
      exact store
  have initial : Inv 0 ambient := by
    simpa only [Inv,mass,List.take_zero,List.map_nil,folded] using hstore
  obtain ⟨r,hr,rs,result,reject⟩ := CountedReject.counted_run (TermRound.machine circuit) (fun _ bits=>bits 724) source next Inv
    cost words.length 724 (by intro j hj bank hbank;rfl) supplier ambient initial
  refine ⟨r,hr,rs,result,?_,reject⟩
  intro hgood
  have h := iterate_invariant next Inv words.length (by
    intro j hj bank hinv hpass
    obtain ⟨r,_hr,_rs,_flag,good,_bad⟩ := supplier j hj bank hinv
    exact (good hpass).2.2) words.length 0 ambient initial (by omega) hgood
  simpa only [Nat.zero_add,Inv] using h

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
