import Proof.CaseAnalysis.WitnessPairHeader
import Proof.CaseAnalysis.WitnessRationalDecision
import Proof.MachineModel.UWalkArithmetic

/-! Each term's coefficient is validated once, with both original length
guards before gcd. Its same circuit payload and checked binary coefficient
remain available to the circuit worker and the mass accumulator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCoefficient
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def printSlots : Fin 2→Fin 720:=![0,718]
def headerSlots (i : Fin 149) : Fin 720:=i.castAdd 571
def rationalSlots (i : Fin 568) : Fin 720:=
  ⟨if i.val=1 then 38 else if i.val=539 then 149 else 150+i.val,by split_ifs <;> omega⟩
def finishSlots : Fin 3→Fin 720:=![148,714,719]
def finishMachine : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ bits=>some ⟨1,![none,none,some (bits 0 && bits 1)],fun _=>.stay⟩
def print:=RecoveryFocus.machine printSlots (HierarchyFixedWord.machine [false])
def header:=RecoveryFocus.machine headerSlots PairHeader.machine
def coefficient:=RecoveryFocus.machine rationalSlots RationalDecision.machine
def finish:=RecoveryFocus.machine finishSlots finishMachine
def first:=Composition.machine print header
def second:=Composition.machine first coefficient
def machine:=Composition.machine second finish
def input (b : ℕ) (bits : List Bool) (i : Fin 720):=
  if i.val=1 then frame bits else if i.val=149 then List.replicate b true else []
def coefficientCode (bits : List Bool):=PairHeader.codeWord bits 0
def circuitCode (bits : List Bool):=PairHeader.codeWord bits 1
def budget (C : ℕ) (bits : List Bool):=4+1+PairHeader.budget bits+1+
  RationalDecision.budget C (coefficientCode bits)+1+1

theorem finish_ready (left right : List Bool) : ClockJoin.ReadyRun finishMachine 1
    ![left,right,[]] ![left,right,[readTapeBit left 0 && readTapeBit right 0]]:=by
  have hs:step finishMachine (initialConfiguration finishMachine ![left,right,[]])=
      some ⟨1,fun _=>0,![left,right,[readTapeBit left 0 && readTapeBit right 0]]⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],ht.le⟩
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 720=>k.val) h)
theorem rational_injective : Function.Injective rationalSlots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 720=>k.val) h
  dsimp only [rationalSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem rational_outside (i : Fin 720)
    (hi : i.val≠38 ∧ i.val≠149 ∧ (i.val<150 ∨ 718 ≤ i.val)) : ∀ j,rationalSlots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 720=>k.val) h
  have hj:=j.isLt
  dsimp only [rationalSlots] at hv
  split_ifs at hv <;> omega

theorem coefficient_run (C : ℕ) (bits : List Bool) (hC : 0<C) : ∃ output,
    ClockJoin.ReadyRun machine (budget C bits) (input (natBitLength C) bits) output ∧
      output 78=frame (circuitCode bits) ∧
      (readTapeBit (output 719) 0=true ↔ PairHeader.valid bits ∧
        ∃ q,decodeCanonicalRational (value (coefficientCode bits))=some q ∧
          natBitLength q.num.natAbs ≤ natBitLength C ∧ natBitLength q.den ≤ natBitLength C) ∧
      (readTapeBit (output 719) 0=true→
        output 690=frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.numerator (coefficientCode bits)))) ∧
        output 693=frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.denominator (coefficientCode bits))))) ∧
      output 316=frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord (coefficientCode bits))):=by
  have hp:=(UWalkNumbers.fixed_ready [false]).focus printSlots (by decide)
    (input (natBitLength C) bits) (by intro i;fin_cases i <;> rfl)
  let printed:=install printSlots (input (natBitLength C) bits) ![[false],[false]]
  have p0:printed 0=[false]:=install_slot printSlots (by decide) _ _ 0
  have pkeep (i : Fin 720) (hi : i≠0 ∧ i≠718) : printed i=input (natBitLength C) bits i:=by
    apply install_other
    intro j;fin_cases j
    · exact Ne.symm hi.1
    · exact Ne.symm hi.2
  obtain ⟨hh,hv,hcoef,hcirc⟩:=PairHeader.header_run bits
  have hhf:=hh.focus headerSlots header_injective printed (by
    refine Fin.addCases (m:=148) (n:=1) ?_ ?_
    · intro i
      rw [PairHeader.input,Fin.addCases_left,CompetitorWitnessHeader.input_eq]
      by_cases h0:i.val=0
      · have he:i=0:=Fin.ext h0
        subst i;exact p0
      · rw [pkeep _ ⟨by
          intro h;have he:=congrArg Fin.val h;exact h0 he,by
          intro h;have he:=congrArg Fin.val h;change i.val=718 at he;omega⟩]
        simp only [headerSlots,Fin.val_castAdd,input,if_neg h0,if_neg (show i.val≠149 by omega)]
    · intro i;fin_cases i
      rw [pkeep _ ⟨by decide,by decide⟩]
      rfl)
  let hbank:=install headerSlots printed (PairHeader.output bits)
  have hold (i : Fin 149) : hbank (headerSlots i)=PairHeader.output bits i:=
    install_slot _ header_injective _ _ _
  have hfresh (i : Fin 720) (hi : 149 ≤ i.val) : hbank i=printed i:=by
    apply install_other
    intro j h
    have hv:=congrArg (fun k : Fin 720=>k.val) h
    change j.val=i.val at hv
    omega
  obtain ⟨r,hr,rv,rb,rs⟩:=RationalDecision.decision_run C (coefficientCode bits) hC
  have hrf:=hr.focus rationalSlots rational_injective hbank (by
    intro i
    by_cases h1:i.val=1
    · have he:i=1:=Fin.ext h1
      subst i
      exact (hold 38).trans hcoef
    by_cases hb:i.val=539
    · have he:i=539:=Fin.ext hb
      subst i
      rw [hfresh _ (by decide),pkeep _ ⟨by decide,by decide⟩]
      rfl
    rw [RationalDecision.input,if_neg hb,if_neg h1,
      hfresh _ (by simp only [rationalSlots,if_neg h1,if_neg hb];omega),
      pkeep _ ⟨by apply Fin.ne_of_val_ne;simp only [rationalSlots,if_neg h1,if_neg hb];omega,
        by apply Fin.ne_of_val_ne;simp only [rationalSlots,if_neg h1,if_neg hb];omega⟩]
    simp only [input,rationalSlots,if_neg h1,if_neg hb,
      if_neg (show 150+i.val≠1 by omega),if_neg (show 150+i.val≠149 by omega)])
  let bank:=install rationalSlots hbank r
  have rkeep (i : Fin 720) (hi : i.val≠38 ∧ i.val≠149 ∧ (i.val<150 ∨ 718 ≤ i.val)) :
      bank i=hbank i:=install_other _ _ _ _ (rational_outside i hi)
  have bh:bank 148=PairHeader.output bits 148:=by
    rw [rkeep _ ⟨by decide,by decide,Or.inl (by decide)⟩]
    exact hold 148
  have br:bank 714=r 564:=install_slot rationalSlots rational_injective _ _ 564
  have bf:bank 719=[]:=by
    rw [rkeep _ ⟨by decide,by decide,Or.inr (by decide)⟩,hfresh _ (by decide),
      pkeep _ ⟨by decide,by decide⟩]
    rfl
  have hf:=(finish_ready (PairHeader.output bits 148) (r 564)).focus finishSlots (by decide) bank (by
    intro i;fin_cases i <;> assumption)
  let final:=install finishSlots bank
    ![PairHeader.output bits 148,r 564,[readTapeBit (PairHeader.output bits 148) 0 && readTapeBit (r 564) 0]]
  have flag:readTapeBit (final 719) 0=
      (readTapeBit (PairHeader.output bits 148) 0 && readTapeBit (r 564) 0):=by
    change readTapeBit (install finishSlots _ _ (finishSlots 2)) 0=_
    rw [install_slot _ (by decide)]
    rfl
  have retain (i : Fin 568) (hi : ∀ j,finishSlots j≠rationalSlots i) : final (rationalSlots i)=r i:=by
    rw [show final=install finishSlots _ _ by rfl,install_other _ _ _ _ hi]
    exact install_slot rationalSlots rational_injective _ _ _
  refine ⟨final,ClockJoin.join second finish _ _ _ _ _
    (ClockJoin.join first coefficient _ _ _ _ _
      (ClockJoin.join print header _ _ _ _ _ hp hhf) hrf) hf,?_,?_,?_,?_⟩
  · rw [show final=install finishSlots _ _ by rfl,install_other _ _ _ _ (by decide),
      rkeep _ ⟨by decide,by decide,Or.inl (by decide)⟩]
    exact (hold 78).trans hcirc
  · rw [flag,Bool.and_eq_true,hv,rv]
  · intro h
    rw [flag,Bool.and_eq_true] at h
    have hrat:readTapeBit (r 564) 0=true:=h.2
    obtain ⟨hn,hd⟩:=rb hrat
    exact ⟨(retain 540 (by decide)).trans hn,(retain 543 (by decide)).trans hd⟩
  · exact (retain 166 (by decide)).trans rs

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCoefficient
