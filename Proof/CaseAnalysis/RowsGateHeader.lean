import Proof.Hierarchy.CompetitorWitnessHeader
import Proof.Hierarchy.CompetitorRationalProducts

/-! A supported gate reuses the existing triple extractor and its four
structural classifiers. The weight field is retained without classification
as a witness mode. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots (i : Fin 122) : Fin 148:=i.castAdd 26
theorem first_injective : Function.Injective firstSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 148=>k.val) h)
noncomputable def first:=RecoveryFocus.machine firstSlots CompetitorWitnessTriple.machine
noncomputable def pair:=Composition.machine (CompetitorWitnessHeader.program 0) (CompetitorWitnessHeader.program 1)
noncomputable def three:=Composition.machine pair (CompetitorWitnessHeader.program 2)
noncomputable def classify:=Composition.machine three (CompetitorWitnessHeader.program 3)
noncomputable def prefixMachine:=Composition.machine first classify

def tests (bits : List Bool) (j : Fin 4):=CompetitorWitnessHeader.testBits bits (j.castAdd 1)
def allFour (bs : Fin 4→Bool):=((bs 0 && bs 1) && bs 2) && bs 3
def flagSlots : Fin 5→Fin 148:=![123,128,133,137,147]
def flagInput (bs : Fin 4→Bool) : Fin 5→List Bool:=![[bs 0],[bs 1],[bs 2],[bs 3],[]]
def flagOutput (bs : Fin 4→Bool) : Fin 5→List Bool:=![[bs 0],[bs 1],[bs 2],[bs 3],[allFour bs]]
def flagMachine : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q scanned=>if q.val=0 then
    some ⟨1,![none,none,none,none,some (((scanned 0 && scanned 1) && scanned 2) && scanned 3)],fun _=>.stay⟩ else none
noncomputable def finish:=RecoveryFocus.machine flagSlots flagMachine
noncomputable def machine:=Composition.machine prefixMachine finish
noncomputable def output (bits : List Bool):=
  install flagSlots (CompetitorWitnessHeader.before [] bits 4) (flagOutput (tests bits))
def codeWord (bits : List Bool) (i : Fin 3):=
  RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits (2*i.val+1))
def port : Fin 3→Fin 148:=![38,78,118]
def budget (bits : List Bool):=27000*(bits.length+1)^2

theorem install_first (bits : List Bool) :
    install firstSlots (CompetitorWitnessHeader.input [] bits) (CompetitorWitnessTriple.stage [] bits 6)=
      CompetitorWitnessHeader.start [] bits:=by
  funext i
  refine Fin.addCases (m:=122) (n:=26) ?_ ?_ i
  · intro j
    rw [CompetitorWitnessHeader.start,Fin.addCases_left]
    exact install_slot firstSlots first_injective _ _ j
  · intro j
    rw [install_other _ _ _ _ (by
      intro k h
      have hv:=congrArg Fin.val h
      change k.val=122+j.val at hv
      omega)]
    simp only [CompetitorWitnessHeader.input,CompetitorWitnessHeader.start,Fin.addCases_right]

theorem classify_ready (bits : List Bool) :
    ClockJoin.ReadyRun classify (64*bits.length+111) (CompetitorWitnessHeader.start [] bits)
      (CompetitorWitnessHeader.before [] bits 4):=by
  have part (j : Fin 4) : ClockJoin.ReadyRun (CompetitorWitnessHeader.program (j.castAdd 1))
      (16*bits.length+27) (CompetitorWitnessHeader.before [] bits j.val)
      (CompetitorWitnessHeader.before [] bits (j.val+1)):=by
    obtain ⟨r,hr,rt,rh,rs⟩:=CompetitorWitnessHeader.step_ready [] bits (j.castAdd 1)
    rw [CompetitorWitnessHeader.values_length] at hr rs
    exact ⟨r,hr,rt,rh,rs.le⟩
  have h1:=ClockJoin.join _ _ _ _ _ _ _ (part 0) (part 1)
  have h2:=ClockJoin.join _ _ _ _ _ _ _ h1 (part 2)
  have h3:=ClockJoin.join _ _ _ _ _ _ _ h2 (part 3)
  have ht:((16*bits.length+27+1+(16*bits.length+27))+1+(16*bits.length+27))+1+(16*bits.length+27)=
      64*bits.length+111:=by omega
  rw [ht] at h3
  exact h3

theorem finish_ready (bits : List Bool) :
    ClockJoin.ReadyRun finish 1 (CompetitorWitnessHeader.before [] bits 4) (output bits):=by
  have flags (j : Fin 4) :
      CompetitorWitnessHeader.before [] bits 4 (flagSlots (j.castAdd 1))=[tests bits j]:=by
    have he:flagSlots (j.castAdd 1)=CompetitorWitnessHeader.slots (j.castAdd 1)
        (CompetitorWitnessHeader.selected (j.castAdd 1)):=by fin_cases j <;> rfl
    rw [he,CompetitorWitnessHeader.before_output [] bits 4 (j.castAdd 1) j.isLt (by decide)]
    fin_cases j <;> rfl
  have blank:CompetitorWitnessHeader.before [] bits 4 147=[]:=by
    rw [CompetitorWitnessHeader.before_other _ _ _ _ (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
    change CompetitorWitnessHeader.start [] bits ((25 : Fin 26).natAdd 122)=[]
    rw [CompetitorWitnessHeader.start,Fin.addCases_right]
  have h:ReadyRun flagMachine 1 (flagInput (tests bits)) (flagOutput (tests bits)):=by
    let final : Configuration 5 2:=⟨1,fun _=>0,flagOutput (tests bits)⟩
    have hs:step flagMachine (initialConfiguration flagMachine (flagInput (tests bits)))=some final:=by
      apply congrArg some
      apply configuration_ext
      · rfl
      · rfl
      · funext i;fin_cases i <;> rfl
    obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
    exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs⟩
  obtain ⟨r,hr,rt,rh,rs⟩:=h
  exact bounded_focus flagSlots (by decide) _ _ _ ⟨r,hr,rt,rh,rs.le⟩
    (CompetitorWitnessHeader.before [] bits 4) (by
      intro i;fin_cases i
      · exact flags 0
      · exact flags 1
      · exact flags 2
      · exact flags 3
      · exact blank)

theorem header_run (bits : List Bool) :
    ClockJoin.ReadyRun machine (budget bits) (CompetitorWitnessHeader.input [] bits) (output bits) ∧
      (readTapeBit (output bits 147) 0=true ↔ CompetitorWitnessTriple.structural bits) ∧
      ∀ i,output bits (port i)=frame (codeWord bits i):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=CompetitorWitnessTriple.triple_run [] bits
  have hf:=bounded_focus firstSlots first_injective _ _ _ ⟨r,hr,rt,rh,rs⟩
    (CompetitorWitnessHeader.input [] bits) (by intro i;simp only [CompetitorWitnessHeader.input,firstSlots,Fin.addCases_left])
  rw [install_first] at hf
  have hp:=ClockJoin.join first classify _ _ _ _ _ hf (classify_ready bits)
  have h:=ClockJoin.join prefixMachine finish _ _ _ _ _ hp (finish_ready bits)
  have ht:(CompetitorWitnessTriple.budget bits+1+(64*bits.length+111))+1+1≤budget bits:=by
    have hb:bits.length+1≤(bits.length+1)^2:=Nat.le_self_pow (by decide) _
    unfold CompetitorWitnessTriple.budget budget
    omega
  refine ⟨ClockJoin.enlarge machine _ _ _ _ h ht,?_,?_⟩
  · change readTapeBit (install flagSlots _ _ (flagSlots 4)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change allFour (tests bits)=true ↔_
    simp [allFour,tests,CompetitorWitnessHeader.testBits,CompetitorWitnessTriple.structural,and_assoc]
  · intro i
    rw [output,install_other _ _ _ _ (by fin_cases i <;> decide)]
    fin_cases i
    · change CompetitorWitnessHeader.before [] bits 4 (CompetitorWitnessHeader.slots 4 0)=_
      rw [CompetitorWitnessHeader.before_unused _ _ _ _ (by decide)]
      exact CompetitorWitnessTriple.field_output [] bits 1
    · rw [CompetitorWitnessHeader.before_other _ _ _ _ (by intro j z;fin_cases j <;> fin_cases z <;> decide)]
      exact CompetitorWitnessTriple.field_output [] bits 3
    · rw [CompetitorWitnessHeader.before_other _ _ _ _ (by intro j z;fin_cases j <;> fin_cases z <;> decide)]
      exact CompetitorWitnessTriple.field_output [] bits 5

end NearCubicWires.RepairOrdinary.CloseoutRowsGateHeader
