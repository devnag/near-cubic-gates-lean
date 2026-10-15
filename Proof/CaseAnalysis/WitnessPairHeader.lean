import Proof.CaseAnalysis.WitnessRationalFields
import Proof.CaseAnalysis.RowsGateHeader

/-! One tagged-pair reader serves the sum header, a term, and its rational
coefficient. The existing triple fields/classifiers suffice; the third cell
is required to be the literal empty tail. No reserialization is performed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.PairHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalBinary CompetitorRationalProducts CompetitorWitnessTriple
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def valid (bits : List Bool) : Prop:=
  field bits 0=1 ∧ field bits 2=1 ∧ field bits 4=0 ∧ node bits 6=0 ∧ field bits 5=0
def codeWord (bits : List Bool) (i : Fin 2):=RecoveryFixedUnpair.leftWord (word bits (2*i.val+1))
theorem extracted_values (bits : List Bool) (a b : ℕ)
    (h : value bits=encodeTaggedList [a,b]) : valid bits ∧ field bits 1=a ∧ field bits 3=b:=by
  simp only [valid,field_eq,node_eq,h,nodeCode,encodeTaggedList,Nat.unpair_pair]
  trivial

theorem valid_iff (bits : List Bool) : valid bits ↔
    value bits=encodeTaggedList [field bits 1,field bits 3]:=by
  constructor
  · rintro ⟨h0,h2,h4,h6,h5⟩
    change node bits 0=_
    rw [←pair_node bits 0,←pair_node bits 1,←pair_node bits 2,←pair_node bits 3,
      ←pair_node bits 4,←pair_node bits 5,h0,h2,h4,h5,h6]
    rfl
  · intro h
    exact (extracted_values bits _ _ h).1

def firstSlots (i : Fin 148) : Fin 149:=i.castAdd 1
def fifthSlots : Fin 6→Fin 149:=![118,142,143,144,145,146]
def finishSlots : Fin 6→Fin 149:=![123,128,132,137,142,148]
theorem first_injective : Function.Injective firstSlots:=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 149=>i.val) h)
def input (bits : List Bool) : Fin 149→List Bool:=
  Fin.addCases (m:=148) (n:=1) (motive:=fun _=>List Bool) (CompetitorWitnessHeader.input [] bits) (fun _=>[])
def first:=RecoveryFocus.machine firstSlots CloseoutRowsGateHeader.machine
def fifth:=RecoveryFocus.machine fifthSlots CompetitorWitnessKind.machine
def finish:=RecoveryFocus.machine finishSlots CompetitorWitnessHeader.gate
def prefixMachine:=Composition.machine first fifth
def machine:=Composition.machine prefixMachine finish
def valueWord (bits : List Bool):=RecoveryFixedUnpair.leftWord (word bits 5)
def flags (bits : List Bool) : Fin 5→Bool:=
  ![decide (field bits 0=1),decide (field bits 2=1),decide (field bits 4=0),
    decide (node bits 6=0),decide (field bits 5=0)]
def middle (bits : List Bool):=install firstSlots (input bits) (CloseoutRowsGateHeader.output bits)
def result (bits : List Bool):=CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (valueWord bits)) (CompetitorWitnessKind.flags (valueWord bits))
  (2*(valueWord bits).length+1)
def classified (bits : List Bool):=install fifthSlots (middle bits) (result bits)
def output (bits : List Bool):=install finishSlots (classified bits) (CompetitorWitnessHeader.gateOutput (flags bits))
def budget (bits : List Bool):=28000*(bits.length+1)^2

theorem middle_old (bits : List Bool) (i : Fin 148) :
    middle bits (firstSlots i)=CloseoutRowsGateHeader.output bits i:=install_slot _ first_injective _ _ _
theorem middle_new (bits : List Bool) : middle bits 148=[]:=by
  rw [middle,install_other _ _ _ _ (by
    intro j h;have hv:=congrArg Fin.val h;change j.val=148 at hv;omega)]
  change input bits ((0 : Fin 1).natAdd 148)=[]
  simp only [input,Fin.addCases_right]

theorem fifth_input (bits : List Bool) (i : Fin 6) :
    middle bits (fifthSlots i)=CompetitorWitnessKind.input (valueWord bits) i:=by
  by_cases hi:i=0
  · subst i
    exact (middle_old bits 118).trans ((CloseoutRowsGateHeader.header_run bits).2.2 2)
  · have hs:fifthSlots i=firstSlots (CompetitorWitnessHeader.slots 4 i):=by
      fin_cases i <;> first | contradiction | rfl
    rw [hs,middle_old,CloseoutRowsGateHeader.output,install_other _ _ _ _ (by
      intro j hj;fin_cases j <;> fin_cases i <;> contradiction)]
    rw [CompetitorWitnessHeader.before_unused [] bits 4 4 (by decide)]
    have hv:i.val≠0:=fun h=>hi (Fin.ext h)
    simpa only [CompetitorWitnessKind.input,hv,if_false] using
      CompetitorWitnessHeader.start_input [] bits 4 i

theorem prefix_flag (bits : List Bool) (i : Fin 4) :
    middle bits (finishSlots (i.castAdd 2))=[flags bits (i.castAdd 1)]:=by
  fin_cases i
  · change middle bits (firstSlots (CloseoutRowsGateHeader.flagSlots 0))=_
    rw [middle_old,CloseoutRowsGateHeader.output,install_slot _ (by decide)]
    rfl
  · change middle bits (firstSlots (CloseoutRowsGateHeader.flagSlots 1))=_
    rw [middle_old,CloseoutRowsGateHeader.output,install_slot _ (by decide)]
    rfl
  · change middle bits (firstSlots (CompetitorWitnessHeader.slots 2 1))=_
    rw [middle_old,CloseoutRowsGateHeader.output,install_other _ _ _ _ (by decide)]
    rw [CompetitorWitnessHeader.before_output [] bits 4 2 (by decide) (by decide)]
    rfl
  · change middle bits (firstSlots (CloseoutRowsGateHeader.flagSlots 3))=_
    rw [middle_old,CloseoutRowsGateHeader.output,install_slot _ (by decide)]
    rfl

theorem finish_input (bits : List Bool) (i : Fin 6) :
    classified bits (finishSlots i)=CompetitorWitnessHeader.gateInput (flags bits) i:=by
  fin_cases i
  · rw [classified,install_other _ _ _ _ (by decide)]
    exact prefix_flag bits 0
  · rw [classified,install_other _ _ _ _ (by decide)]
    exact prefix_flag bits 1
  · rw [classified,install_other _ _ _ _ (by decide)]
    exact prefix_flag bits 2
  · rw [classified,install_other _ _ _ _ (by decide)]
    exact prefix_flag bits 3
  · change install fifthSlots _ _ (fifthSlots 1)=_
    rw [install_slot _ (by decide)]
    rfl
  · rw [classified,install_other _ _ _ _ (by decide)]
    exact middle_new bits

theorem header_run (bits : List Bool) :
    ClockJoin.ReadyRun machine (budget bits) (input bits) (output bits) ∧
      (readTapeBit (output bits 148) 0=true ↔ valid bits) ∧
      output bits 38=frame (codeWord bits 0) ∧ output bits 78=frame (codeWord bits 1):=by
  have hfirst:=(CloseoutRowsGateHeader.header_run bits).1.focus firstSlots first_injective (input bits)
    (by intro i;simp only [input,firstSlots,Fin.addCases_left])
  obtain ⟨r,hr,rt,rh,rs⟩:=CompetitorWitnessKind.kind_ready (valueWord bits)
  have hkind:ClockJoin.ReadyRun CompetitorWitnessKind.machine (16*(valueWord bits).length+27)
      (CompetitorWitnessKind.input (valueWord bits)) (result bits):=⟨r,hr,rt,rh,rs.le⟩
  have hfifth:=hkind.focus fifthSlots (by decide) (middle bits) (fifth_input bits)
  obtain ⟨g,hg,gt,gh,gs⟩:=CompetitorWitnessHeader.gate_ready (flags bits)
  have hgate:ClockJoin.ReadyRun CompetitorWitnessHeader.gate 1 (CompetitorWitnessHeader.gateInput (flags bits))
      (CompetitorWitnessHeader.gateOutput (flags bits)):=⟨g,hg,gt,gh,gs.le⟩
  have hfinish:=hgate.focus finishSlots (by decide) (classified bits) (finish_input bits)
  have hall:=ClockJoin.join prefixMachine finish _ _ _ _ _
    (ClockJoin.join first fifth _ _ _ _ _ hfirst hfifth) hfinish
  have ht:(CloseoutRowsGateHeader.budget bits+1+(16*(valueWord bits).length+27))+1+1  ≤  budget bits:=by
    have hl:(valueWord bits).length=bits.length:=by simp [valueWord,RecoveryFixedUnpair.word_lengths,CompetitorWitnessTriple.word_length]
    have hp:bits.length+1  ≤  (bits.length+1)^2:=Nat.le_self_pow (by decide) _
    unfold CloseoutRowsGateHeader.budget budget
    rw [hl]
    omega
  refine ⟨ClockJoin.enlarge machine _ _ _ _ hall ht,?_,?_,?_⟩
  · change readTapeBit (install finishSlots _ _ (finishSlots 5)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change CompetitorWitnessHeader.allTests (flags bits)=true ↔_
    simp [CompetitorWitnessHeader.allTests,flags,valid,and_assoc]
  · rw [output,install_other _ _ _ _ (by decide),classified,install_other _ _ _ _ (by decide)]
    exact (middle_old bits 38).trans ((CloseoutRowsGateHeader.header_run bits).2.2 0)
  · rw [output,install_other _ _ _ _ (by decide),classified,install_other _ _ _ _ (by decide)]
    exact (middle_old bits 78).trans ((CloseoutRowsGateHeader.header_run bits).2.2 1)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.PairHeader
