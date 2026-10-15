import Proof.CaseAnalysis.RowsIntegerLayout
import Proof.CaseAnalysis.RowsCanonicalFlag
import Proof.CaseAnalysis.WitnessInputPowerFields

/-! The actual cold input generates its capacity, traverses its canonical
list once, and allocates the native integer bank. All loop ports are aliases
of physically retained fields; the prepared loop has no free driver input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open RepairSource.VerifierDecoding CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficient : ℕ:=1000000000000000000000
noncomputable def power:=RecoveryFocus.machine powerSlots (InputPower.machine 24 coefficient 1)
noncomputable def canonical:=RecoveryFocus.machine canonSlots CanonicalTest.machine
noncomputable def bank:=RecoveryFocus.machine bankSlots CloseoutRowsIntegerBank.machine
noncomputable def first:=Composition.machine power canonical
noncomputable def prepare:=Composition.machine first bank
def prepareBudget (bits : List Bool):=InputPower.budget 24 coefficient 1 bits+1+
  CanonicalTest.budget bits+1+(2*CloseoutRowsIntegerReady.capacity bits.length+4)
noncomputable def loopInput (bits : List Bool) : Fin 221→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (220+1)=>List Bool)
    (CloseoutRowsIntegerRound.data (CloseoutRowsIntegerReady.capacity bits.length) [] []
      ((Reencode.fields bits).flatMap frame) (CloseoutRowsCanonicalFlag.flag bits))
    (fun _ : Fin 1=>CompareMachine.word (Reencode.fields bits).length)

theorem power_input (bits : List Bool) : ∀ i,input bits (powerSlots i)=InputPower.input 24 bits i:=by
  have raw (i : Fin 63) : InputPower.input 24 bits i=if i.val=0 then frame bits else []:=by
    change Fin.addCases (m:=10) (n:=53) (HierarchyAllocation.input bits)
      (fun _=>[]) i=if i.val=0 then frame bits else []
    refine Fin.addCases (m:=10) (n:=53) ?_ ?_ i
    · intro j
      rw [Fin.addCases_left]
      rfl
    · intro j
      rw [Fin.addCases_right]
      have hn:(j.natAdd 10).val≠0:=by simp only [Fin.val_natAdd];omega
      rw [if_neg hn]
  intro i
  rw [raw]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    rfl
  · have hn:powerSlots i≠221:=by
      intro h
      have hv:=congrArg Fin.val h
      rw [power_val] at hv
      split_ifs at hv <;> omega
    simp only [input,if_neg hn,if_neg hi]

theorem prepare_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun prepare (prepareBudget bits) (input bits) output ∧
      (∀ i,output (loopSlots i)=loopInput bits i) ∧
      (CloseoutRowsCanonicalFlag.flag bits=true ↔
        ∃ codes,CanonicalBinary.encodeBalancedList codes=value bits):=by
  obtain ⟨p,hp,hcap,_,_,hraw⟩:=InputPower.input_power_retained 24 coefficient 1 bits
  have hcapacity:p (60 : Fin 63)=List.replicate (CloseoutRowsIntegerReady.capacity bits.length) true:=hcap
  have hraw':p (0 : Fin 63)=frame bits:=hraw
  have h0:=hp.focus powerSlots power_injective (input bits) (power_input bits)
  obtain ⟨c,hc,hstream,hcount,hcanonical⟩:=CanonicalTest.fields_run bits
  have hflag:=(CloseoutRowsCanonicalFlag.retained bits c hc).1
  have h1:=hc.focus canonSlots canon_injective (powered bits p) (powered_canon bits p hraw')
  have hfirst:=ClockJoin.join power canonical _ _ _ _ _ h0 h1
  have hs:c 30=(Reencode.fields bits).flatMap frame:=by
    rw [hstream,←Reencode.fields_stream]
    rfl
  have hcount':c 41=CompareMachine.word (Reencode.fields bits).length:=by
    simpa only [Reencode.fields,List.length_map] using hcount
  have h2:=(CloseoutRowsIntegerBank.bank_ready (CloseoutRowsIntegerReady.capacity bits.length) []
    ((Reencode.fields bits).flatMap frame) (CloseoutRowsCanonicalFlag.flag bits)
    (CloseoutRowsIntegerReady.capacity_positive bits.length)).focus bankSlots bank_injective
      (parsed bits p c) (parsed_bank bits p c _ _ _ hcapacity hs hflag)
  obtain ⟨b,hb,bt,bh,bs⟩:=h2
  have h:=ClockJoin.join first bank _ _ _ _ _ hfirst ⟨b,hb,bt,bh,bs.le⟩
  refine ⟨_,h,?_,?_⟩
  · intro i
    refine Fin.addCases (m:=220) (n:=1) ?_ ?_ i
    · intro j
      change install bankSlots _ _ (bankSlots j)=_
      rw [install_slot _ bank_injective]
      rw [loopInput,Fin.addCases_left]
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      change install bankSlots (parsed bits p c) _ 220=CompareMachine.word (Reencode.fields bits).length
      rw [install_other _ _ _ _ (by
        intro k h
        have hv:=congrArg Fin.val h
        change k.val=220 at hv
        omega)]
      change install canonSlots _ c (canonSlots 41)=_
      rw [install_slot _ canon_injective,hcount']
  · rw [hflag] at hcanonical
    exact hcanonical

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerCold
