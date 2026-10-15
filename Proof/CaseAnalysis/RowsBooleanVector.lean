import Proof.CaseAnalysis.RowsBooleanMeaning
import Proof.CaseAnalysis.RowsIntegerFlag

/-! Reuse the same cold balanced-list/Boolean-field scan, and fold its
retained vector flag. The native support/top bitmap is its actual output. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBooleanVector
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2→Fin 178:=![172,176]
noncomputable def finish:=RecoveryFocus.machine slots CloseoutRowsIntegerRound.flagMachine
noncomputable def machine:=Composition.machine NatCold.body finish
noncomputable def finished (bank : Fin 178→List Bool) (flag : Bool):=
  install slots bank ![bank 172,[flag && readTapeBit (bank 172) 0]]

theorem finish_ready (bank : Fin 178→List Bool) (flag : Bool) (hflag : bank 176=[flag]) :
    ClockJoin.ReadyRun finish 1 bank (finished bank flag):=by
  obtain ⟨r,hr,rt,rh,rs⟩:=CloseoutRowsIntegerRound.flag_ready (bank 172) flag
  exact bounded_focus slots (by decide) _ _ _ ⟨r,hr,rt,rh,rs.le⟩ bank (by
    intro i;fin_cases i
    · rfl
    · exact hflag)

theorem vector_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (NatCold.budget bits) (NatCold.input bits) output ∧
      output 174=frame (BitFields.payload bits) ∧
      output 41=RepairSource.VerifierDecoding.CompareMachine.word (BitFields.payload bits).length ∧
      (readTapeBit (output 176) 0=true ↔ (CanonicalBinary.decodeBoolList (value bits)).isSome) ∧
      (∀ values,CanonicalBinary.decodeBoolList (value bits)=some values → output 174=frame values):=by
  obtain ⟨base,hbase,hstream,hcount,hcanonical⟩:=CanonicalTest.fields_run bits
  have hcan:=bounded_focus NatCold.canonSlots NatCold.canon_injective _ _ _ hbase (NatCold.input bits)
    (by intro i;simp only [NatCold.input,NatCold.canonSlots,Fin.addCases_left])
  have hp:=ClockJoin.join NatCold.canonical NatCold.prime _ _ _ _ _ hcan (NatCold.prime_ready bits base)
  obtain ⟨out,hout,_,hreaderCount,hbinary,_,hvector⟩:=BitFields.ready_full (Reencode.fields bits) true
  have hr:=bounded_focus NatCold.readerSlots NatCold.reader_injective _ _ _ hout (NatCold.primed bits base)
    (NatCold.reader_input bits base hstream hcount)
  let bank:=install NatCold.readerSlots (NatCold.primed bits base) out
  let flag:=(Reencode.fields bits).all BitFields.good
  have hflag:bank 176=[flag]:=by
    change install NatCold.readerSlots _ out (NatCold.readerSlots 4)=_
    rw [install_slot _ NatCold.reader_injective,hvector,Bool.true_and]
  have h172:bank 172=base 172:=by
    change install NatCold.readerSlots _ out 172=_
    rw [install_other _ _ _ _ (by decide)]
    change NatCold.copied bits base (NatCold.canonSlots 172)=_
    exact NatCold.copied_old _ _ _
  have hb:=ClockJoin.join NatCold.prefixMachine NatCold.reader _ _ _ _ _ hp hr
  have hf:=ClockJoin.join NatCold.body finish _ _ _ _ _ hb (finish_ready bank flag hflag)
  have htime:((CanonicalTest.budget bits+1+1)+1+BitFields.readyTime (Reencode.fields bits))+1+1=NatCold.time bits:=by
    unfold NatCold.time
    omega
  rw [htime] at hf
  have more:=ClockJoin.enlarge machine _ (NatCold.budget bits) _ _ hf (NatCold.time_bound bits)
  have h174:finished bank flag 174=frame (BitFields.payload bits):=by
    rw [finished,install_other _ _ _ _ (by decide)]
    change install NatCold.readerSlots _ out (NatCold.readerSlots 2)=_
    rw [install_slot _ NatCold.reader_injective]
    exact hbinary
  refine ⟨finished bank flag,more,h174,?_,?_,?_⟩
  · rw [finished,install_other _ _ _ _ (by decide)]
    change install NatCold.readerSlots _ out (NatCold.readerSlots 1)=_
    rw [install_slot _ NatCold.reader_injective]
    simpa only [BitFields.payload,List.length_map] using hreaderCount
  · change readTapeBit (install slots bank _ (slots 1)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change (flag && readTapeBit (bank 172) 0)=true ↔_
    rw [h172,←checks_iff]
    simp only [checks,Bool.and_eq_true,hcanonical,flag,and_comm]
  · intro values hv
    rw [h174,(checks_of_typed values bits (CanonicalBinary.encodeBoolList_of_decode hv).symm).2]

end NearCubicWires.RepairOrdinary.CloseoutRowsBooleanVector
