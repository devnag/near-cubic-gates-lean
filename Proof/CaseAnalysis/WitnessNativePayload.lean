import Proof.CaseAnalysis.WitnessNatNative
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The source serializer never changes its framed binary input. The node
guard reuses that retained field for binary comparisons before unary readers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePayload
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header_readonly : NoWrite MatrixNaturalHeader.machine 0:=by
  intro q bits a ha
  fin_cases q <;> simp [MatrixNaturalHeader.machine] at ha
  all_goals first | (cases ha;rfl) | (split_ifs at ha <;> cases ha <;> rfl)

theorem word_readonly : NoWrite NativeWord.machine 0:=by
  apply composition
  · apply composition
    · exact unselected NativeWord.copySlots _ _ (by decide)
    · change NoWrite (RecoveryFocus.machine NativeWord.headerSlots MatrixNaturalHeader.resetMachine)
        (NativeWord.headerSlots 0)
      exact focus _ NativeWord.header_injective _ 0 (rewind _ 0 header_readonly)
  · exact unselected NativeWord.zeroSlots _ _ (by decide)

theorem word_payload (bits : List Bool) (output : Fin 7→List Bool)
    (h : ClockJoin.ReadyRun NativeWord.machine (NativeWord.budget bits) (NativeWord.input bits) output) :
    output 0=frame bits:=by
  obtain ⟨r,hr,ht,_,_⟩:=h
  rw [←ht]
  exact run_tape _ 0 word_readonly _ _ r hr

theorem nat_payload (bits : List Bool) (output : Fin 183→List Bool)
    (h : ClockJoin.ReadyRun NatNative.machine (NatNative.budget bits) (NatNative.input bits) output) :
    output 174=frame (BitFields.payload bits):=by
  obtain ⟨base,hb,hbinary,hcount,_,_⟩:=NatCold.nat_run bits
  have hc:=bounded_focus NatNative.coldSlots NatNative.cold_injective _ _ _ hb (NatNative.input bits)
    (by intro i;simp only [NatNative.input,NatNative.coldSlots,Fin.addCases_left])
  obtain ⟨out,ho,_⟩:=NativeWord.word_run (BitFields.payload bits)
  have hsource:=word_payload _ out ho
  have hn:=bounded_focus NatNative.nativeSlots NatNative.native_injective _ _ _ ho
    (NatNative.copied bits base) (NatNative.native_input bits base hbinary hcount)
  have hall:=ClockJoin.join NatNative.cold NatNative.native _ _ _ _ _ hc hn
  have more:=ClockJoin.enlarge NatNative.machine _ (NatNative.budget bits) _ _ hall (NatNative.time_bound bits)
  obtain ⟨actual,ha,hat,_,_⟩:=more
  obtain ⟨given,hg,hgt,_,_⟩:=h
  have he:given=actual:=Option.some.inj (hg.symm.trans ha)
  rw [←hgt,he,hat]
  change install NatNative.nativeSlots (NatNative.copied bits base) out (NatNative.nativeSlots 0)=_
  rw [install_slot _ NatNative.native_injective,hsource]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePayload
