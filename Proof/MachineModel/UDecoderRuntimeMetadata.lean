import Proof.MachineModel.UDecoderRuntimeCanonical
import Proof.MachineModel.UDecoderCalls

/-! The accepted U decoder supplies the literal canonical runtime metadata.
The three capped counters retain exactly the decoder's existing zero-tail
relations; every other listed tape is an equality of actual finite tapes. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem successful_runtime_metadata_source (raw witness : List Bool)
    (final : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes)))
    (h : Successful raw witness final) (ha : Accepted raw) :
    ∃ v word,(∃ x bound padding,raw=VerifierInputFields.source word x bound padding ∧
      UInputScalars.Guards raw x bound) ∧ RuntimeMetadata raw.length final.heads final.tapes v word := by
  obtain ⟨word,x,bound,padding,base,small,he,hg,_,_,_,_,hh,ht,ho⟩ := h
  obtain ⟨v,hd⟩ := (accepted_iff raw word x bound padding he hg).mp ha
  have hv := (Whole.valid_decode_iff raw.length word).mpr ⟨v,hd⟩
  obtain ⟨t,s,fields,a,b,out,hparts,_,_,heq,hbits,hsource⟩ := ho.2 hv
  obtain ⟨hbound,hcode⟩ := decode_code_length hd
  have hp : HeaderMachine.parts word=some (v.tapeCount,v.stateCount,codeFields v) := by
    rw [←hcode]
    exact parts_code v
  have hparts' := Option.some.inj (hparts.symm.trans hp)
  have hts : t=v.tapeCount := congrArg Prod.fst hparts'
  have hss : s=v.stateCount := congrArg (fun z => z.2.1) hparts'
  have hfields : fields=codeFields v := congrArg (fun z => z.2.2) hparts'
  subst t s fields
  have hsource' : out.pre++frame out.bits=frame word :=
    hsource.trans (FrontTable.table_source word (codeFields v) v.tapeCount v.stateCount hparts).symm
  have hpos : out.pre.length=2*word.length := by
    have hl := congrArg List.length hsource'
    simp only [hbits,List.length_append,frame_length,List.length_nil] at hl
    omega
  have hsheads (i : Fin 21) : final.heads (slots i)=small.heads i := by
    rw [hh]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective]
  have hstapes (i : Fin 21) : final.tapes (slots i)=small.tapes i := by
    rw [ht]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective]
  have hhead (i : Fin 21) : final.heads (slots i)=
      (Ready.endpoint word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out).heads i := by
    exact (hsheads i).trans (congrArg (fun cfg => cfg.heads i) heq)
  have htape (i : Fin 21) : ZeroPadding.pad (Ready.inputCapacity word i) (final.tapes (slots i))=
      (Ready.endpoint word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out).tapes i := by
    rw [hstapes]
    exact congrArg (fun cfg => cfg.tapes i) heq
  have hc0 := ready_code_fields word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have ht1 := ready_t word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hsc := ready_s_c word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hbs := ready_bound word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hj := ready_j word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hstart := ready_start word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hfour := ready_four_t word (codeFields v) (Nat.log 2 raw.length) v.tapeCount v.stateCount a b out
  have hb := decode_table_bound hd
  have hjb : natBitLength v.stateCount≤v.stateCount := by
    have hs : 0<v.stateCount := Nat.zero_lt_of_lt v.machine.start.isLt
    rw [←BitWidthMachine.width_eq v.stateCount hs]
    exact ClockBinary.length_bound v.stateCount v.stateCount Nat.lt_two_pow_self
  refine ⟨v,word,⟨x,bound,padding,he,hg⟩,?_⟩
  refine ⟨hd,decoded_canonical hd,hcode,hbound,hb.1,hb.2.1,hjb.trans hb.2.1,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [show Ready.inputCapacity word 0=0 from rfl,ZeroPadding.pad_zero,
      show slots 0=(6 : Fin 69) from rfl] using
      (htape 0).trans (hc0.2.trans hsource')
  · exact (hhead 0).trans (hc0.1.trans hpos)
  · exact (htape 1).trans ht1.2
  · exact (htape 2).trans hsc.2.2.1
  · exact (htape 3).trans hsc.2.2.2
  · exact (hhead 1).trans ht1.1
  · exact (hhead 2).trans hsc.1
  · exact (hhead 3).trans hsc.2.1
  · simpa only [show Ready.inputCapacity word 7=0 from rfl,ZeroPadding.pad_zero,
      show slots 7=(55 : Fin 69) from rfl] using
      (htape 7).trans hbs.2
  · exact (hhead 7).trans hbs.1
  · simpa only [show Ready.inputCapacity word 10=0 from rfl,ZeroPadding.pad_zero,
      show slots 10=(58 : Fin 69) from rfl] using
      (htape 10).trans hj.2
  · exact (hhead 10).trans hj.1
  · simpa only [show Ready.inputCapacity word 11=0 from rfl,ZeroPadding.pad_zero,code_fields_take,
      show slots 11=(59 : Fin 69) from rfl] using
      (htape 11).trans hstart.2
  · exact (hhead 11).trans hstart.1
  · simpa only [show Ready.inputCapacity word 20=0 from rfl,ZeroPadding.pad_zero,
      show slots 20=(68 : Fin 69) from rfl] using
      (htape 20).trans hfour.2
  · exact (hhead 20).trans hfour.1

theorem successful_runtime_metadata (raw witness : List Bool)
    (final : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes)))
    (h : Successful raw witness final) (ha : Accepted raw) :
    ∃ v word,RuntimeMetadata raw.length final.heads final.tapes v word := by
  obtain ⟨v,word,_,hm⟩ := successful_runtime_metadata_source raw witness final h ha
  exact ⟨v,word,hm⟩

end NearCubicWires.RepairOrdinary.UDecoder
