import Proof.MachineModel.UPreparedRuntimeNumeric

/-! The prepared139-tape U prefix refers to the same initialized snapshot,
canonical verifier and raw input decomposition. All numeric dimensions are
identified through their retained physical input counters. -/
namespace NearCubicWires.RepairOrdinary.UPrepared
open LocalBitMultitape RecoveryExecution RepairSource RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem origin_metadata_source {raw witness : List Bool} {heads : Fin 69 → ℕ}
    {tapes : Fin 69 → List Bool} (h : UDecoder.RuntimeOrigin raw witness heads tapes) :
    ∃ v word,(∃ x bound padding,raw=VerifierInputFields.source word x bound padding ∧
      UInputScalars.Guards raw x bound) ∧ UDecoder.RuntimeMetadata raw.length heads tapes v word := by
  obtain ⟨base,ha,hs,hk⟩ := h
  obtain ⟨v,word,hsource,hm⟩ := UDecoder.successful_runtime_metadata_source raw witness base hs ha
  exact ⟨v,word,hsource,hm.transport hk⟩

structure OldRuntimeFields (v : OrdinaryVerifier) (word : List Bool)
    (heads : Fin 139 → ℕ) (tapes : Fin 139 → List Bool) : Prop where
  code_tape : tapes 6=frame word
  code_head : heads 6=2*word.length
  s_tape : ZeroPadding.pad (word.length+2) (tapes 51)=CapMachine.counter word.length v.stateCount
  c_tape : ZeroPadding.pad (word.length+2) (tapes 52)=CapMachine.counter word.length word.length
  s_head : heads 51=1
  c_head : heads 52=1
  binary_s : tapes 55=frame (binary (natBitLength v.stateCount) v.stateCount)
  binary_s_head : heads 55=0
  start_tape : tapes 59=frame (binary (natBitLength v.stateCount) v.machine.start.val)
  start_head : heads 59=0
  four_t : tapes 68=CompareMachine.word (4*v.tapeCount)
  four_t_head : heads 68=1

theorem old_runtime_fields {s u : ℕ} (N : ℕ) (base : Configuration 97 u) (final : Configuration 139 s)
    (v : OrdinaryVerifier) (word : List Bool)
    (hm : UDecoder.RuntimeMetadata N (fun i => base.heads (i.castAdd 28))
      (fun i => base.tapes (i.castAdd 28)) v word)
    (hpres : ∀ i : Fin 97,i.val≠20 → i.val≠50 → i.val≠58 → i.val≠73 →
      final.tapes (i.castAdd 42)=base.tapes i ∧ final.heads (i.castAdd 42)=base.heads i) :
    OldRuntimeFields v word final.heads final.tapes := by
  have hk (i : Fin 69) (hi : UDecoder.RuntimeSlot i) (h50 : i≠50) (h58 : i≠58) :
      final.heads (i.castAdd 70)=base.heads (i.castAdd 28) ∧
      final.tapes (i.castAdd 70)=base.tapes (i.castAdd 28) := by
    have hn : i.val≠20 ∧ i.val≠50 ∧ i.val≠58 ∧ i.val≠73 := by
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp_all
    have hr := hpres (i.castAdd 28) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    have he : (i.castAdd 28).castAdd 42=i.castAdd 70 := by apply Fin.ext; rfl
    simpa only [he] using And.intro hr.2 hr.1
  have h6 := hk 6 (by decide) (by decide) (by decide)
  have h51 := hk 51 (by decide) (by decide) (by decide)
  have h52 := hk 52 (by decide) (by decide) (by decide)
  have h55 := hk 55 (by decide) (by decide) (by decide)
  have h59 := hk 59 (by decide) (by decide) (by decide)
  have h68 := hk 68 (by decide) (by decide) (by decide)
  exact ⟨h6.2.trans hm.code_tape,h6.1.trans hm.code_head,
    (congrArg (ZeroPadding.pad (word.length+2)) h51.2).trans hm.s_tape,
    (congrArg (ZeroPadding.pad (word.length+2)) h52.2).trans hm.c_tape,
    h51.1.trans hm.s_head,h52.1.trans hm.c_head,h55.2.trans hm.binary_s,h55.1.trans hm.binary_s_head,
    h59.2.trans hm.start_tape,h59.1.trans hm.start_head,h68.2.trans hm.four_t,h68.1.trans hm.four_t_head⟩

structure RuntimeFields {s : ℕ} (raw witness : List Bool) (base : Configuration 97 frontStates)
    (final : Configuration 139 s) (v : OrdinaryVerifier) (word : List Bool) (c : ℕ) : Prop where
  initialized : UInitialized.Prepared raw witness base
  inputMetadata : UDecoder.RuntimeMetadata raw.length (fun i => base.heads (i.castAdd 28))
    (fun i => base.tapes (i.castAdd 28)) v word
  source : ∃ x bound padding,raw=VerifierInputFields.source word x bound padding ∧ UInputScalars.Guards raw x bound
  cap_bound : c≤Nat.log 2 raw.length
  tapes_bound : v.tapeCount≤c
  width_bound : natBitLength v.stateCount≤c
  input_t : ZeroPadding.pad (c+2) (base.tapes 50)=CapMachine.counter c v.tapeCount
  input_j : base.tapes 58=CompareMachine.word (natBitLength v.stateCount)
  numeric : UWalkArray.Numeric (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount) c
    (ZeroPadding.config (UWalkBootstrap.capacity c) final)
  old : OldRuntimeFields v word final.heads final.tapes
  buffers : NumericBuffers (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount) final.tapes
  t_repad : ZeroPadding.pad (max (c+2) (word.length+2)) (final.tapes 50)=
    ZeroPadding.pad (max (c+2) (word.length+2)) (CapMachine.counter word.length v.tapeCount)
  generated_heads : ∀ i : Fin 139,97 ≤ i.val → i.val<135 → final.heads i=0
  array : final.tapes 136=(List.replicate v.tapeCount
    (frame (binary (ClockDyadicLedger.width raw.length) 0))).flatten
  array_heads : ∀ i : Fin 139,135 ≤ i.val → final.heads i=0

theorem prepared_runtime_fields {s : ℕ} (raw witness : List Bool) (final : Configuration 139 s)
    (hp : Prepared raw witness final) :
    ∃ base v word c,RuntimeFields raw witness base final v word c := by
  obtain ⟨base,c,t,j,hbase,_,hc,htc,hjc,hit,hij,hnum,hpres,harray,hheads⟩ := hp
  obtain ⟨v,word,hsource,hm⟩ := origin_metadata_source (UInitialized.runtime_origin raw witness base hbase)
  have het : t=v.tapeCount := hm.counter_t_unique c t hit
  have hej : j=natBitLength v.stateCount := hm.counter_j_unique j hij
  subst t j
  have hd := numeric_drivers (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount) c final hnum
  refine ⟨base,v,word,c,hbase,hm,hsource,hc,htc,hjc,hit,hij,hnum,
    old_runtime_fields raw.length base final v word hm hpres,
    numeric_buffers (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount) c final hnum,
    counter_repad (final.tapes 50) c word.length v.tapeCount hd.2.1,?_,harray,hheads⟩
  exact numeric_output_heads (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount) c final hnum

theorem RuntimeFields.drivers {s : ℕ} {raw witness : List Bool} {base : Configuration 97 frontStates}
    {final : Configuration 139 s} {v : OrdinaryVerifier} {word : List Bool} {c : ℕ}
    (h : RuntimeFields raw witness base final v word c) :
    final.tapes 20=List.replicate (ClockDyadicLedger.width raw.length) true ∧
    ZeroPadding.pad (c+2) (final.tapes 50)=CapMachine.counter c v.tapeCount ∧
    final.tapes 58=CompareMachine.word (natBitLength v.stateCount) ∧
    final.tapes 73=CompareMachine.word (ClockDyadicLedger.width raw.length) ∧
    final.heads 20=0 ∧ final.heads 50=1 ∧ final.heads 58=1 ∧ final.heads 73=1 :=
  numeric_drivers _ _ _ _ final h.numeric

end NearCubicWires.RepairOrdinary.UPrepared
