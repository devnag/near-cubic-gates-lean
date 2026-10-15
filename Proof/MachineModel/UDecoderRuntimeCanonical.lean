import Proof.MachineModel.UDecoderRuntimeEndpoint

/-! The accepted U decoder supplies the literal canonical runtime metadata.
The three capped counters retain exactly the decoder's existing zero-tail
relations; every other listed tape is an equality of actual finite tapes. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure RuntimeMetadata (N : ℕ) (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool)
    (v : OrdinaryVerifier) (word : List Bool) : Prop where
  decoded : decode N word=some v
  canonical : RepairSource.VerifierDecoding.canonical v=v
  code_eq : VerifierEncoding.code v=word
  code_bound : word.length≤Nat.log 2 N
  tapes_bound : v.tapeCount≤word.length
  states_bound : v.stateCount≤word.length
  width_bound : natBitLength v.stateCount≤word.length
  code_tape : tapes 6=frame word
  code_head : heads 6=2*word.length
  t_tape : ZeroPadding.pad (word.length+2) (tapes 50)=CapMachine.counter word.length v.tapeCount
  s_tape : ZeroPadding.pad (word.length+2) (tapes 51)=CapMachine.counter word.length v.stateCount
  c_tape : ZeroPadding.pad (word.length+2) (tapes 52)=CapMachine.counter word.length word.length
  t_head : heads 50=1
  s_head : heads 51=1
  c_head : heads 52=1
  binary_s : tapes 55=frame (binary (natBitLength v.stateCount) v.stateCount)
  binary_s_head : heads 55=0
  j_tape : tapes 58=CompareMachine.word (natBitLength v.stateCount)
  j_head : heads 58=1
  start_tape : tapes 59=frame (binary (natBitLength v.stateCount) v.machine.start.val)
  start_head : heads 59=0
  four_t : tapes 68=CompareMachine.word (4*v.tapeCount)
  four_t_head : heads 68=1

theorem decoded_canonical {N : ℕ} {word : List Bool} {v : OrdinaryVerifier}
    (hd : decode N word=some v) : RepairSource.VerifierDecoding.canonical v=v := by
  obtain ⟨hb,hc⟩ := decode_code_length hd
  have he := decode_code v N (by rw [hc]; exact hb)
  rw [hc,hd] at he
  exact (Option.some.inj he).symm

theorem code_fields_take (v : OrdinaryVerifier) :
    (codeFields v).take (natBitLength v.stateCount)=binary (natBitLength v.stateCount) v.machine.start.val := by
  have he := List.take_left (l₁:=VerifierEncoding.fixedBits (natBitLength v.stateCount) v.machine.start.val)
    (l₂:=flags v++table v)
  simpa only [codeFields,List.append_assoc,fixedBits_binary,binary_length] using he

theorem RuntimeMetadata.code_head_bound {N : ℕ} {heads : Fin 69 → ℕ} {tapes : Fin 69 → List Bool}
    {v : OrdinaryVerifier} {word : List Bool} (h : RuntimeMetadata N heads tapes v word) :
    heads 6≤2*word.length+1 := by rw [h.code_head]; omega

theorem RuntimeMetadata.counter_t_unique {N : ℕ} {heads : Fin 69 → ℕ} {tapes : Fin 69 → List Bool}
    {v : OrdinaryVerifier} {word : List Bool} (h : RuntimeMetadata N heads tapes v word)
    (c t : ℕ) (ht : ZeroPadding.pad (c+2) (tapes 50)=CapMachine.counter c t) :
    t=v.tapeCount :=
  padded_counter_unique (tapes 50) (c+2) (word.length+2) c word.length t v.tapeCount ht h.t_tape

theorem RuntimeMetadata.counter_j_unique {N : ℕ} {heads : Fin 69 → ℕ} {tapes : Fin 69 → List Bool}
    {v : OrdinaryVerifier} {word : List Bool} (h : RuntimeMetadata N heads tapes v word)
    (j : ℕ) (hj : tapes 58=CompareMachine.word j) : j=natBitLength v.stateCount := by
  have he := congrArg List.length (hj.symm.trans h.j_tape)
  simpa only [CompareMachine.word,List.length_cons,List.length_replicate,Nat.add_right_cancel_iff] using he

end NearCubicWires.RepairOrdinary.UDecoder
