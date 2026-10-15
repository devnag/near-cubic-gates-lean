import Proof.MachineModel.UTransitionFocus
import Proof.MachineModel.UPreparedRuntimeFields

/-! Match the exact executed139-tape endpoint, with18 fresh blank tapes,
to the canonical transition walk. No prepared data is supplied externally. -/
namespace NearCubicWires.RepairOrdinary.UTransition
open LocalBitMultitape RecoveryExecution SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def store (raw witness : List Bool) (v : OrdinaryVerifier) (word x choices : List Bool) (m : ℕ) :=
  TransitionWalk.initialStore raw.length v (2*word.length) (frame witness)
    (2*(ClockDyadicLedger.width raw.length+choices.length)) x choices m

def physicalCapacity (c len w C : ℕ) (i : Fin 157) : ℕ :=
  if i.val=50 then max (c+2) (len+2)
  else if i.val=51 ∨ i.val=52 then len+2
  else if i.val=91 then 2*w
  else if i.val=136 then C
  else if i.val=139 ∨ i.val=140 ∨ i.val=141 ∨ i.val=144 ∨ i.val=150 ∨
    i.val=151 ∨ i.val=152 ∨ i.val=153 ∨ i.val=155 ∨ i.val=156 then 1
  else 0
def logicalCapacity (c len : ℕ) (i : Fin 42) : ℕ := if i.val=1 then max (c+2) (len+2) else 0

theorem matched_heads {s : ℕ} (raw witness : List Bool)
    (base : Configuration 97 UPrepared.frontStates) (final : Configuration 139 s)
    (v : OrdinaryVerifier) (word x choices : List Bool) (c m : ℕ)
    (hm : UPrepared.RuntimeFields raw witness base final v word c)
    (hscan : final.heads 1=2*(ClockDyadicLedger.width raw.length+choices.length))
    (hcount : final.heads 74=0)
    (he : UInitialized.EventFields (ClockDyadicLedger.width raw.length) x choices
      (fun i => final.heads (i.castAdd 42)) (fun i => final.tapes (i.castAdd 42))) :
    ∀ k,(extended final).heads (slots k)=
      (TransitionWalk.cfg TransitionWalk.machine.start (store raw witness v word x choices m)).heads k := by
  obtain ⟨_,_,hout,h91,h21,h92⟩ := he
  obtain ⟨_,_,_,_,_,h50,h58,_⟩ := hm.drivers
  have hgen (i : Fin 139) (hi : 97 ≤ i.val) : final.heads i=0 := by
    by_cases hj : i.val<135
    · exact hm.generated_heads i hi hj
    · exact hm.array_heads i (by omega)
  intro k
  fin_cases k
  · exact hm.old.code_head
  · exact h50
  · exact hm.old.s_head
  · exact hm.old.c_head
  · exact hm.old.binary_s_head
  · exact h58
  · exact hm.old.start_head
  · exact hscan
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hgen 112 (by decide)
  · exact hm.old.four_t_head
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hgen 119 (by decide)
  · exact hgen 132 (by decide)
  · rfl
  · rfl
  · exact hgen 113 (by decide)
  · exact hgen 114 (by decide)
  · exact h91
  · exact h21
  · exact h92.trans (congrArg List.length hout)
  · exact hgen 123 (by decide)
  · exact hgen 136 (by decide)
  · exact hgen 115 (by decide)
  · exact hgen 116 (by decide)
  · exact hgen 111 (by decide)
  · exact hcount
  · exact hgen 127 (by decide)
  · rfl

theorem matched_tapes {s : ℕ} (raw witness : List Bool)
    (base : Configuration 97 UPrepared.frontStates) (final : Configuration 139 s)
    (v : OrdinaryVerifier) (word x choices : List Bool) (c m : ℕ)
    (hm : UPrepared.RuntimeFields raw witness base final v word c)
    (hscan : final.tapes 1=frame witness)
    (hcount : final.tapes 74=frame (binary (ClockDyadicLedger.width raw.length) m))
    (he : UInitialized.EventFields (ClockDyadicLedger.width raw.length) x choices
      (fun i => final.heads (i.castAdd 42)) (fun i => final.tapes (i.castAdd 42))) :
    ∀ k,ZeroPadding.pad
      (physicalCapacity c word.length (ClockDyadicLedger.width raw.length)
        (UWalkCapacity.amount (ClockDyadicLedger.width raw.length) v.tapeCount (natBitLength v.stateCount)) (slots k))
      ((extended final).tapes (slots k))=
    ZeroPadding.pad (logicalCapacity c word.length k)
      ((TransitionWalk.cfg TransitionWalk.machine.start (store raw witness v word x choices m)).tapes k) := by
  obtain ⟨hserial,hI,hout,_,_,_⟩ := he
  have hj := hm.drivers.2.2.1
  intro k
  fin_cases k
  · change ZeroPadding.pad 0 (final.tapes 6)=ZeroPadding.pad 0 (frame (VerifierEncoding.code v))
    simpa only [ZeroPadding.pad_zero,hm.inputMetadata.code_eq] using hm.old.code_tape
  · change ZeroPadding.pad (max (c+2) (word.length+2)) (final.tapes 50)=
      ZeroPadding.pad (max (c+2) (word.length+2)) (CapMachine.counter (VerifierEncoding.code v).length v.tapeCount)
    simpa only [hm.inputMetadata.code_eq] using hm.t_repad
  · change ZeroPadding.pad (word.length+2) (final.tapes 51)=
      ZeroPadding.pad 0 (CapMachine.counter (VerifierEncoding.code v).length v.stateCount)
    simpa only [ZeroPadding.pad_zero,hm.inputMetadata.code_eq] using hm.old.s_tape
  · change ZeroPadding.pad (word.length+2) (final.tapes 52)=
      ZeroPadding.pad 0 (CapMachine.counter (VerifierEncoding.code v).length (VerifierEncoding.code v).length)
    simpa only [ZeroPadding.pad_zero,hm.inputMetadata.code_eq] using hm.old.c_tape
  · change ZeroPadding.pad 0 (final.tapes 55)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.old.binary_s
  · change ZeroPadding.pad 0 (final.tapes 58)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hj
  · change ZeroPadding.pad 0 (final.tapes 59)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.old.start_tape
  · change ZeroPadding.pad 0 (final.tapes 1)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hscan
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change ZeroPadding.pad 0 (final.tapes 112)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.reset1
  · change ZeroPadding.pad 0 (final.tapes 68)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.old.four_t
  · rfl
  · rfl
  · rfl
  · rfl
  · change ZeroPadding.pad 0 (final.tapes 119)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.zero1
  · change ZeroPadding.pad 0 (final.tapes 132)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.unit
  · rfl
  · rfl
  · change ZeroPadding.pad 0 (final.tapes 113)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.reset2
  · change ZeroPadding.pad 0 (final.tapes 114)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.reset3
  · change ZeroPadding.pad (2*ClockDyadicLedger.width raw.length) (final.tapes 91)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hserial
  · change ZeroPadding.pad 0 (final.tapes 21)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hI
  · change ZeroPadding.pad 0 (final.tapes 92)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hout
  · change ZeroPadding.pad 0 (final.tapes 123)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.zero2
  · change ZeroPadding.pad _ (final.tapes 136)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero,hm.array]
    congr 1
    simp only [List.ofFn_const]
  · change ZeroPadding.pad 0 (final.tapes 115)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.reset4
  · change ZeroPadding.pad 0 (final.tapes 116)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.arrayReset
  · change ZeroPadding.pad 0 (final.tapes 111)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.capacity
  · change ZeroPadding.pad 0 (final.tapes 74)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hcount
  · change ZeroPadding.pad 0 (final.tapes 127)=ZeroPadding.pad 0 _
    simp only [ZeroPadding.pad_zero]
    exact hm.buffers.zero3
  · rfl

end NearCubicWires.RepairOrdinary.UTransition
