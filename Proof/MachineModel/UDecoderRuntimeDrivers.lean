import Proof.MachineModel.UDecoderRuntimeScalars
import Proof.MachineModel.UDecoderRetained

/-! The actual decoder endpoint supplies bounded t and j for the next
numeric producer. The capped-t zero tail is kept explicit. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RuntimeDrivers (N : ℕ) (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) : Prop :=
  ∃ c t j,c≤Nat.log 2 N ∧ t≤c ∧ j≤c ∧
    ZeroPadding.pad (c+2) (tapes 50)=CapMachine.counter c t ∧
    tapes 58=CompareMachine.word j ∧ heads 50=1 ∧ heads 58=1

theorem successful_runtime_drivers (raw witness : List Bool)
    (final : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes)))
    (h : Successful raw witness final) (ha : Accepted raw) :
    RuntimeDrivers raw.length final.heads final.tapes := by
  obtain ⟨code,x,bound,padding,base,small,he,hg,_,_,_,_,hh,ht,ho⟩ := h
  have hd := (accepted_iff raw code x bound padding he hg).mp ha
  have hv := (Whole.valid_decode_iff raw.length code).mpr hd
  obtain ⟨t,s,fields,a,b,out,hparts,_,hs,heq,_⟩ := ho.2 hv
  have hcap := (Whole.valid_parts_iff code fields (Nat.log 2 raw.length) t s hparts).mp hv
  have hlen := GuardedPreparation.parts_lengths hparts
  have hj : natBitLength s ≤ s := by
    rw [←BitWidthMachine.width_eq s hs]
    exact ClockBinary.length_bound s s Nat.lt_two_pow_self
  have hsmallt := ready_t code fields (Nat.log 2 raw.length) t s a b out
  have hsmallj := ready_j code fields (Nat.log 2 raw.length) t s a b out
  have hth : small.heads 1=1 := by
    have h := congrArg (fun cfg => cfg.heads 1) heq
    exact h.trans hsmallt.1
  have hjh : small.heads 10=1 := by
    have h := congrArg (fun cfg => cfg.heads 10) heq
    exact h.trans hsmallj.1
  have htt : ZeroPadding.pad (code.length+2) (small.tapes 1)=CapMachine.counter code.length t := by
    have h := congrArg (fun cfg => cfg.tapes 1) heq
    simpa only [ZeroPadding.config,(runtime_scalar_caps code).1] using h.trans hsmallt.2
  have hjt : small.tapes 10=CompareMachine.word (natBitLength s) := by
    have h := congrArg (fun cfg => cfg.tapes 10) heq
    simpa [ZeroPadding.config,(runtime_scalar_caps code).2] using h.trans hsmallj.2
  have hsheads (i : Fin 21) : final.heads (slots i)=small.heads i := by
    rw [hh]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective]
  have hstapes (i : Fin 21) : final.tapes (slots i)=small.tapes i := by
    rw [ht]
    simp [RecoveryFocus.config,RecoveryFocus.pick_slot _ slots_injective]
  refine ⟨code.length,t,natBitLength s,hcap.1,by omega,by omega,?_,?_,?_,?_⟩
  · change ZeroPadding.pad (code.length+2) (final.tapes (slots 1))=_
    rw [hstapes]
    exact htt
  · exact (hstapes 10).trans hjt
  · exact (hsheads 1).trans hth
  · exact (hsheads 10).trans hjh

end NearCubicWires.RepairOrdinary.UDecoder
