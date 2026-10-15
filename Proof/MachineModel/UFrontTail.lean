import Proof.MachineModel.UFrontCalls

/-! The guarded witness phase and final return of the actual ordinary front. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem witness_budget (raw x bound : List Bool) (hg : UInputScalars.Guards raw x bound) :
    UWitness.budget (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound)≤
      UWitness.budget (ClockDyadicLedger.width raw.length) (ClockDyadicLedger.limit raw.length) :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hg.2.2 1))

theorem witness_tail (raw witness : List Bool) (base : Configuration 69 decoderStates)
    (hp : UDecoder.Successful raw witness base) (hd : UDecoder.Accepted raw) :
    ∃ n final, n≤UWitness.budget (ClockDyadicLedger.width raw.length) (ClockDyadicLedger.limit raw.length)+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (witnessInput base)) final ∧
      machine.halted final.control=true ∧ (final.scanned 79=true ↔ Accepted raw witness) ∧
      (final.scanned 79=true → Successful raw witness final) := by
  obtain ⟨code,x,bound,padding,he,hg,last,hlast,hout,hpres,hsteps⟩ :=
    witness_run raw witness base (UDecoder.successful_fields raw witness base hp)
  obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 1
    (UWitness.budget (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound)) _ last hlast (by rfl)
  have hbound := witness_budget raw x bound hg
  have haccepted := hout.2.2.2.1.trans (accepted_iff raw witness code x bound padding he hg hd).symm
  refine ⟨m,_,by omega,hstop,?_,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa [RecoveryCalls.stopped,Configuration.scanned,UWitnessOrdinary.project,
      Function.comp_apply,UWitnessOrdinary.slots] using haccepted
  · intro _
    exact ⟨code,x,bound,padding,base,last.final,he,hg,hd,hp,rfl,rfl,hout,hpres⟩

end NearCubicWires.RepairOrdinary.UFront
