import Proof.MachineModel.UFrontTail

/-! All-input ordinary front execution: field/scalar checks, canonical
decoder and truncation-safe bounded witness prefix, with every return paid. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_eq (raw witness : List Bool) :
    controlConfig (RecoveryCalls.code sizes 0)
      (TapeEmbedding.config (fun _ : Fin 12 => 0) (fun _ : Fin 12 => [])
        (initialConfiguration UDecoder.machine (UDecoder.input raw witness)))=
      initialConfiguration machine (input raw witness) := by
  apply configuration_ext
  · rfl
  · funext i
    simp [controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
  · rfl

theorem whole_prefix (raw witness : List Bool) :
    ∃ n final, n≤budget raw ∧ Timed machine n (initialConfiguration machine (input raw witness)) final ∧
      machine.halted final.control=true ∧
      (final.scanned 79=true ↔ Accepted raw witness) ∧
      (final.scanned 79=true → Successful raw witness final) := by
  obtain ⟨base,hbase,hsteps,hvalid,hprepared⟩ := UDecoder.whole_run raw witness
  have he := TapeEmbedding.run_embed UDecoder.machine (fun _ : Fin 12 => 0)
    (fun _ : Fin 12 => []) _ _ base hbase
  let first := TapeEmbedding.receipt (fun _ : Fin 12 => 0) (fun _ : Fin 12 => []) base
  have hbit : first.final.scanned 67=base.final.scanned 67 := rfl
  cases hv : base.final.scanned 67 with
  | false =>
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 2 (UDecoder.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,hm,htail⟩ := reject_tail first.final.heads first.final.tapes
    have hall := hcall.trans htail
    have hbad : ¬Accepted raw witness := by
      intro ha
      have ht := hvalid.mpr (accepted_decoder raw witness ha)
      rw [hv] at ht
      contradiction
    refine ⟨n+m,_,by dsimp [budget]; omega,hall,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
    · rw [rejected_bit]; simp [hbad]
    · rw [rejected_bit]; simp
  | true =>
    have hp := hprepared hv
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 1 (UDecoder.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,final,hm,htail,hhalt,haccept,hgood⟩ := witness_tail raw witness base.final hp (hvalid.mp hv)
    have hre : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=witnessInput base.final := rfl
    have hcall := Eq.mp (congrArg (fun tail => Timed machine n
      (initialConfiguration machine (input raw witness))
      (controlConfig (RecoveryCalls.code sizes 1) tail)) hre) hcall
    exact ⟨n+m,final,by dsimp [budget]; omega,hcall.trans htail,hhalt,haccept,hgood⟩

theorem whole_run (raw witness : List Bool) :
    ∃ r,run machine (budget raw) (input raw witness)=some r ∧
      r.steps≤600*(raw.length+1)*PCPResourceLedger.q raw.length^2+
        128*(ClockDyadicLedger.limit raw.length+1)*(ClockDyadicLedger.width raw.length+1)+3 ∧
      (r.final.scanned 79=true ↔ Accepted raw witness) ∧
      (r.final.scanned 79=true → Successful raw witness r.final) := by
  obtain ⟨n,final,hn,hp,hh,hbit,hgood⟩ := whole_prefix raw witness
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hm := run_moreFuel machine n (budget raw-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  have hb := UDecoder.budget_bound raw
  refine ⟨r,hm,?_,by rwa [hf],by rwa [hf]⟩
  dsimp [budget,UWitness.budget] at hn
  omega

end NearCubicWires.RepairOrdinary.UFront
