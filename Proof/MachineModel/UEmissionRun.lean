import Proof.MachineModel.UEmissionCalls

/-! The actual external-input event emitter, including early rejection.
Its fuel depends only on the ordinary input length. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_eq (raw witness : List Bool) :
    controlConfig (RecoveryCalls.code sizes 0)
      (TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => [])
        (initialConfiguration UPrepared.machine (UPrepared.input raw witness)))=
      initialConfiguration machine (input raw witness) := by
  apply configuration_ext
  · rfl
  · funext i
    simp [controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
  · rfl

theorem whole_prefix (raw witness : List Bool) :
    ∃ n final,n≤budget raw ∧ Timed machine n (initialConfiguration machine (input raw witness)) final ∧
      machine.halted final.control=true ∧ Outcome raw witness final := by
  obtain ⟨base,hbase,_,hvalid,hprepared⟩ := UPrepared.whole_run raw witness
  have he := TapeEmbedding.run_embed UPrepared.machine (fun _ : Fin 18 => 0)
    (fun _ : Fin 18 => []) _ _ base hbase
  let first := TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) base
  have hbit : first.final.scanned 79=base.final.scanned 79 := rfl
  cases hv : base.final.scanned 79 with
  | false =>
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 2 (UPrepared.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    have hbad : ¬UFront.Accepted raw witness := by
      intro ha
      have ht := hvalid.mpr ha
      rw [hv] at ht
      contradiction
    obtain ⟨m,final,hm,htail,hhalt,hout⟩ := reject_tail raw witness first.final hbad (by rfl) (by rfl)
    have hre : RecoveryCalls.restarted (programs 2) first.final.heads first.final.tapes=
        Composition.restart first.final reject.start := rfl
    have hcall := Eq.mp (congrArg (fun tail => Timed machine n
      (initialConfiguration machine (input raw witness))
      (controlConfig (RecoveryCalls.code sizes 2) tail)) hre) hcall
    have hb := UAggregateClock.emission_reject_bound raw
    exact ⟨n+m,final,by dsimp [budget]; omega,hcall.trans htail,hhalt,hout⟩
  | true =>
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 1 (UPrepared.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,final,hm,htail,hhalt,hout⟩ := walk_tail raw witness base.final (hprepared hv)
    have hre : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=
        UTransition.entry (UTransition.extended base.final).heads (UTransition.extended base.final).tapes := rfl
    have hcall := Eq.mp (congrArg (fun tail => Timed machine n
      (initialConfiguration machine (input raw witness))
      (controlConfig (RecoveryCalls.code sizes 1) tail)) hre) hcall
    have hb := UAggregateClock.emission_valid_bound raw (UAggregateClock.walkFuel raw.length) (by rfl)
    exact ⟨n+m,final,by dsimp [budget]; omega,hcall.trans htail,hhalt,hout⟩

theorem whole_run (raw witness : List Bool) :
    ∃ r,run machine (budget raw) (input raw witness)=some r ∧
      r.steps≤budget raw ∧ Outcome raw witness r.final := by
  obtain ⟨n,final,hn,hp,hh,hout⟩ := whole_prefix raw witness
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hm := run_moreFuel machine n (budget raw-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,by omega,by rwa [hf]⟩

end NearCubicWires.RepairOrdinary.UEmission
