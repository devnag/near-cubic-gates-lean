import Proof.MachineModel.UInitializedTail

/-! Ordinary external input through all guards and actual memory
initialization, including rejecting inputs and all call returns. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem initial_eq (raw witness : List Bool) :
    controlConfig (RecoveryCalls.code sizes 0)
      (TapeEmbedding.config (fun _ : Fin 16 => 0) (fun _ : Fin 16 => [])
        (initialConfiguration UFront.machine (UFront.input raw witness)))=
      initialConfiguration machine (input raw witness) := by
  apply configuration_ext
  · rfl
  · funext i
    simp [controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
  · rfl

theorem whole_prefix (raw witness : List Bool) :
    ∃ n final,n≤budget raw ∧ Timed machine n (initialConfiguration machine (input raw witness)) final ∧
      machine.halted final.control=true ∧
      (final.scanned 79=true ↔ UFront.Accepted raw witness) ∧
      (final.scanned 79=true → Prepared raw witness final) := by
  obtain ⟨base,hbase,hsteps,hvalid,hprepared⟩ := UFront.whole_run raw witness
  have he := TapeEmbedding.run_embed UFront.machine (fun _ : Fin 16 => 0)
    (fun _ : Fin 16 => []) _ _ base hbase
  let first := TapeEmbedding.receipt (fun _ : Fin 16 => 0) (fun _ : Fin 16 => []) base
  have hbit : first.final.scanned 79=base.final.scanned 79 := rfl
  cases hv : base.final.scanned 79 with
  | false =>
    obtain ⟨n,hn,hstop⟩ := stop_receipt sizes programs 0 next 0 (UFront.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hstop := Eq.mp (congrArg (fun start => Timed machine n start
      (RecoveryCalls.stopped sizes first.final.heads first.final.tapes))
      (initial_eq raw witness)) hstop
    have hbad : ¬UFront.Accepted raw witness := by
      intro ha
      have ht := hvalid.mpr ha
      rw [hv] at ht
      contradiction
    have hfalse : (RecoveryCalls.stopped sizes first.final.heads first.final.tapes).scanned 79=false :=
      hbit.trans hv
    refine ⟨n,_,by dsimp [budget]; omega,hstop,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · rw [hfalse]; simp [hbad]
    · rw [hfalse]; simp
  | true =>
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 1 (UFront.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,final,hm,htail,hhalt,hflag,hgood⟩ := initialization_tail raw witness base.final (hprepared hv) hv
    have hre : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=
        UInitializationAmbient.entry base.final := rfl
    have hcall := Eq.mp (congrArg (fun tail => Timed machine n
      (initialConfiguration machine (input raw witness))
      (controlConfig (RecoveryCalls.code sizes 1) tail)) hre) hcall
    refine ⟨n+m,final,by dsimp [budget]; omega,hcall.trans htail,hhalt,?_,fun _ => hgood⟩
    exact ⟨fun _ => hvalid.mp hv,fun _ => hflag⟩

theorem budget_bound (raw : List Bool) :
    budget raw≤600*(raw.length+1)*PCPResourceLedger.q raw.length^2+
      400*(ClockDyadicLedger.limit raw.length+1)*(ClockDyadicLedger.width raw.length+1)+5 := by
  have hb := UDecoder.budget_bound raw
  dsimp [budget,initBudget,UFront.budget,UWitness.budget]
  nlinarith

theorem whole_run (raw witness : List Bool) :
    ∃ r,run machine (budget raw) (input raw witness)=some r ∧
      r.steps≤600*(raw.length+1)*PCPResourceLedger.q raw.length^2+
        400*(ClockDyadicLedger.limit raw.length+1)*(ClockDyadicLedger.width raw.length+1)+5 ∧
      (r.final.scanned 79=true ↔ UFront.Accepted raw witness) ∧
      (r.final.scanned 79=true → Prepared raw witness r.final) := by
  obtain ⟨n,final,hn,hp,hh,hbit,hgood⟩ := whole_prefix raw witness
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hm := run_moreFuel machine n (budget raw-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,(by omega : r.steps≤budget raw).trans (budget_bound raw),by rwa [hf],by rwa [hf]⟩

end NearCubicWires.RepairOrdinary.UInitialized
