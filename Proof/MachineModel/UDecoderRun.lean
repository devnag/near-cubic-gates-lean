import Proof.MachineModel.UDecoderTail

/-! Whole ordinary input preparation and guarded decoder, from the literal
external input/witness and blank scratch. The witness remains unread. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_bound (raw : List Bool) : budget raw≤600*(raw.length+1)*PCPResourceLedger.q raw.length^2 := by
  have hl : Nat.log 2 raw.length+1≤PCPResourceLedger.q raw.length :=
    Nat.add_le_add_right ((Nat.log_mono_right (Nat.le_succ raw.length)).trans
      (Nat.log_le_clog 2 (raw.length+1))) 1
  have hq : 1≤PCPResourceLedger.q raw.length := by simp [PCPResourceLedger.q]
  have hq2 : PCPResourceLedger.q raw.length≤PCPResourceLedger.q raw.length^2 :=
    Nat.le_self_pow (by decide) _
  have hb := Nat.mul_le_mul_left (128*(raw.length+1)) (hl.trans hq2)
  have hn : 0<(raw.length+1)*PCPResourceLedger.q raw.length^2 := by positivity
  dsimp [budget,UInputEntry.budget,Ready.limitedBudget]
  nlinarith

theorem initial_eq (raw witness : List Bool) :
    controlConfig (RecoveryCalls.code sizes 0)
      (TapeEmbedding.config (fun _ : Fin 19 => 0) (fun _ : Fin 19 => [])
        (initialConfiguration UInputOrdinary.machine (UInputOrdinary.input raw witness)))=
      initialConfiguration machine (input raw witness) := by
  apply configuration_ext
  · rfl
  · funext i
    simp [controlConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases]
  · rfl

theorem whole_prefix (raw witness : List Bool) :
    ∃ n final, n≤budget raw ∧ Timed machine n (initialConfiguration machine (input raw witness)) final ∧
      machine.halted final.control=true ∧
      (final.scanned 67=true ↔ Accepted raw) ∧
      (final.scanned 67=true → Successful raw witness final) := by
  obtain ⟨base,hbase,hraw0,hwit,hwhead,hvalid,hprepared,hsteps⟩ := UInputOrdinary.entry_run raw witness
  have he := TapeEmbedding.run_embed UInputOrdinary.machine (fun _ : Fin 19 => 0)
    (fun _ : Fin 19 => []) _ _ base hbase
  let first := TapeEmbedding.receipt (fun _ : Fin 19 => 0) (fun _ : Fin 19 => []) base
  have hbit : first.final.scanned 47=base.final.scanned 47 := rfl
  cases hv : base.final.scanned 47 with
  | false =>
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 2 (UInputEntry.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 2)
        (RecoveryCalls.restarted (programs 2) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,hm,htail⟩ := reject_tail first.final.heads first.final.tapes
    have hall := hcall.trans htail
    have hbad : ¬Accepted raw := by
      intro ha
      have ht := hvalid.mpr (accepted_valid raw ha)
      rw [hv] at ht
      contradiction
    refine ⟨n+m,_,by dsimp [budget]; omega,hall,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
    · rw [rejected_bit]; simp [hbad]
    · rw [rejected_bit]; simp
  | true =>
    obtain ⟨hp,hh⟩ := hprepared hv
    obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 1 (UInputEntry.budget raw)
      _ first he (by simp [next]; exact hbit.trans hv)
    have hcall := Eq.mp (congrArg (fun start => Timed machine n start
      (controlConfig (RecoveryCalls.code sizes 1)
        (RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes)))
      (initial_eq raw witness)) hcall
    obtain ⟨m,final,hm,htail,hhalt,haccept,hgood⟩ := decoder_tail raw witness base.final hp hh hwit hwhead
    have hre : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=decoderInput base.final := rfl
    have hcall := Eq.mp (congrArg (fun tail => Timed machine n
      (initialConfiguration machine (input raw witness))
      (controlConfig (RecoveryCalls.code sizes 1) tail)) hre) hcall
    have hall := hcall.trans htail
    exact ⟨n+m,final,by dsimp [budget]; omega,hall,hhalt,haccept,hgood⟩

theorem whole_run (raw witness : List Bool) :
    ∃ r,run machine (budget raw) (input raw witness)=some r ∧
      r.steps≤600*(raw.length+1)*PCPResourceLedger.q raw.length^2 ∧
      (r.final.scanned 67=true ↔ Accepted raw) ∧
      (r.final.scanned 67=true → Successful raw witness r.final) := by
  obtain ⟨n,final,hn,hp,hh,hbit,hgood⟩ := whole_prefix raw witness
  obtain ⟨r,hr,hf,hs⟩ := hp.run hh
  have hm := run_moreFuel machine n (budget raw-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,(by omega : r.steps≤budget raw).trans (budget_bound raw),by rwa [hf],by rwa [hf]⟩

end NearCubicWires.RepairOrdinary.UDecoder
