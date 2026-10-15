import Proof.PCP.VerifierDecodingRepeatBody
import Proof.MachineModel.OrdinaryOracleComposeTrace

/-! Oracle transport through the existing physical sentinel-driven repeater.
The extra driver is retained during each body query; no query is copied or
recharged, and each driver movement and call return is an actual local step. -/
namespace NearCubicWires.RepairSource.RecoveryOracleRepeat
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
open VerifierDecoding.RepeatMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyReturn (s : ℕ) (r : OracleReturn s) :
    OracleReturn (Fintype.card (Control s)) :=
  ⟨bodyCode s r.onFalse,bodyCode s r.onTrue⟩

noncomputable def program (p : OrdinaryOracleProgram) : OrdinaryOracleProgram where
  base := ⟨p.base.tapeCount+1,Fintype.card (Control p.base.stateCount),
    by have h := p.base.twoTapes; omega,
    machine p.base.machine (fun _ _=>true),p.base.outputTape.castAdd 1,p.base.outputFresh⟩
  queryTape := p.queryTape.castAdd 1
  queryFresh := p.queryFresh
  query := fun q=>match (code p.base.stateCount).symm q with
    | .inl state => if p.base.machine.halted state then none
      else (p.query state).map (bodyReturn p.base.stateCount)
    | .inr _ => none

theorem body_trace {o : ℕ→Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {c d : p.Config} (total head : ℕ)
    (h : OrdinaryOracleTrace o p cost c d) :
    OrdinaryOracleTrace o (program p) cost (active c total head) (active d total head) := by
  induction h with
  | refl => exact .refl _
  | @cons cost rest c middle d hs ht ih =>
    apply OrdinaryOracleTrace.cons (middle:=active middle total head) _ ih
    cases hs with
    | «local» c middle hh hq hs =>
      refine .local _ _ ?_ ?_ ?_
      · simp [program,machine,active,controlConfig,bodyCode]
      · simp [program,active,controlConfig,bodyCode,TapeEmbedding.config,hh,hq]
      · apply body_step p.base.machine (fun _ _=>true)
          (TapeEmbedding.config (fun _ : Fin 1=>head) (fun _=>VerifierDecoding.CompareMachine.word total) c)
          (TapeEmbedding.config (fun _ : Fin 1=>head) (fun _=>VerifierDecoding.CompareMachine.word total) middle) hh
        rw [TapeEmbedding.step_embed,hs]
        rfl
    | ask c bits padding rule hh hq hr hw =>
      have hhalt : (program p).base.machine.halted (active c total head).control=false := by
        simp [program,machine,active,controlConfig,bodyCode]
      have hquery : (program p).query (active c total head).control=
          some (bodyReturn p.base.stateCount rule) := by
        simp [program,active,controlConfig,bodyCode,TapeEmbedding.config,hh,hq]
      have hhead : (active c total head).heads (program p).queryTape=0 := by
        simpa [program,active,controlConfig,TapeEmbedding.config] using hr
      have hword : (active c total head).tapes (program p).queryTape=frame bits++padding := by
        simpa [program,active,controlConfig,TapeEmbedding.config] using hw
      have ha := OrdinaryOracleStep.ask (oracle:=o) (program:=program p)
        (active c total head) bits padding (bodyReturn p.base.stateCount rule)
        hhalt hquery hhead hword
      have he : ({active c total head with control:=if o (CanonicalBinary.bitsValue bits)
          then (bodyReturn p.base.stateCount rule).onTrue
          else (bodyReturn p.base.stateCount rule).onFalse} : (program p).Config)=
          active {c with control:=if o (CanonicalBinary.bitsValue bits)
            then rule.onTrue else rule.onFalse} total head := by
        cases o (CanonicalBinary.bitsValue bits) <;> rfl
      exact Eq.mp (congrArg (fun endpoint : (program p).Config=>
        OrdinaryOracleStep o (program p) ((frame bits).length+1) (active c total head) endpoint) he) ha

theorem phase_local (o : ℕ→Bool) (p : OrdinaryOracleProgram)
    (phase : Fin 5) (data : p.Config) (total head : ℕ) (after : (program p).Config)
    (hp : phase.val<3)
    (hs : step (program p).base.machine (cfg phase data total head)=some after) :
    OrdinaryOracleTrace o (program p) 1 (cfg phase data total head) after := by
  apply single
  refine .local _ _ ?_ ?_ hs
  · simp [program,machine,cfg,controlConfig,phaseCode,Nat.not_le.mpr hp]
  · simp [program,cfg,controlConfig,phaseCode]

theorem iteration {o : ℕ→Bool} {p : OrdinaryOracleProgram}
    {cost : ℕ} {c d : p.Config} (total pos : ℕ)
    (hp : pos<total) (hc : c.control=p.base.machine.start)
    (h : OrdinaryOracleTrace o p cost c d) (hh : p.base.machine.halted d.control=true) :
    OrdinaryOracleTrace o (program p) (cost+2)
      (cfg 0 c total (pos+1)) (cfg 0 d total (pos+2)) := by
  have henter := enter_step p.base.machine (fun _ _=>true) c total pos hp
  have hc' : {c with control:=p.base.machine.start}=c := by
    apply configuration_ext
    · exact hc.symm
    · rfl
    · rfl
  rw [hc'] at henter
  have hin := phase_local o p 0 c total (pos+1) _ (by decide) henter
  have hbody := body_trace total (pos+2) h
  have hreturn : OrdinaryOracleTrace o (program p) 1
      (active d total (pos+2)) (cfg 0 d total (pos+2)) := by
    apply single
    refine .local _ _ ?_ ?_ (return_step p.base.machine (fun _ _=>true) d total (pos+2) hh)
    · simp [program,machine,active,controlConfig,bodyCode]
    · simp [program,active,controlConfig,bodyCode,TapeEmbedding.config,hh]
  have hall := trans hin (trans hbody hreturn)
  simpa only [show 1+(cost+1)=cost+2 by omega] using hall

theorem reset_trace (o : ℕ→Bool) (p : OrdinaryOracleProgram)
    (data : p.Config) (total pos : ℕ) (hp : pos≤total) :
    OrdinaryOracleTrace o (program p) (pos+1)
      (cfg 2 data total pos) (cfg 3 data total 1) := by
  induction pos with
  | zero =>
    exact phase_local o p 2 data total 0 _ (by decide)
      (reset_stop p.base.machine (fun _ _=>true) data total)
  | succ pos ih =>
    have hs := phase_local o p 2 data total (pos+1) _ (by decide)
      (reset_step p.base.machine (fun _ _=>true) data total pos (by omega))
    simpa only [Nat.add_comm 1] using trans hs (ih (by omega))

theorem exhaust_trace (o : ℕ→Bool) (p : OrdinaryOracleProgram)
    (data : p.Config) (total : ℕ) :
    OrdinaryOracleTrace o (program p) (total+3)
      (cfg 0 data total (total+1)) (cfg 3 data total 1) := by
  have h1 := phase_local o p 0 data total (total+1) _ (by decide)
    (exhaust_step p.base.machine (fun _ _=>true) data total)
  have h2 := phase_local o p 1 data total (total+1) _ (by decide)
    (reset_start p.base.machine (fun _ _=>true) data total total)
  have h3 := reset_trace o p data total total (Nat.le_refl _)
  simpa only [show 1+(1+(total+1))=total+3 by omega] using trans h1 (trans h2 h3)

end NearCubicWires.RepairSource.RecoveryOracleRepeat
