import Proof.CaseAnalysis.RowsCircuitBottomLoop

/-! Alias the already produced bottom-count template as the literal loop
driver. Its existing trailing false cell changes no instruction or runtime. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverPads {t : ℕ} (count : ℕ) (i : Fin (t+1)):=if i.val=t then count+2 else 0
noncomputable def templateCfg {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total pos : ℕ):=
  controlConfig (fun _=>RepeatMachine.phaseCode s phase)
    (TapeEmbedding.config (fun _ : Fin 1=>pos) (fun _=>UnaryTemplate.tape total) data)

theorem template_cfg {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total pos : ℕ) :
    ZeroPadding.config (driverPads total) (RepeatMachine.cfg phase data total pos)=
      templateCfg phase data total pos:=by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,driverPads,Fin.val_castAdd,if_neg (show j.val≠t by omega),
        ZeroPadding.pad_zero,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,templateCfg]
    · intro j
      have hj:j=0:=Fin.eq_zero j;subst j
      simp only [ZeroPadding.config,driverPads,Fin.val_natAdd,Fin.val_zero,Nat.add_zero,if_true,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_right,templateCfg]
      change ZeroPadding.pad (total+2) (CompareMachine.word total)=UnaryTemplate.tape total
      simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem template_run {t s : ℕ} (body : Machine t s) (fuel total : ℕ)
    (first last : Configuration t s) (base : ExecutionReceipt (t+1) (Fintype.card (RepeatMachine.Control s)))
    (hr : runFrom (CloseoutRowsDegreeLoop.machine body) fuel (RepeatMachine.cfg 0 first total 1)=some base)
    (hf : base.final=RepeatMachine.cfg 3 last total 1) : ∃ r,
    runFrom (CloseoutRowsDegreeLoop.machine body) fuel (templateCfg 0 first total 1)=some r ∧
      r.final=templateCfg 3 last total 1 ∧ r.steps=base.steps:=by
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config (CloseoutRowsDegreeLoop.machine body) (driverPads total) _ _ base hr
  rw [template_cfg] at rr
  rw [hf,template_cfg] at rf
  exact ⟨r,rr,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomLoop
