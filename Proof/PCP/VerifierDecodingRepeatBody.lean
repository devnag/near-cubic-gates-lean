import Proof.PCP.VerifierDecodingRepeatKernel

/-! Exact interpreter transport at the bounded decoder-loop body boundary.
The additional driver tape is physically retained throughout every body run. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_step {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (c d : Configuration (t+1) s) (hn : (TapeEmbedding.machine 1 body).halted c.control = false)
    (hs : step (TapeEmbedding.machine 1 body) c = some d) :
    step (machine body accepted) (controlConfig (bodyCode s) c) = some (controlConfig (bodyCode s) d) := by
  have he : step (machine body accepted) (controlConfig (bodyCode s) c) =
      (step (TapeEmbedding.machine 1 body) c).map (controlConfig (bodyCode s)) := by
    have hh : body.halted c.control = false := hn
    simp [step,machine,controlConfig,bodyCode,TapeEmbedding.machine,hh,Option.map_map,
      Function.comp_def,bodyAction,TapeEmbedding.action,LocalBitMultitape.applyAction,Configuration.scanned]
  rw [he,hs]
  rfl

theorem body_prefix {t s space time : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    {c d : Configuration (t+1) s} (hp : Prefix (TapeEmbedding.machine 1 body) space time c d) :
    Prefix (machine body accepted) space time (controlConfig (bodyCode s) c) (controlConfig (bodyCode s) d) := by
  apply hp.mapControl (bodyCode s)
  · intro x _; simp [machine,bodyCode]
  · exact body_step body accepted

theorem body_timed {t s fuel : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total head : ℕ) (r : ExecutionReceipt t s)
    (hr : runFrom body fuel data = some r) :
    Timed (machine body accepted) r.steps (active data total head) (active r.final total head) := by
  have hp := TapeEmbedding.run_embed body (fun _ : Fin 1 => head) (fun _ => CompareMachine.word total) fuel data r hr
  have hs := (prefix_of_run _ _ _ _ hp).1
  exact ⟨_,body_prefix body accepted hs⟩

theorem return_step {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total head : ℕ) (hh : body.halted data.control = true) :
    step (machine body accepted) (active data total head) =
      some (cfg (if accepted data.control data.scanned then 0 else 4) data total head) := by
  simp [step,machine,active,controlConfig,bodyCode,hh,Configuration.scanned,TapeEmbedding.config]
  apply configuration_ext
  · rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [LocalBitMultitape.applyAction,action,HeadMove.apply,cfg,controlConfig,TapeEmbedding.config]
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [LocalBitMultitape.applyAction,action,cfg,controlConfig,TapeEmbedding.config]

/-- One complete iteration, including the actual driver advance and return. -/
theorem iteration {t s fuel : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total pos : ℕ) (r : ExecutionReceipt t s)
    (hd : data.control = body.start) (hp : pos < total) (hr : runFrom body fuel data = some r) :
    Timed (machine body accepted) (r.steps+2) (cfg 0 data total (pos+1))
      (cfg (if accepted r.final.control r.final.scanned then 0 else 4) r.final total (pos+2)) := by
  have henter := enter_step body accepted data total pos hp
  have hd' : {data with control := body.start} = data := by
    apply configuration_ext
    · exact hd.symm
    · rfl
    · rfl
  rw [hd'] at henter
  have hbody := body_timed body accepted data total (pos+2) r hr
  have hret := return_step body accepted r.final total (pos+2) (prefix_of_run body _ _ r hr).2
  have htail := hbody.trans (Timed.single (by simp [machine,active,controlConfig,bodyCode]) hret)
  have hall := (Timed.single (by simp [machine,cfg,controlConfig,phaseCode]) henter).trans htail
  have he : 1+(r.steps+1)=r.steps+2 := by omega
  simpa only [he] using hall

theorem reset_prefix {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total pos : ℕ) (hp : pos ≤ total) :
    Timed (machine body accepted) (pos+1) (cfg 2 data total pos) (cfg 3 data total 1) := by
  induction pos with
  | zero => exact Timed.single (by simp [machine,cfg,controlConfig,phaseCode]) (reset_stop body accepted data total)
  | succ pos ih =>
    exact Timed.step (by simp [machine,cfg,controlConfig,phaseCode])
      (reset_step body accepted data total pos (by omega)) (ih (by omega))

/-- Exhaustion includes an actual return of the consumed unary driver. -/
theorem exhaust {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total : ℕ) :
    Timed (machine body accepted) (total+3) (cfg 0 data total (total+1)) (cfg 3 data total 1) := by
  have hreset := (Timed.single (by simp [machine,cfg,controlConfig,phaseCode])
    (reset_start body accepted data total total)).trans (reset_prefix body accepted data total total (Nat.le_refl _))
  have hall := (Timed.single (by simp [machine,cfg,controlConfig,phaseCode])
    (exhaust_step body accepted data total)).trans hreset
  have he : 1+(1+(total+1))=total+3 := by omega
  simpa only [he] using hall

end NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
