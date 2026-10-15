import Proof.PCP.VerifierDecodingTableBoundEntry

/-! Scoped ordinary loop for the decoder's state-flag, action-tag, and table
record scans. A literal sentinel counter drives repetition. The body has no
access to that added tape, and every entry, return, and final rewind is paid. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Control (s : ℕ) := Sum (Fin s) (Fin 5)
noncomputable def code (s : ℕ) : Control s ≃ Fin (Fintype.card (Control s)) := Fintype.equivFin _
noncomputable def bodyCode (s : ℕ) (q : Fin s) := code s (.inl q)
noncomputable def phaseCode (s : ℕ) (q : Fin 5) := code s (.inr q)
noncomputable def action {t s : ℕ} (q : Fin (Fintype.card (Control s))) (move : HeadMove) :
    Action (t+1) (Fintype.card (Control s)) :=
  ⟨q,fun _ => none,Fin.addCases (fun _ => .stay) (fun _ => move)⟩
noncomputable def bodyAction {t s : ℕ} (a : Action t s) : Action (t+1) (Fintype.card (Control s)) :=
  ⟨bodyCode s a.nextControl,Fin.addCases a.write (fun _ => none),Fin.addCases a.move (fun _ => .stay)⟩

noncomputable def machine {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool) :
    Machine (t+1) (Fintype.card (Control s)) where
  descriptionBits := 0
  start := phaseCode s 0
  halted := fun q => match (code s).symm q with | .inl _ => false | .inr phase => decide (3 ≤ phase.val)
  rule := fun q scanned => match (code s).symm q with
    | .inl state =>
      if body.halted state then
        some (action (phaseCode s (if accepted state (fun i => scanned (i.castAdd 1)) then 0 else 4)) .stay)
      else (body.rule state (fun i => scanned (i.castAdd 1))).map bodyAction
    | .inr phase =>
      if phase.val = 0 then
        some (if scanned ((0 : Fin 1).natAdd t) then action (bodyCode s body.start) .right
          else action (phaseCode s 1) .stay)
      else if phase.val = 1 then some (action (phaseCode s 2) .left)
      else if phase.val = 2 then
        some (if scanned ((0 : Fin 1).natAdd t) then action (phaseCode s 2) .left
          else action (phaseCode s 3) .right)
      else none

noncomputable def cfg {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total head : ℕ) :
    Configuration (t+1) (Fintype.card (Control s)) :=
  controlConfig (fun _ => phaseCode s phase)
    (TapeEmbedding.config (fun _ : Fin 1 => head) (fun _ => CompareMachine.word total) data)
noncomputable def active {t s : ℕ} (data : Configuration t s) (total head : ℕ) :
    Configuration (t+1) (Fintype.card (Control s)) :=
  controlConfig (bodyCode s) (TapeEmbedding.config (fun _ : Fin 1 => head) (fun _ => CompareMachine.word total) data)

@[simp] theorem cfg_cells {t s : ℕ} (phase : Fin 5) (data : Configuration t s) (total head : ℕ) :
    (cfg phase data total head).tapeCells = data.tapeCells+total+1 := by
  simp [cfg,controlConfig,CompareMachine.word,Configuration.tapeCells,
    TapeEmbedding.config,Fin.sum_univ_add]
  omega

private theorem apply_action {t s : ℕ} (phase next : Fin 5) (data : Configuration t s) (total head : ℕ) (move : HeadMove) :
    LocalBitMultitape.applyAction (cfg phase data total head) (action (phaseCode s next) move) =
      cfg next data total (move.apply head) := by
  apply configuration_ext
  · rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [LocalBitMultitape.applyAction,cfg,controlConfig,TapeEmbedding.config,action,HeadMove.apply]
    · simp [LocalBitMultitape.applyAction,cfg,controlConfig,TapeEmbedding.config,action]
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [LocalBitMultitape.applyAction,cfg,controlConfig,TapeEmbedding.config,action]

theorem enter_step {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total pos : ℕ) (hp : pos < total) :
    step (machine body accepted) (cfg 0 data total (pos+1)) =
      some (active {data with control := body.start} total (pos+2)) := by
  simp [step,machine,cfg,controlConfig,phaseCode,Configuration.scanned,TapeEmbedding.config,hp]
  apply configuration_ext
  · rfl
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [LocalBitMultitape.applyAction,action,HeadMove.apply,active,controlConfig,TapeEmbedding.config]
  · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [LocalBitMultitape.applyAction,action,active,controlConfig,TapeEmbedding.config]

theorem exhaust_step {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total : ℕ) :
    step (machine body accepted) (cfg 0 data total (total+1)) = some (cfg 1 data total (total+1)) := by
  simp [step,machine,cfg,controlConfig,phaseCode,Configuration.scanned,TapeEmbedding.config]
  exact apply_action 0 1 data total (total+1) .stay

theorem reset_start {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total pos : ℕ) :
    step (machine body accepted) (cfg 1 data total (pos+1)) = some (cfg 2 data total pos) := by
  simp [step,machine,cfg,controlConfig,phaseCode]
  simpa only [cfg,controlConfig,phaseCode,TapeEmbedding.config,HeadMove.apply,Nat.add_sub_cancel] using
    apply_action 1 2 data total (pos+1) .left

theorem reset_step {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total pos : ℕ) (hp : pos < total) :
    step (machine body accepted) (cfg 2 data total (pos+1)) = some (cfg 2 data total pos) := by
  simp [step,machine,cfg,controlConfig,phaseCode,Configuration.scanned,TapeEmbedding.config,hp]
  simpa only [cfg,controlConfig,phaseCode,TapeEmbedding.config,HeadMove.apply,Nat.add_sub_cancel] using
    apply_action 2 2 data total (pos+1) .left

theorem reset_stop {t s : ℕ} (body : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (data : Configuration t s) (total : ℕ) :
    step (machine body accepted) (cfg 2 data total 0) = some (cfg 3 data total 1) := by
  simp [step,machine,cfg,controlConfig,phaseCode,Configuration.scanned,TapeEmbedding.config]
  exact apply_action 2 3 data total 0 .right

end NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
