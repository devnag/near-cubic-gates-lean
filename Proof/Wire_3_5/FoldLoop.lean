import Proof.CaseAnalysis.RecoveryGrammarRepeat
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding

/-- One step on the added (last) tape: move its head by `move`, then halt. -/
def counterStep (t : ℕ) (move : HeadMove) : Machine (t + 1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1, fun _ => none, Fin.addCases (fun _ => HeadMove.stay) (fun _ => move)⟩ else none

/-- The configuration of `t` body tapes at heads `bodyHeads` and the counter tape at head `h`. -/
def loopConfig {t s : ℕ} (q : Fin s) (T : Fin t → List Bool) (bodyHeads : Fin t → ℕ) (w : List Bool) (h : ℕ) :
    Configuration (t + 1) s :=
  ⟨q, Fin.addCases bodyHeads (fun _ => h), Fin.addCases T (fun _ => w)⟩

theorem counterStep_run (t : ℕ) (move : HeadMove) (T : Fin t → List Bool) (bodyHeads : Fin t → ℕ)
    (w : List Bool) (h : ℕ) :
    runFrom (counterStep t move) 1 (loopConfig 0 T bodyHeads w h) =
      some ⟨loopConfig 1 T bodyHeads w (move.apply h), 1,
        max (loopConfig (0 : Fin 2) T bodyHeads w h).tapeCells
          (loopConfig (1 : Fin 2) T bodyHeads w (move.apply h)).tapeCells⟩ := by
  have hstep : step (counterStep t move) (loopConfig 0 T bodyHeads w h) =
      some (loopConfig 1 T bodyHeads w (move.apply h)) := by
    simp only [step, counterStep, loopConfig]
    simp only [Fin.val_zero, ↓reduceIte, Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [applyAction, HeadMove.apply]
      · simp [applyAction]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [applyAction]
  have hnot : (counterStep t move).halted (loopConfig (0 : Fin 2) T bodyHeads w h).control = false := rfl
  have h0 := runFrom_zero_of_halted (counterStep t move) (loopConfig (1 : Fin 2) T bodyHeads w (move.apply h)) rfl
  exact runFrom_step _ _ _ _ hnot hstep h0

/-- **The uniform loop**: move the counter head onto the first cell, run `body` once per counter cell, move it back. -/
noncomputable def foldLoop {t s : ℕ} (body : Machine t s) :=
  Composition.machine (counterStep t .right)
    (Composition.machine (RepeatMachine.machine body (fun _ _ => true)) (counterStep t .left))

theorem initial_loopConfig {t u : ℕ} (p : Machine (t + 1) u) (T : Fin t → List Bool) (w : List Bool) :
    initialConfiguration p (Fin.addCases T (fun _ => w)) = loopConfig p.start T (fun _ => 0) w 0 := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [initialConfiguration, loopConfig]
  · rfl

theorem repeat_cfg_eq {t s : ℕ} (body : Machine t s) (phase : Fin 5) (T : Fin t → List Bool) (c h : ℕ) :
    RepeatMachine.cfg phase (initialConfiguration body T) c h =
      loopConfig (RepeatMachine.phaseCode s phase) T (fun _ => 0) (CompareMachine.word c) h := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [RepeatMachine.cfg, controlConfig, TapeEmbedding.config, loopConfig, initialConfiguration]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [RepeatMachine.cfg, controlConfig, TapeEmbedding.config, loopConfig, initialConfiguration]

/-- **The uniform loop runs the body `c` times** at restored heads. -/
theorem foldLoop_ready {t s : ℕ} (body : Machine t s) (T : ℕ → Fin t → List Bool) (cost c : ℕ)
    (hbody : ∀ i, i < c → ClockJoin.ReadyRun body cost (T i) (T (i + 1))) :
    ClockJoin.ReadyRun (foldLoop body) (1 + 1 + (c * (cost + 2) + c + 3 + 1 + 1))
      (Fin.addCases (T 0) (fun _ => CompareMachine.word c))
      (Fin.addCases (T c) (fun _ => CompareMachine.word c)) := by
  -- the repeat run between the two counter steps
  obtain ⟨r, hr, hrs, hrf⟩ := RecoveryBoundedGrammarRepeat.run body (fun i => initialConfiguration body (T i))
    cost c c 0 0 (by omega) (fun _ _ _ => rfl) (fun i _ hi => by
      obtain ⟨x, hx, hxt, hxh, hxs⟩ := hbody i (by omega)
      exact ⟨x, hx, hxs, funext hxh, hxt⟩)
  -- enter: counter head 0 → 1; leave: counter head 1 → 0
  obtain ⟨r1, h1, hr1f, hr1s⟩ : ∃ r1 : ExecutionReceipt (t + 1) 2,
      runFrom (counterStep t .right) 1 (loopConfig 0 (T 0) (fun _ => 0) (CompareMachine.word c) 0) = some r1 ∧
        r1.final = loopConfig 1 (T 0) (fun _ => 0) (CompareMachine.word c) 1 ∧ r1.steps = 1 :=
    ⟨_, counterStep_run t .right (T 0) (fun _ => 0) (CompareMachine.word c) 0, rfl, rfl⟩
  obtain ⟨r3, h3, hr3f, hr3s⟩ : ∃ r3 : ExecutionReceipt (t + 1) 2,
      runFrom (counterStep t .left) 1 (loopConfig 0 (T c) (fun _ => 0) (CompareMachine.word c) 1) = some r3 ∧
        r3.final = loopConfig 1 (T c) (fun _ => 0) (CompareMachine.word c) 0 ∧ r3.steps = 1 :=
    ⟨_, counterStep_run t .left (T c) (fun _ => 0) (CompareMachine.word c) 1, rfl, rfl⟩
  have hfin : Composition.restart r.final (counterStep t .left).start =
      loopConfig 0 (T c) (fun _ => 0) (CompareMachine.word c) 1 := by
    rw [hrf, Nat.zero_add, repeat_cfg_eq]; rfl
  have hinner := Composition.run_join (RepeatMachine.machine body (fun _ _ => true)) (counterStep t .left)
    _ 1 _ r r3 hr (by rw [hfin]; exact h3)
  have hstart : Composition.restart r1.final
      (Composition.machine (RepeatMachine.machine body (fun _ _ => true)) (counterStep t .left)).start =
      Composition.leftConfig 2 (RepeatMachine.cfg 0 (initialConfiguration body (T 0)) c (0 + 1)) := by
    rw [hr1f, repeat_cfg_eq]; rfl
  have houter := Composition.run_join (counterStep t .right)
    (Composition.machine (RepeatMachine.machine body (fun _ _ => true)) (counterStep t .left)) 1 _ _ r1 _ h1
    (by rw [hstart]; exact hinner)
  refine ⟨Composition.joinedReceipt r1 (Composition.joinedReceipt r r3), ?_, ?_, ?_, ?_⟩
  · unfold run foldLoop
    rw [initial_loopConfig]
    exact houter
  · simp only [Composition.joinedReceipt, Composition.rightConfig, hr3f, loopConfig]
  · intro i
    simp only [Composition.joinedReceipt, Composition.rightConfig, hr3f, loopConfig]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · simp only [Composition.joinedReceipt, hr1s, hr3s]
    omega

end NearCubicWires.WireExponent3_5.Transfer
