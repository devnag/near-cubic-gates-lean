import Proof.Amplification.RecoveryUnpairSetup

/-! One fixed ordinary program joins binary input preparation, constant
initialization, every radix round, and the final unpair branch. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev loopStates := Fintype.card (RecoveryCalls.Control RecoveryRootLoop.sizes)
abbrev finishStates := Fintype.card (RecoveryCalls.Control RecoveryUnpairFinish.sizes)
def sizes : Fin 4 → Nat := ![8, 10, loopStates, finishStates]
noncomputable def programs : (j : Fin 4) → Machine 15 (sizes j)
  | ⟨0, _⟩ => bootMachine
  | ⟨1, _⟩ => initializeMachine
  | ⟨2, _⟩ => RecoveryRootLoop.machine
  | ⟨3, _⟩ => RecoveryFocus.machine RecoveryRootLoop.bodySlots RecoveryUnpairFinish.machine
  | ⟨n + 4, h⟩ => False.elim (by omega)

def next (j : Fin 4) (_ : Fin (sizes j)) (_ : Fin 15 → Bool) : Option (Fin 4) :=
  if j.val = 0 then some 1 else if j.val = 1 then some 2 else if j.val = 2 then some 3 else none

noncomputable def rawMachine := RecoveryCalls.machine sizes programs 0 next

def loopStore (bits : List Bool) := RecoveryRootIteration.iterate
  (RecoveryRootIteration.digits bits) (initialStore bits)
def resultStore (bits : List Bool) := RecoveryUnpairFinish.finished (loopStore bits)
def loopTime (bits : List Bool) := RecoveryRootIteration.time
  (RecoveryRootIteration.digits bits) (initialStore bits)
def rawTime (bits : List Bool) :=
  ((8 * bits.length + 6 + 1 + (16 + 1)) + (loopTime bits + 1)) +
    (RecoveryUnpairFinish.time (loopStore bits) + 1)

noncomputable def boundary (j : Fin 4) (bits : List Bool) (s : Store) (position : Nat) :=
  controlConfig (RecoveryCalls.code sizes j)
    (RecoveryRootLoop.config (programs j).start (frame bits) (frame (RecoveryRadixInput.prepared bits)) s position)

theorem initial_config {states : Nat} (p : Machine 15 states) (bits : List Bool) (s : Store) :
    initialConfiguration p (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) s) =
      RecoveryRootLoop.config p.start (frame bits) (frame (RecoveryRadixInput.prepared bits)) s 0 := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem setup_call (bits : List Bool) :
    Timed rawMachine (8 * bits.length + 6 + 1 + (16 + 1))
      (initialConfiguration rawMachine (input bits)) (boundary 2 bits (initialStore bits) 0) := by
  have hb := (boot_ready bits).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hi := (initialize_ready bits).call sizes programs 0 next 1 2 (by intro q; rfl)
  have h := hb.trans hi
  have hin : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) (input bits)) =
      initialConfiguration rawMachine (input bits) := by rfl
  rw [hin] at h
  change Timed rawMachine _ _
    (controlConfig (RecoveryCalls.code sizes 2)
      (initialConfiguration (programs 2)
        (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) (initialStore bits)))) at h
  rw [initial_config] at h
  exact h

theorem loop_call (bits : List Bool) :
    Timed rawMachine (loopTime bits + 1) (boundary 2 bits (initialStore bits) 0)
      (boundary 3 bits (loopStore bits) (4 * bits.length)) := by
  obtain ⟨r, hr, ht, hh, hs⟩ := RecoveryRootLoop.loop_run
    (RecoveryRootIteration.digits bits) (frame bits) (initialStore bits) (initial_valid bits)
  rw [RecoveryRootIteration.stream_digits] at hr ht
  rw [RecoveryRootIteration.digits_length] at hh
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs 2) _ _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next 2 ⟨r.peakTapeCells, hp⟩
  rw [hs, initial_config] at hb
  have hret := RecoveryCalls.return_step sizes programs 0 next 2 3 r.final hhalt (by rfl)
  have he : RecoveryCalls.restarted (programs 3) r.final.heads r.final.tapes =
      RecoveryRootLoop.config (programs 3).start (frame bits) (frame (RecoveryRadixInput.prepared bits))
        (loopStore bits) (4 * bits.length) := by rw [hh, ht]; rfl
  rw [he] at hret
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem finish_call (bits : List Bool) :
    Timed rawMachine (RecoveryUnpairFinish.time (loopStore bits) + 1)
      (boundary 3 bits (loopStore bits) (4 * bits.length))
      (RecoveryCalls.stopped sizes (RecoveryRootLoop.heads (4 * bits.length))
        (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) (resultStore bits))) := by
  have hv := RecoveryRootIteration.iterate_valid (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits)
  obtain ⟨base, hr, ht, hh, hs⟩ := RecoveryUnpairFinish.finish_ready (loopStore bits) hv.1 hv.2.2
  obtain ⟨r, hrun, hf, hsteps⟩ := RecoveryFocus.run_config RecoveryRootLoop.bodySlots
    RecoveryRootLoop.bodySlots_injective RecoveryUnpairFinish.machine
    (RecoveryRootLoop.heads (4 * bits.length))
    (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) (loopStore bits))
    (RecoveryUnpairFinish.time (loopStore bits)) _ base hr
  have hin := RecoveryRootLoop.body_config (frame bits) (frame (RecoveryRadixInput.prepared bits))
    (loopStore bits) (loopStore bits) (4 * bits.length)
    (initialConfiguration RecoveryUnpairFinish.machine (loopStore bits).tapes) (by intro i; rfl) rfl
  have hout := RecoveryRootLoop.body_config (frame bits) (frame (RecoveryRadixInput.prepared bits))
    (loopStore bits) (resultStore bits) (4 * bits.length) base.final hh ht
  rw [hin] at hrun
  rw [hout] at hf
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs 3) _ _ r hrun
  have hb := RecoveryCalls.body_timed sizes programs 0 next 3 ⟨r.peakTapeCells, hp⟩
  rw [hsteps, hs] at hb
  have hret := RecoveryCalls.stop_step sizes programs 0 next 3 r.final hhalt (by rfl)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes =
      RecoveryCalls.stopped sizes (RecoveryRootLoop.heads (4 * bits.length))
        (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) (resultStore bits)) := by
    rw [hf]; rfl
  rw [he] at hret
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem raw_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 15 (Fintype.card (RecoveryCalls.Control sizes)),
      run rawMachine (rawTime bits) (input bits) = some r ∧
      r.final.tapes = RecoveryRootLoop.tapes
        (frame bits) (frame (RecoveryRadixInput.prepared bits)) (resultStore bits) ∧
      r.final.heads = RecoveryRootLoop.heads (4 * bits.length) ∧ r.steps = rawTime bits := by
  have h := ((setup_call bits).trans (loop_call bits)).trans (finish_call bits)
  obtain ⟨r, hr, hf, hs⟩ := h.run
    (by simp [rawMachine, RecoveryCalls.machine, RecoveryCalls.stopped])
  exact ⟨r, hr, by simp [hf, RecoveryCalls.stopped], by simp [hf, RecoveryCalls.stopped], hs⟩

theorem loop_width (bits : List Bool) : (loopStore bits).root.length = 3 + 2 * bits.length := by
  have h := RecoveryRootIteration.iterate_width (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits)
  simpa only [loopStore, initial_width, RecoveryRootIteration.digits_length] using h

theorem raw_time_bound (bits : List Bool) : rawTime bits ≤ 512 * (bits.length + 1) ^ 2 := by
  have hl := RecoveryRootIteration.initial_time_bound (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits) (initial_width bits)
  rw [RecoveryRootIteration.digits_length] at hl
  have hf := RecoveryUnpairFinish.time_bound (loopStore bits)
  rw [loop_width] at hf
  unfold rawTime loopTime
  nlinarith

theorem result_values (bits : List Bool) :
    (RadixSemantics.value (resultStore bits).root, RadixSemantics.value (resultStore bits).remainder) =
      Nat.unpair (RadixSemantics.value bits) := by
  have hv := RecoveryRootIteration.iterate_valid (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits)
  have hf := RecoveryUnpairFinish.finished_values (loopStore bits) hv.1
  have hn := RecoveryRootIteration.iterate_numeric (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits)
  rw [initial_numeric] at hn
  change (loopStore bits).numeric = _ at hn
  rw [hn, RepairSource.RecoveryOracle.RestoringRoot.execute_unpair,
    RecoveryRootIteration.digits_value] at hf
  exact hf

theorem result_width (bits : List Bool) :
    (resultStore bits).root.length = 3 + 2 * bits.length ∧
      (resultStore bits).remainder.length = 3 + 2 * bits.length := by
  have hv := RecoveryRootIteration.iterate_valid (RecoveryRootIteration.digits bits)
    (initialStore bits) (initial_valid bits)
  simpa only [resultStore, loop_width] using RecoveryUnpairFinish.finished_width (loopStore bits) hv.1

end NearCubicWires.RepairOrdinary.RecoveryUnpair
