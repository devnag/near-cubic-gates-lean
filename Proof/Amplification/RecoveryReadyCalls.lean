import Proof.Amplification.RecoveryRootRoundTapes

/-! Literal composition of reusable scalar receipts into the fixed finite call
graph. Tape installation is only a proof-level description of the output of
an executed call, never a machine instruction. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def install {t u : Nat} (slot : Fin t → Fin u)
    (ambient : Fin u → List Bool) (replacement : Fin t → List Bool) : Fin u → List Bool :=
  fun i => match RecoveryFocus.pick slot i with | some j => replacement j | none => ambient i

@[simp] theorem install_slot {t u : Nat} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (ambient : Fin u → List Bool) (replacement : Fin t → List Bool) (j : Fin t) :
    install slot ambient replacement (slot j) = replacement j := by
  simp [install, RecoveryFocus.pick_slot slot hi]

theorem install_other {t u : Nat} (slot : Fin t → Fin u)
    (ambient : Fin u → List Bool) (replacement : Fin t → List Bool) (i : Fin u)
    (hi : ∀ j, slot j ≠ i) : install slot ambient replacement i = ambient i := by
  classical
  have hn : ¬∃ j, slot j = i := by simpa using hi
  simp [install, RecoveryFocus.pick, hn]

theorem install_existing {t u : Nat} (slot : Fin t → Fin u)
    (ambient : Fin u → List Bool) (input : Fin t → List Bool)
    (hi : ∀ j, ambient (slot j) = input j) : install slot ambient input = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [install, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [install, hp]
    exact (hi j).symm.trans (congrArg ambient he)

theorem ReadyRun.focus {t u s n : Nat} {p : Machine t s}
    {input output : Fin t → List Bool} (h : ReadyRun p n input output)
    (slot : Fin t → Fin u) (hi : Function.Injective slot) (ambient : Fin u → List Bool)
    (hin : ∀ j, ambient (slot j) = input j) :
    ReadyRun (RecoveryFocus.machine slot p) n ambient (install slot ambient output) := by
  obtain ⟨base, hr, ht, hh, hs⟩ := h
  obtain ⟨r, hrun, hf, hsteps⟩ := RecoveryFocus.run_config slot hi p (fun _ => 0) ambient n
    (initialConfiguration p input) base hr
  have hinit : RecoveryFocus.config slot (fun _ => 0) ambient (initialConfiguration p input) =
      initialConfiguration (RecoveryFocus.machine slot p) ambient := by
    apply configuration_ext
    · rfl
    · funext i; cases hp : RecoveryFocus.pick slot i <;> simp [RecoveryFocus.config, hp, initialConfiguration]
    · exact install_existing slot ambient input hin
  rw [hinit] at hrun
  refine ⟨r, hrun, ?_, ?_, hsteps.trans hs⟩
  · rw [hf]
    change install slot ambient base.final.tapes = install slot ambient output
    rw [ht]
  · intro i
    cases hp : RecoveryFocus.pick slot i <;> simp [hf, RecoveryFocus.config, hp, hh]

theorem ReadyRun.call {t k n : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j l : Fin k) {input output : Fin t → List Bool}
    (h : ReadyRun (programs j) n input output)
    (hn : ∀ q, next j q (fun i => readTapeBit (output i) 0) = some l) :
    Timed (RecoveryCalls.machine sizes programs entry next) (n + 1)
      (controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) input))
      (controlConfig (RecoveryCalls.code sizes l) (initialConfiguration (programs l) output)) := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs j) n _ r hr
  have hbody := RecoveryCalls.body_timed sizes programs entry next j ⟨r.peakTapeCells, hp⟩
  rw [hs] at hbody
  have hscan : r.final.scanned = (fun i => readTapeBit (output i) 0) := by
    funext i; simp [Configuration.scanned, ht, hh]
  have hret := RecoveryCalls.return_step sizes programs entry next j l r.final hhalt
    (by rw [hscan]; exact hn _)
  have he : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes =
      initialConfiguration (programs l) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hret
  exact hbody.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

theorem ReadyRun.stop {t k n : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) {input output : Fin t → List Bool}
    (h : ReadyRun (programs j) n input output)
    (hn : ∀ q, next j q (fun i => readTapeBit (output i) 0) = none) :
    Timed (RecoveryCalls.machine sizes programs entry next) (n + 1)
      (controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) input))
      (RecoveryCalls.stopped sizes (fun _ => 0) output) := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  obtain ⟨hp, hhalt⟩ := prefix_of_run (programs j) n _ r hr
  have hbody := RecoveryCalls.body_timed sizes programs entry next j ⟨r.peakTapeCells, hp⟩
  rw [hs] at hbody
  have hscan : r.final.scanned = (fun i => readTapeBit (output i) 0) := by
    funext i; simp [Configuration.scanned, ht, hh]
  have hret := RecoveryCalls.stop_step sizes programs entry next j r.final hhalt
    (by rw [hscan]; exact hn _)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes =
      RecoveryCalls.stopped sizes (fun _ : Fin t => 0) output := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [he] at hret
  exact hbody.trans (Timed.single (by simp [RecoveryCalls.machine, controlConfig, RecoveryCalls.code]) hret)

end NearCubicWires.RepairOrdinary.RecoveryRootRound
