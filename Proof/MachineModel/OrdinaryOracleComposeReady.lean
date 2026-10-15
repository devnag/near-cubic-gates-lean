import Proof.MachineModel.OrdinaryOracleComposeGraph
import Proof.Amplification.RecoveryReadyCalls

/-! The exact reusable endpoints consumed by the compositor's five calls.
These are constructed from actual traces; tape installation only describes
the outcome of the statically focused executed call. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Ready (o : ℕ → Bool) (p : OrdinaryOracleProgram) (n : ℕ)
    (input output : Fin p.base.tapeCount → List Bool) : Prop :=
  ∃ final, OrdinaryOracleTrace o p n (initialConfiguration p.base.machine input) final ∧
    p.base.machine.halted final.control = true ∧
    (∀ i, final.heads i = 0) ∧ final.tapes = output

theorem Ready.padding {o : ℕ → Bool} {p : OrdinaryOracleProgram} {n : ℕ}
    {input output : Fin p.base.tapeCount → List Bool} (h : Ready o p n input output)
    (caps : Fin p.base.tapeCount → ℕ) :
    Ready o p n (fun i => ZeroPadding.pad (caps i) (input i))
      (fun i => ZeroPadding.pad (caps i) (output i)) := by
  obtain ⟨final, ht, hh, hr, ho⟩ := h
  refine ⟨ZeroPadding.config caps final, trace_padding caps ht, hh, hr, ?_⟩
  simp only [ZeroPadding.config, ho]

theorem Ready.focus {o : ℕ → Bool} {p : OrdinaryOracleProgram} {n t : ℕ}
    {input output : Fin p.base.tapeCount → List Bool} (h : Ready o p n input output)
    (ports : Ports t) (slot : Fin p.base.tapeCount → Fin t)
    (hi : Function.Injective slot) (hq : slot p.queryTape = ports.queryTape)
    (ambient : Fin t → List Bool) (hin : ∀ j, ambient (slot j) = input j) :
    Ready o (ports.program (focused p slot)) n ambient (install slot ambient output) := by
  obtain ⟨final, ht, hh, hr, ho⟩ := h
  have hf := focus_trace ports slot hi hq (fun _ => 0) ambient ht
  have he : RecoveryFocus.config slot (fun _ => 0) ambient
      (initialConfiguration p.base.machine input) =
      initialConfiguration (ports.program (focused p slot)).base.machine ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i <;>
        simp [RecoveryFocus.config, hp, initialConfiguration]
    · exact install_existing slot ambient input hin
  rw [he] at hf
  refine ⟨RecoveryFocus.config slot (fun _ => 0) ambient final, hf, hh, ?_, ?_⟩
  · intro i
    cases hp : RecoveryFocus.pick slot i <;> simp [RecoveryFocus.config, hp, hr]
  · change install slot ambient final.tapes = _
    rw [ho]

theorem Ready.ordinary {o : ℕ → Bool} {t s n : ℕ} (ports : Ports t)
    {p : Machine t s} {input output : Fin t → List Bool}
    (h : ReadyRun p n input output) : Ready o (ports.program (ordinary p)) n input output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  have trace := ordinary_trace (o := o) ports p n _ r hr
  rw [hs] at trace
  exact ⟨r.final, trace, (prefix_of_run p n _ r hr).2, hh, ht⟩

theorem Ready.call {o : ℕ → Bool} {t k n : ℕ} (ports : Ports t)
    (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k))
    (j l : Fin k) {input output : Fin t → List Bool}
    (h : Ready o (ports.program (pieces j)) n input output)
    (hn : ∀ q, next j q (fun i => readTapeBit (output i) 0) = some l) :
    OrdinaryOracleTrace o (ports.program (graph pieces entry next)) (n + 1)
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j)
        (initialConfiguration (pieces j).machine input))
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) l)
        (initialConfiguration (pieces l).machine output)) := by
  obtain ⟨final, ht, hh, hr, ho⟩ := h
  have body := graph_trace ports pieces entry next j ht
  have hscan : final.scanned = fun i => readTapeBit (output i) 0 := by
    funext i
    simp [Configuration.scanned, hr, ho]
  have ret := graph_return o ports pieces entry next j l final hh (by rw [hscan]; exact hn _)
  have he : RecoveryCalls.restarted (pieces l).machine final.heads final.tapes =
      initialConfiguration (pieces l).machine output := by
    apply configuration_ext
    · rfl
    · exact funext hr
    · exact ho
  rw [he] at ret
  exact trans body ret

theorem Ready.stop {o : ℕ → Bool} {t k n : ℕ} (ports : Ports t)
    (pieces : Fin k → Piece t) (entry : Fin k)
    (next : (j : Fin k) → Fin (pieces j).states → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) {input output : Fin t → List Bool}
    (h : Ready o (ports.program (pieces j)) n input output)
    (hn : ∀ q, next j q (fun i => readTapeBit (output i) 0) = none) :
    OrdinaryOracleTrace o (ports.program (graph pieces entry next)) (n + 1)
      (controlConfig (RecoveryCalls.code (fun j => (pieces j).states) j)
        (initialConfiguration (pieces j).machine input))
      (RecoveryCalls.stopped (fun j => (pieces j).states) (fun _ => 0) output) := by
  obtain ⟨final, ht, hh, hr, ho⟩ := h
  have body := graph_trace ports pieces entry next j ht
  have hscan : final.scanned = fun i => readTapeBit (output i) 0 := by
    funext i
    simp [Configuration.scanned, hr, ho]
  have ret := graph_stop o ports pieces entry next j final hh (by rw [hscan]; exact hn _)
  have he : RecoveryCalls.stopped (fun j => (pieces j).states) final.heads final.tapes =
      RecoveryCalls.stopped (fun j => (pieces j).states) (fun _ : Fin t => 0) output := by
    apply configuration_ext
    · rfl
    · exact funext hr
    · exact ho
  rw [he] at ret
  exact trans body ret

end NearCubicWires.RepairSource.OrdinaryOracleCompose
