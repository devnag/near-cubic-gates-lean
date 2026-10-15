import Proof.MachineModel.OrdinaryOracleComposeReadyAt

/-! Focus an actual cold trace on its retained inputs. Final inactive heads
are unrestricted; no return-to-zero operation is added to the source run. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focus_from_initial {o : ℕ→Bool} {p : OrdinaryOracleProgram} {t cost : ℕ}
    (ports : Ports t) (slot : Fin p.base.tapeCount→Fin t)
    (hi : Function.Injective slot) (hq : slot p.queryTape=ports.queryTape)
    (heads : Fin t→ℕ) (ambient : Fin t→List Bool)
    (input : Fin p.base.tapeCount→List Bool) (final : p.Config)
    (h : OrdinaryOracleTrace o p cost (initialConfiguration p.base.machine input) final)
    (hin : ∀ j,ambient (slot j)=input j) (hh0 : ∀ j,heads (slot j)=0) :
    OrdinaryOracleTrace o (ports.program (focused p slot)) cost
      ⟨p.base.machine.start,heads,ambient⟩ (RecoveryFocus.config slot heads ambient final):=by
  have initial:RecoveryFocus.config slot heads ambient (initialConfiguration p.base.machine input)=
      (⟨p.base.machine.start,heads,ambient⟩ : Configuration t p.base.stateCount):=by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp]
      | some j =>
        have he:=RecoveryFocus.slot_of_pick slot hp
        simpa only [RecoveryFocus.config,hp,initialConfiguration] using
          (hh0 j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input hin
  exact initial ▸ focus_trace ports slot hi hq heads ambient h

end NearCubicWires.RepairSource.OrdinaryOracleCompose
