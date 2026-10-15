import Proof.MachineModel.OrdinaryOracleComposeReady

/-! After cold recovery, unrelated graph cursors need not be zero. A ready
oracle call uses only its selected zero heads and preserves all other heads. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem Ready.focus_at {o : ℕ→Bool} {p : OrdinaryOracleProgram} {n t : ℕ}
    {input output : Fin p.base.tapeCount→List Bool} (h : Ready o p n input output)
    (ports : Ports t) (slot : Fin p.base.tapeCount→Fin t)
    (hi : Function.Injective slot) (hq : slot p.queryTape=ports.queryTape)
    (heads : Fin t→ℕ) (ambient : Fin t→List Bool)
    (hin : ∀ j,ambient (slot j)=input j) (hh0 : ∀ j,heads (slot j)=0) :
    ∃ final,OrdinaryOracleTrace o (ports.program (focused p slot)) n
      ⟨p.base.machine.start,heads,ambient⟩ final ∧
      (ports.program (focused p slot)).base.machine.halted final.control=true ∧
      final.heads=heads ∧ final.tapes=install slot ambient output:=by
  obtain ⟨base,hr,halt,hh,ht⟩:=h
  have trace:=focus_trace ports slot hi hq heads ambient hr
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
  refine ⟨RecoveryFocus.config slot heads ambient base,initial ▸ trace,halt,?_,?_⟩
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he:=RecoveryFocus.slot_of_pick slot hp
      simpa only [RecoveryFocus.config,hp] using
        (hh j).trans ((hh0 j).symm.trans (congrArg heads he))
  · change install slot ambient base.tapes=install slot ambient output
    rw [ht]

end NearCubicWires.RepairSource.OrdinaryOracleCompose
