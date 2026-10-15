import Proof.PCP.PCPSerializerCapacityPower
import Proof.PCP.PCPSerializerMassReady

/-! Execute a restored local producer while retaining arbitrary inactive
source and driver cursors of the enclosing serializer. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ClockJoin.ReadyRun.focus_at {t u s n : ℕ} {p : Machine t s}
    {input output : Fin t → List Bool} (h : ClockJoin.ReadyRun p n input output)
    (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (heads : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hin : ∀ j,ambient (slot j)=input j) (hh0 : ∀ j,heads (slot j)=0) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) n ⟨p.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=install slot ambient output ∧ r.steps ≤ n := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p heads ambient n
    (initialConfiguration p input) base hr
  have hinit : RecoveryFocus.config slot heads ambient (initialConfiguration p input)=
      (⟨p.start,heads,ambient⟩ : Configuration u s) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        simpa only [RecoveryFocus.config,hp,initialConfiguration] using
          (hh0 j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input hin
  rw [hinit] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [hf,RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simpa only [hf,RecoveryFocus.config,hp] using
        (hh j).trans ((hh0 j).symm.trans (congrArg heads he))
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [ht]

end NearCubicWires.RepairOrdinary
