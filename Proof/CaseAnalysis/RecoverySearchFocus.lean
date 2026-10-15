import Proof.CaseAnalysis.RecoverySearchCanonical

/-! Focus the completed search at the compiler's retained head state.
Only its actual input ports must be at zero; graph work cursors survive. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem focus_ready {o : Nat→Bool} {p : OrdinaryOracleProgram} {cost t : Nat}
    {input output : Fin p.base.tapeCount→List Bool}
    (ready : Ready o p cost input output) (ports : Ports t)
    (slots : Fin p.base.tapeCount→Fin t) (hinj : Function.Injective slots)
    (hquery : slots p.queryTape=ports.queryTape)
    (H : Fin t→Nat) (A : Fin t→List Bool)
    (hH : ∀ i,H (slots i)=0) (hA : ∀ i,A (slots i)=input i) :
    ∃ final,
      OrdinaryOracleTrace o (ports.program (focused p slots)) cost
        ⟨p.base.machine.start,H,A⟩ final ∧
      (ports.program (focused p slots)).base.machine.halted final.control=true ∧
      final.heads=H ∧ final.tapes=install slots A output := by
  classical
  obtain ⟨final,ht,halt,heads,tapes⟩:=ready
  have trace:=focus_trace ports slots hinj hquery H A ht
  have start : RecoveryFocus.config slots H A (initialConfiguration p.base.machine input)=
      (⟨p.base.machine.start,H,A⟩ : Configuration t p.base.stateCount) := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slots i with
      | none=>simp [RecoveryFocus.config,hp]
      | some j=>
        have he:=RecoveryFocus.slot_of_pick slots hp
        simp only [RecoveryFocus.config,hp,initialConfiguration]
        exact (he ▸ hH j).symm
    · exact install_existing slots A input hA
  rw [start] at trace
  refine ⟨RecoveryFocus.config slots H A final,trace,halt,?_,?_⟩
  · funext i
    cases hp : RecoveryFocus.pick slots i with
    | none=>simp [RecoveryFocus.config,hp]
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hp
      simp only [RecoveryFocus.config,hp]
      exact (heads j).trans (he ▸ hH j).symm
  · change install slots A final.tapes=install slots A output
    rw [tapes]

end NearCubicWires.RepairSource.RecoveryBoundedSearchExecution
