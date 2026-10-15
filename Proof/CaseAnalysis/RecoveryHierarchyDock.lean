import Proof.CaseAnalysis.RecoveryHierarchyDockLayout

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem scalar_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3≤Cpad)
    (A : Fin 158→List Bool) (H : Fin 158→ℕ)
    (h70 : A 70=[]) (h106 : A 106=[]) (hh70 : H 70=0) (hh106 : H 106=0) :
    ∃ r,runFrom (machine source k CH Cpad code) (HierarchyStreams.budget source k CH Cpad code x)
      ⟨(machine source k CH Cpad code).start,heads source k H,input source k A (frame x++frame bound)⟩=some r ∧
      r.steps≤HierarchyStreams.budget source k CH Cpad code x ∧
      HierarchyStreams.Fields source k CH Cpad code x bound (project source r.final) ∧
      ∀ i : Fin 158,i≠70→i≠106→
        r.final.heads (old source k i)=H i ∧ r.final.tapes (old source k i)=A i:=by
  obtain ⟨localRun,hl,hs,hfields⟩:=HierarchyStreams.scalar_run source k CH Cpad code x bound hpad
  obtain ⟨result,hr,hcontrol,hsteps,hh,ht,hother⟩:=RecoveryFocus.dock
    (slots source k) (slots_injective source k) (HierarchyStreams.machine source k CH Cpad code)
    (HierarchyStreams.budget source k CH Cpad code x) (heads source k H)
    (input source k A (frame x++frame bound)) _ (heads_projection source k H hh70 hh106)
    (input_projection source k A (frame x++frame bound) h70 h106) localRun hl
  have hp : project source result.final=localRun.final:=
    configuration_ext hcontrol (funext hh) (funext ht)
  refine ⟨result,hr,hsteps.trans_le hs,?_,?_⟩
  · rw [hp]
    exact hfields
  · intro i hi70 hi106
    have hu:=hother (old source k i) (slots_other source k i hi70 hi106)
    simpa only [heads,input,old,Fin.addCases_left] using hu

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock
