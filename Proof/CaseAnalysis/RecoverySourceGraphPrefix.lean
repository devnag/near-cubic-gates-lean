import Proof.CaseAnalysis.RecoverySourceGraphLayout

/-! Execute the complete physical supplier inside the unchanged graph bank.
The serializer's intervening1506 tapes remain genuinely empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def supplierMachine (k d CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (supplierSlots source k d) (RecoveryBoundedColdSuppliers.machine source k d CH Cpad code)

theorem prefix_run (k d CH Cpad : ℕ) (code x bound : List Bool) (W : ℕ) (hpad : k+3 ≤ Cpad) :
    ∃ r,run (supplierMachine source k d CH Cpad code)
      (RecoveryBoundedColdSuppliers.budget source k d CH Cpad code x W)
      (input source k d (frame x++frame bound) W)=some r ∧
      r.steps ≤ RecoveryBoundedColdSuppliers.budget source k d CH Cpad code x W ∧
      (∀ i : Fin 1664,r.final.heads (graphSlots source k d i)=0) ∧
      (∀ i : Fin 1664,r.final.tapes (graphSlots source k d i)=
        RecoveryBoundedColdGraph.insert [] (RecoveryBoundedColdSuppliers.output source k d CH Cpad code x W) i) ∧
      r.final.tapes (hierarchyPort source k d)=frame x++frame bound ∧
      r.final.heads (hierarchyPort source k d)=0 ∧
      r.final.tapes (wPort source k d)=List.replicate W true ∧
      r.final.heads (wPort source k d)=0:=by
  obtain ⟨s,hs,hsteps,hheads,htapes,hinput,hihead,hW,hWhead⟩:=
    RecoveryBoundedColdSuppliers.cold_run source k d CH Cpad code x bound W hpad
  obtain ⟨r,hr,_hcontrol,hstep,hhead,htape,hkeep⟩:=RecoveryFocus.dock
    (supplierSlots source k d) (supplier_injective source k d)
    (RecoveryBoundedColdSuppliers.machine source k d CH Cpad code)
    (RecoveryBoundedColdSuppliers.budget source k d CH Cpad code x W)
    (fun _=>0) (input source k d (frame x++frame bound) W) _
    (by intro i;rfl) (input_supplier source k d (frame x++frame bound) W) s hs
  have hselhead (i : Fin 158) : r.final.heads (graphSlots source k d (RecoveryBoundedColdGraph.slots i))=0:=by
    rw [←supplier_old]
    exact (hhead _).trans (hheads i)
  have hseltape (i : Fin 158) : r.final.tapes (graphSlots source k d (RecoveryBoundedColdGraph.slots i))=
      RecoveryBoundedColdSuppliers.output source k d CH Cpad code x W i:=by
    rw [←supplier_old]
    exact (htape _).trans (htapes i)
  refine ⟨r,hr,hstep.trans_le hsteps,?_,?_,(htape _).trans hinput,
    (hhead _).trans hihead,(htape _).trans hW,(hhead _).trans hWhead⟩
  · intro i
    by_cases he : ∃ j,RecoveryBoundedColdGraph.slots j=i
    · obtain ⟨j,rfl⟩:=he
      exact hselhead j
    · have hn : ∀ j,RecoveryBoundedColdGraph.slots j≠i:=by simpa only [not_exists] using he
      exact (hkeep _ (supplier_away_graph source k d i hn)).1
  · intro i
    by_cases he : ∃ j,RecoveryBoundedColdGraph.slots j=i
    · obtain ⟨j,rfl⟩:=he
      exact (hseltape j).trans (RecoveryBoundedColdGraph.projection [] _ j).symm
    · have hn : ∀ j,RecoveryBoundedColdGraph.slots j≠i:=by simpa only [not_exists] using he
      have hz:=RecoveryBoundedColdGraph.other [] (fun _=>[]) (RecoveryBoundedColdSuppliers.output source k d CH Cpad code x W) i hn
      rw [RecoveryBoundedColdGraph.constant] at hz
      exact ((hkeep _ (supplier_away_graph source k d i hn)).2.trans
        (input_graph source k d (frame x++frame bound) W i)).trans hz

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph
