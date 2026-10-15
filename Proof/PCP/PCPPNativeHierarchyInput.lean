import Proof.PCP.PCPPNativeHierarchyLayout

/-! Original compound request through the same-source hierarchy and retained
normalization streams. The physically extracted oracle is retained head0. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
open LocalBitMultitape RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : RepairSource.ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def projected {s : ℕ} (k : ℕ) (out : Configuration (tapes source k) s) :
    Configuration (HierarchyStreams.tapes source k) 1 :=
  ⟨0,out.heads ∘ hierarchySlots source k,out.tapes ∘ hierarchySlots source k⟩
theorem fields_projected {s t : ℕ} (k CH Cpad : ℕ) (code x bound : List Bool)
    (out : Configuration (tapes source k) s) (prior : Configuration (HierarchyStreams.tapes source k) t)
    (hh : ∀ i,out.heads (hierarchySlots source k i)=prior.heads i)
    (ht : ∀ i,out.tapes (hierarchySlots source k i)=prior.tapes i)
    (hf : HierarchyStreams.Fields source k CH Cpad code x bound prior) :
    HierarchyStreams.Fields source k CH Cpad code x bound (projected source k out) := by
  exact ⟨(ht _).trans hf.input,(hh _).trans hf.inputHead,
    (ht _).trans hf.width,(hh _).trans hf.widthHead,
    (ht _).trans hf.queries,(hh _).trans hf.queriesHead,
    (ht _).trans hf.queryStream,(hh _).trans hf.queryStreamHead,
    (ht _).trans hf.queryCount,(hh _).trans hf.queryCountHead,
    (ht _).trans hf.clauseStream,(hh _).trans hf.clauseStreamHead,
    (ht _).trans hf.clauseCount,(hh _).trans hf.clauseCountHead⟩

theorem raw_run (k CH Cpad : ℕ) (code x bound oracle : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ result,run (machine source k CH Cpad code) (budget source k CH Cpad code x bound oracle)
      (input source k (frame x++frame bound) oracle)=some result ∧
      result.steps ≤ budget source k CH Cpad code x bound oracle ∧
      HierarchyStreams.Fields source k CH Cpad code x bound (projected source k result.final) ∧
      (∀ j : Fin 4,j.val≠1 → result.final.heads (loadSlots source k j)=0 ∧
        result.final.tapes (loadSlots source k j)=PCPPNativeInputFields.output (frame x++frame bound) oracle j) := by
  obtain ⟨first,hfirst,firstHeads,firstTapes,firstSteps⟩ :=
    (PCPPNativeInputFields.ready (frame x++frame bound) oracle).focus_at
      (loadSlots source k) (load_injective source k) (fun _ => 0)
      (input source k (frame x++frame bound) oracle)
      (load_input source k (frame x++frame bound) oracle) (by intro j; rfl)
  obtain ⟨prior,hprior,priorSteps,priorFields⟩ := HierarchyStreams.scalar_run source k CH Cpad code x bound hpad
  obtain ⟨last,hlast,_,lastSteps,lastHeads,lastTapes,lastKeep⟩ := RecoveryFocus.dock
    (hierarchySlots source k) (hierarchy_injective source k) (HierarchyStreams.machine source k CH Cpad code)
    _ first.final.heads first.final.tapes _
    (by intro j; rw [firstHeads]; rfl)
    (by intro j; rw [firstTapes]; exact hierarchy_input source k (frame x++frame bound) oracle j)
    prior hprior
  let result := Composition.joinedReceipt first last
  have hr := Composition.run_join (load source k) (hierarchy source k CH Cpad code)
    _ _ _ first last hfirst hlast
  refine ⟨result,hr,?_,?_,?_⟩
  · change first.steps+1+last.steps ≤ _
    unfold budget
    rw [firstSteps,lastSteps]
    omega
  · apply fields_projected source k CH Cpad code x bound result.final prior.final
    · exact lastHeads
    · exact lastTapes
    · exact priorFields
  · intro j hj
    have hk := lastKeep (loadSlots source k j) (hierarchy_away source k j hj)
    constructor
    · exact hk.1.trans (congrFun firstHeads _)
    · exact hk.2.trans ((congrFun firstTapes _).trans (loaded_local source k (frame x++frame bound) oracle j))

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
