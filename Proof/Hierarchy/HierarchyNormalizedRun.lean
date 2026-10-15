import Proof.Hierarchy.HierarchyNormalizedBounds
import Proof.Hierarchy.HierarchyClauseRun

/-! The actual common source/query/clause prefix supplies all four fields
to the one fixed outer encoder. No field is installed at an uncharged join. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem scalar_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r,runFrom (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (entry source k CH Cpad code x bound)=some r ∧
      r.final.tapes (output source k)=Codec.word (source.output (HierarchyStreams.request k CH Cpad code x))
        (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) ∧
      r.final.heads (output source k)=0 ∧ r.steps ≤ budget source k CH Cpad code x := by
  obtain ⟨p,hp,pt,ph,_ps⟩ := HierarchyClauses.clause_run source k CH Cpad code x bound hpad
  obtain ⟨r,hr,rt,rh,_rf,_old,_heads,rs⟩ := PCPOuterDock.dock_run
    (HierarchyClauses.machine source k CH Cpad code) (HierarchyClauses.fieldSlots source k)
    (HierarchyClauses.fieldSlots_injective source k) _ _ p hp
    (HierarchyClauses.words source k CH Cpad code x 0)
    (HierarchyClauses.words source k CH Cpad code x 1)
    (HierarchyClauses.words source k CH Cpad code x 2)
    (HierarchyClauses.words source k CH Cpad code x 3)
    (HierarchyClauses.suffixes source k CH Cpad code x 0)
    (HierarchyClauses.suffixes source k CH Cpad code x 1)
    (HierarchyClauses.suffixes source k CH Cpad code x 2)
    (HierarchyClauses.suffixes source k CH Cpad code x 3) ph
    (by intro j; fin_cases j <;> exact pt _)
  have he : Composition.leftConfig _ (TapeEmbedding.config
      (fun _ : Fin 129 => 0) (fun _ : Fin 129 => [])
      (HierarchyClauses.entry source k CH Cpad code x bound))=
      entry source k CH Cpad code x bound := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  refine ⟨r,?_,?_,rh,rs⟩
  · exact (congrArg (fun c => runFrom (machine source k CH Cpad code)
      (budget source k CH Cpad code x) c) he).symm.trans hr
  · exact rt.trans (HierarchyClauses.words_code source k CH Cpad code x)

theorem append_zero_heads (t e : ℕ) :
    (fun i => Fin.addCases (m:=t) (n:=e) (motive:=fun _ => ℕ)
      (fun _ => 0) (fun _ => 0) i)=(fun _ : Fin (t+e) => 0) := by
  funext i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

theorem append_blank_tapes (t e : ℕ) (ht : 0<t) (bits : List Bool) :
    (fun i => Fin.addCases (m:=t) (n:=e) (motive:=fun _ => List Bool)
      (SourceHandoff.sourceTapes bits) (fun _ => []) i)=
      (SourceHandoff.sourceTapes bits : Fin (t+e) → List Bool) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [SourceHandoff.sourceTapes]
  · simp [SourceHandoff.sourceTapes,Nat.ne_of_gt ht]

theorem three_heads {t s : ℕ} (e₁ e₂ e₃ : ℕ) (c : Configuration t s)
    (hc : c.heads=(fun _ => 0)) :
    (TapeEmbedding.config (fun _ : Fin e₃ => 0) (fun _ : Fin e₃ => [])
      (TapeEmbedding.config (fun _ : Fin e₂ => 0) (fun _ : Fin e₂ => [])
        (TapeEmbedding.config (fun _ : Fin e₁ => 0) (fun _ : Fin e₁ => []) c))).heads=(fun _ => 0) := by
  simp only [TapeEmbedding.config]
  rw [hc,append_zero_heads,append_zero_heads,append_zero_heads]

theorem three_tapes {t s : ℕ} (e₁ e₂ e₃ : ℕ) (ht : 0<t) (bits : List Bool) (c : Configuration t s)
    (hc : c.tapes=SourceHandoff.sourceTapes bits) :
    (TapeEmbedding.config (fun _ : Fin e₃ => 0) (fun _ : Fin e₃ => [])
      (TapeEmbedding.config (fun _ : Fin e₂ => 0) (fun _ : Fin e₂ => [])
        (TapeEmbedding.config (fun _ : Fin e₁ => 0) (fun _ : Fin e₁ => []) c))).tapes=
      SourceHandoff.sourceTapes bits := by
  simp only [TapeEmbedding.config]
  rw [hc,append_blank_tapes _ _ ht,append_blank_tapes _ _ (by omega),append_blank_tapes _ _ (by omega)]

theorem entry_heads (k CH Cpad : ℕ) (code x bound : List Bool) :
    (entry source k CH Cpad code x bound).heads=(fun _ => 0) := by
  exact three_heads 128 309 129 (initialConfiguration (HierarchyStreams.machine source k CH Cpad code)
    (SourceHandoff.sourceTapes (frame x++frame bound))) rfl

theorem entry_tapes (k CH Cpad : ℕ) (code x bound : List Bool) :
    (entry source k CH Cpad code x bound).tapes=SourceHandoff.sourceTapes (frame x++frame bound) := by
  have ht : 0<HierarchyStreams.tapes source k := by unfold HierarchyStreams.tapes; omega
  exact three_tapes 128 309 129 ht (frame x++frame bound)
    (initialConfiguration (HierarchyStreams.machine source k CH Cpad code)
      (SourceHandoff.sourceTapes (frame x++frame bound))) rfl

theorem raw_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r,run (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (SourceHandoff.sourceTapes (frame x++frame bound))=some r ∧
      r.final.tapes (output source k)=Codec.word (source.output (HierarchyStreams.request k CH Cpad code x))
        (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x) ∧
      r.final.heads (output source k)=0 ∧ r.steps ≤ budget source k CH Cpad code x := by
  obtain ⟨r,hr,rt,rh,rs⟩ := scalar_run source k CH Cpad code x bound hpad
  have he : entry source k CH Cpad code x bound=
      initialConfiguration (machine source k CH Cpad code) (SourceHandoff.sourceTapes (frame x++frame bound)) := by
    apply configuration_ext
    · rfl
    · exact entry_heads source k CH Cpad code x bound
    · exact entry_tapes source k CH Cpad code x bound
  rw [he] at hr
  exact ⟨r,hr,rt,rh,rs⟩

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyNormalized
