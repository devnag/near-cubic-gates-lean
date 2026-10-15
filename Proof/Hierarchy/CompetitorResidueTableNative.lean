import Proof.Hierarchy.CompetitorResidueTableFields

/-! The accepted signed residue cell consumes the two physically loaded
operands, while the full P/N source head remains at its current cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def nativeProgram := TapeEmbedding.machine 18 CompetitorResidueCell.machine
def extraHeads (pos : ℕ) : Fin 18 → ℕ := fun i => if i.val=10 then pos else 0

theorem loaded_keep (w a b : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 27)
    (hi : i=4 ∨ i=8 ∨ i=9 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22) :
    loaded w a b ambient i=ambient i := by
  have h0 : i≠0 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have h1 : i≠1 := by rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp only [loaded,firstLoaded,Function.update_of_ne h0,Function.update_of_ne h1]
  exact clean_keep w ambient i hi

theorem loaded_native (w q a b : ℕ) (source output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w q source output ambient) (i : Fin 9) :
    loaded w a b ambient (i.castAdd 18)=paddedInput w q a b output i := by
  have h4 := (clean_keep w ambient 4 (by simp)).trans h.crop
  have h8 := (clean_keep w ambient 8 (by simp)).trans h.output
  have h2 := clean_work w ambient 2
  have h3 := clean_work w ambient 3
  have h5 := clean_work w ambient 4
  have h6 := clean_work w ambient 5
  have h7 := clean_work w ambient 6
  change clean w ambient 2=List.replicate (capacity w) false at h2
  change clean w ambient 3=List.replicate (capacity w) false at h3
  change clean w ambient 5=List.replicate (capacity w) false at h5
  change clean w ambient 6=List.replicate (capacity w) false at h6
  change clean w ambient 7=List.replicate (capacity w) false at h7
  fin_cases i
  all_goals simp [loaded,firstLoaded,paddedInput,padding,CompetitorResidueCell.input,
    CompetitorSignedResidue.input,ZeroPadding.pad,Fin.addCases,h2,h3,h4,h5,h6,h7,h8]

theorem native_run (w q a b pos : ℕ) (source output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w q source output ambient) (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ r,runFrom nativeProgram (CompetitorResidueCell.budget w q)
      (cfg nativeProgram.start pos output.length (loaded w a b ambient))=some r ∧
      r.steps≤CompetitorResidueCell.budget w q ∧
      r.final.heads=heads pos (output++binary q (CompetitorSignedResidue.residue w q a b)).length ∧
      Store w q source (output++binary q (CompetitorSignedResidue.residue w q a b)) r.final.tapes := by
  obtain ⟨base,out,hr,hs,hh,ht,h8,h4,hbound⟩ := padded_cell_run w q a b output ha hb hq
  let extra : Fin 18 → List Bool := fun i => loaded w a b ambient (i.natAdd 9)
  have hrun := TapeEmbedding.run_embed CompetitorResidueCell.machine (extraHeads pos) extra _ _ base hr
  have hin : TapeEmbedding.config (extraHeads pos) extra
      (RecoveryCalls.restarted CompetitorResidueCell.machine (CompetitorResidueCell.heads output)
        (paddedInput w q a b output))=
      cfg nativeProgram.start pos output.length (loaded w a b ambient) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      refine Fin.addCases (m := 9) (n := 18) ?_ ?_ i
      · intro j
        simp only [TapeEmbedding.config,RecoveryCalls.restarted,cfg,Fin.addCases_left]
        exact (loaded_native w q a b source output ambient h j).symm
      · intro j
        simp only [TapeEmbedding.config,cfg,Fin.addCases_right,extra]
  rw [hin] at hrun
  refine ⟨TapeEmbedding.receipt (extraHeads pos) extra base,hrun,hs,?_,?_⟩
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,hh]
    funext i
    fin_cases i <;> rfl
  · constructor
    · exact (loaded_keep w a b ambient 9 (by simp)).trans h.width
    · exact (loaded_keep w a b ambient 20 (by simp)).trans h.widthCopy
    · exact (congrFun ht 4).trans h4
    · exact (loaded_keep w a b ambient 19 (by simp)).trans h.source
    · exact (congrFun ht 8).trans h8
    · exact (loaded_keep w a b ambient 21 (by simp)).trans h.erase
    · exact (loaded_keep w a b ambient 22 (by simp)).trans h.reset
    · intro i
      fin_cases i
      all_goals first
        | (change (base.final.tapes 0).length≤_; rw [ht]; exact hbound 0)
        | (change (base.final.tapes 1).length≤_; rw [ht]; exact hbound 1)
        | (change (base.final.tapes 2).length≤_; rw [ht]; exact hbound 2)
        | (change (base.final.tapes 3).length≤_; rw [ht]; exact hbound 3)
        | (change (base.final.tapes 5).length≤_; rw [ht]; exact hbound 5)
        | (change (base.final.tapes 6).length≤_; rw [ht]; exact hbound 6)
        | (change (base.final.tapes 7).length≤_; rw [ht]; exact hbound 7)
        | skip
      change (loaded w a b ambient 10).length≤capacity w
      simp only [loaded,firstLoaded,Function.update_of_ne (by decide : (10 : Fin 27)≠1),
        Function.update_of_ne (by decide : (10 : Fin 27)≠0)]
      rw [show clean w ambient 10=List.replicate (capacity w) false from clean_work w ambient 7]
      simp

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
