import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmFields

/-! The caller bank has exactly the seven checked metadata fields outside
the actual scanner output. This supplies the physical batch-copy target. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
open LocalBitMultitape MatrixScoreBatch RepairRepresentation CompetitorCountMask CompetitorSelectedCount
open CloseoutRowsEstimatorCoefficients RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_other (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (i : Fin (CompetitorCountTableRecord.tapes p)) :
    i.val≠0 → (∀ k,slots p k≠promote p i) →
      Table.input p (EquationRow.request row) Q row.odd q denominator
        (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select) i=[] := by
  unfold Table.input
  refine Fin.addCases (m:=CompetitorSelectedTable.tapes p) (n:=27) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left]
    unfold CompetitorSelectedTable.extend
    refine Fin.addCases (m:=CompetitorCountTable.tapes p) (n:=92) (fun k=>?_) (fun k=>?_) j
    · simp only [Fin.addCases_left]
      unfold CompetitorCountTable.input CompetitorCountTable.extend
      refine Fin.addCases (m:=CompetitorCountBanks.tapes p) (n:=124) (fun l=>?_) (fun l=>?_) k
      · simp only [Fin.addCases_left]
        unfold CompetitorCountBanks.input CompetitorCountBanks.extend
        refine Fin.addCases (m:=CompetitorCrossScheduler.tapes p) (n:=511) (fun m=>?_) (fun m=>?_) l
        · intro hz _
          have hz' : m.val≠0:=hz
          simp [CompetitorCrossScheduler.input,hz']
        · intro _ _
          simp
      · intro _ avoid
        by_cases h1 : l=1
        · subst l
          exact False.elim (avoid 0 rfl)
        by_cases h3 : l=3
        · subst l
          exact False.elim (avoid 1 rfl)
        simp [CompetitorCountTable.metadata,h1,h3]
    · intro _ avoid
      by_cases h0 : k=0
      · subst k
        exact False.elim (avoid 2 rfl)
      simp [CompetitorSelectedTable.extra,h0]
  · intro _ avoid
    by_cases h22 : j.val=22
    · have he : j=22:=Fin.ext h22
      subst j
      exact False.elim (avoid 3 rfl)
    by_cases h23 : j.val=23
    · have he : j=23:=Fin.ext h23
      subst j
      exact False.elim (avoid 4 rfl)
    by_cases h24 : j.val=24
    · have he : j=24:=Fin.ext h24
      subst j
      exact False.elim (avoid 5 rfl)
    by_cases h25 : j.val=25
    · have he : j=25:=Fin.ext h25
      subst j
      exact False.elim (avoid 6 rfl)
    simp [CountRequest.extra]

noncomputable def bare (p : Program) (row : EquationRow.Input) (C : ℕ) :=
  Warm.supplied p row C (fun _=>[])

theorem outside (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (i : Fin (WholePrefix.tapes p)) : (∀ k,slots p k≠i) →
      Warm.input p row C Q q denominator select i=bare p row C i := by
  unfold Warm.input Warm.supplied bare Warm.supplied
  refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (fun j=>?_) (fun j=>?_) i
  · intro _
    simp
  · intro avoid
    simp only [Fin.addCases_right,WholePrefix.extra]
    split_ifs with hz
    · rfl
    · unfold Record.input Consumer.input
      revert hz avoid
      refine Fin.addCases (m:=130) (n:=CompetitorCountTableRecord.tapes p) (fun k=>?_) (fun k=>?_) j
      · intro _ hz
        have hk : k≠0:=fun he=>hz (congrArg Fin.val he)
        simp [EquationRowFramed.input,hk]
      · intro avoid _
        simp only [Fin.addCases_right,Consumer.extra]
        split_ifs with hk
        · rfl
        · exact table_other p row Q q denominator select k hk avoid

theorem installed (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) :
    install (slots p) (bare p row C) (words row Q q denominator select)=
      Warm.input p row C Q q denominator select := by
  classical
  funext i
  by_cases hi : ∃ k,slots p k=i
  · obtain ⟨k,rfl⟩:=hi
    rw [install_slot _ (injective p)]
    exact (projected p row C Q q denominator select k).symm
  · have ho : ∀ k,slots p k≠i:=by simpa using hi
    rw [install_other _ _ _ _ ho]
    exact (outside p row C Q q denominator select i ho).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
