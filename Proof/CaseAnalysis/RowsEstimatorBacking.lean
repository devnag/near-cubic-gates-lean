import Proof.CaseAnalysis.RowsEstimatorSparse

/-! Exact owned backing for the seven paid metadata copies. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_caps (p : Program) (D : ℕ) (i : Fin 7) : Reset.caps p D (slots p i)=D := by
  have hv:=slots_val p i
  unfold Reset.caps
  rw [hv]
  fin_cases i <;> simp <;> omega

theorem bare_promote (p : Program) (row : EquationRow.Input) (C : ℕ)
    (i : Fin (CompetitorCountTableRecord.tapes p)) : bare p row C (promote p i)=[] := by
  unfold bare Warm.supplied promote
  erw [Fin.addCases_right]
  simp [WholePrefix.extra]

theorem bare_field (p : Program) (row : EquationRow.Input) (C : ℕ) (i : Fin 7) :
    bare p row C (slots p i)=[] := by
  fin_cases i <;> exact bare_promote p row C _

theorem padded_field (p : Program) (row : EquationRow.Input) (C D : ℕ) (i : Fin 7) :
    WarmReuse.padded p D (bare p row C) (slots p i)=List.replicate D false := by
  unfold WarmReuse.padded
  rw [field_caps,bare_field]
  simp [ZeroPadding.pad]

theorem padded_installed (p : Program) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) :
    install (slots p) (WarmReuse.padded p D (bare p row C))
      (fun i=>ZeroPadding.pad D (words row Q q denominator select i))=
      WarmReuse.padded p D (Warm.input p row C Q q denominator select) := by
  classical
  funext i
  by_cases hit : ∃ k,slots p k=i
  · obtain ⟨k,rfl⟩:=hit
    rw [install_slot _ (injective p)]
    unfold WarmReuse.padded
    rw [field_caps,projected]
  · have ho : ∀ k,slots p k≠i:=by simpa using hit
    rw [install_other _ _ _ _ ho]
    unfold WarmReuse.padded
    rw [outside p row C Q q denominator select i ho]

theorem bounded (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) (i : Fin 7) :
    (words row Q q denominator select i).length≤Driver.value a row.d row.p row.cuts.length C := by
  rw [← projected (CompetitorCrossScheduler.producer a) row C Q q denominator select i]
  exact InputSupport.warm a row C Q q denominator select hC hQ _

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
