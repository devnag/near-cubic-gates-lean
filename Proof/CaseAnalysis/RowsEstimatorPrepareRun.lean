import Proof.CaseAnalysis.RowsEstimatorPreparePad
import Proof.CaseAnalysis.RowsEstimatorPrepareCopy

/-! Literal original Warm input from the scanned prefix and seven retained fields,
with both physical D passes and their controller handoff paid. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem exact_bound {t s n : ℕ} {worker : Machine t s} {A B : Fin t → List Bool}
    (h : ReadyRun worker n A B) : ClockJoin.ReadyRun worker n A B := by
  obtain ⟨r,hr,ht,hh,hs⟩:=h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem ready (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p) :
    let p:=CompetitorCrossScheduler.producer a
    let D:=Driver.value a row.d row.p row.cuts.length C
    let fields:=WarmFields.words row Q q denominator select
    ClockJoin.ReadyRun (machine p) (4*D+9)
      (data p (WarmFields.bare p row C) D 0 fields)
      (data p (WarmReuse.padded p D (Warm.input p row C Q q denominator select)) D (D+1) fields) := by
  dsimp only
  let p:=CompetitorCrossScheduler.producer a
  let D:=Driver.value a row.d row.p row.cuts.length C
  let fields:=WarmFields.words row Q q denominator select
  have hp:=pad_ready p (WarmFields.bare p row C) D fields
  have hc:=copy_ready p (WarmReuse.padded p D (WarmFields.bare p row C)) D fields
    (WarmFields.padded_field p row C D) (WarmFields.bounded a row C Q q denominator select hC hQ)
  rw [WarmFields.padded_installed] at hc
  have h:=ClockJoin.join (pad p) (copy p) (2*D+4) (2*D+4) _ _ _ (exact_bound hp) (exact_bound hc)
  have he : 2*D+4+1+(2*D+4)=4*D+9:=by omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
