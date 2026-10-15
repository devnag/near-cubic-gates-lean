import Proof.CaseAnalysis.RowsEstimatorPreparedAny

/-! Execute paid preparation and the actual original Warm/reset/append consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last (a : WilliamsAlgorithm):=TapeEmbedding.machine 7 (WarmActual.machine a)
noncomputable def machine (a : WilliamsAlgorithm):=Composition.machine (WarmPrepare.machine (producer a)) (last a)
def startWith {t s u : ℕ} (first : Machine t s) (_last : Machine t u)
    (H : Fin t → ℕ) (A : Fin t → List Bool) := Composition.leftConfig u
      (⟨first.start,H,A⟩ : Configuration t s)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool):=
  let p:=producer a
  let D:=Driver.value a row.d row.p row.cuts.length C
  startWith (WarmPrepare.machine p) (last a) (WarmPrepare.heads p out)
    (WarmPrepare.live p (WarmPrepare.data p (WarmFields.bare p row C) D 0
      (WarmFields.words row Q q denominator select)) out)

noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  4*Driver.value a row.d row.p row.cuts.length C+9+1+WarmActual.budget a row C Q

def Result {s : ℕ} (p : Program) (worker : Machine (WarmPrepare.tapes p) s) (fuel : ℕ)
    (initial : Configuration (WarmPrepare.tapes p) s) (D b : ℕ) (out word : List Bool)
    (fields : Fin 7 → List Bool) : Prop := ∃ r,
  runFrom worker fuel initial=some r ∧ r.steps ≤ 8*D+40*b+74 ∧
    r.final.heads=WarmPrepare.heads p (out++word) ∧
    r.final.tapes (WarmPrepare.spare p)=out++word ∧
    (∀ i,r.final.tapes (WarmPrepare.work p i)=List.replicate D false) ∧
    r.final.tapes (WarmPrepare.driver p)=List.replicate D true ∧
    r.final.tapes (WarmPrepare.log p)=List.replicate (D+1) false ∧
    (∀ i,r.final.tapes (WarmPrepare.source p i)=fields i)

theorem prepare_entry (p : Program) (H : Fin (WarmPrepare.tapes p) → ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) :
    Composition.leftConfig 4 (⟨(WarmPrepare.pad p).start,H,A⟩ : Configuration (WarmPrepare.tapes p) 4)=
      (⟨(WarmPrepare.machine p).start,H,A⟩ : Configuration (WarmPrepare.tapes p) 8) := rfl

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    Result (producer a) (machine a) (budget a row C Q) (entry a row C Q q denominator select out)
      (Driver.value a row.d row.p row.cuts.length C) (scalarWidth (EquationRow.request row) Q) out
      (Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)
      (WarmFields.words row Q q denominator select) := by
  let p:=producer a
  let D:=Driver.value a row.d row.p row.cuts.length C
  let fields:=WarmFields.words row Q q denominator select
  obtain ⟨x,hx,xh,xt,xs⟩:=WarmPrepare.live_run a row C Q q denominator select out hC hQ
  rw [prepare_entry] at hx
  obtain ⟨y,hy,ys,yh,yt,yw,yd,yl⟩:=WarmActual.run a row C Q q denominator f select out hC hQ hf hc
  exact complete_any p (WarmPrepare.machine p) (WarmActual.machine a)
    (WarmActual.entry a row C Q q denominator select out) _ _
    (Warm.input p row C Q q denominator select) (WarmFields.bare p row C) D fields out _ x y hx xh xt xs
    (warm_entry p (Warm.machine a) _ D fields out) hy ys yh yt yw yd yl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
