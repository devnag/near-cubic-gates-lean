import Proof.CaseAnalysis.FinalRowFrameJoin

/-! The actual warm row at one caller-produced capacity shared by every label.
The extra inequality only enlarges its paid rewind/reset capacity. It neither
allocates the entry bank nor changes the estimator, table, or denominator.
Paper A.3 and C.10: row preparation is charged once per external label. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowCommonCapacity
open LocalBitMultitape RepairRepresentation RepairOrdinary
open RepairOrdinary.MatrixScoreBatch RepairOrdinary.CloseoutRowsEstimator
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairOrdinary.C10RowFrameJoin
open ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q D : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) :=
  WarmReuse.entry (producer a) (Warm.machine a) D
    (Warm.input (producer a) row C Q q denominator select) out

noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q D : ℕ) :=
  Reuse.budget (Warm.budget a row Q) (scalarWidth (EquationRow.request row) Q) D

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q D : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U * (EquationRow.request row).U),
      Int.ModEq ((2 : ℤ) ^ Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row))
          i.divNat i.modNat) (f i.divNat i.modNat))
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) : ∃ r,
    runFrom (WarmActual.machine a) (budget a row Q D)
      (entry a row C Q D q denominator select out) = some r ∧
      r.steps ≤ 4*D + 40*scalarWidth (EquationRow.request row) Q + 64 ∧
      r.final.heads = (fun i => if i = Reuse.output (producer a) then
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length else 0) ∧
      r.final.tapes (Reuse.output (producer a)) = out ++
        Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      (∀ i, r.final.tapes (Reuse.work (producer a) i) = List.replicate D false) ∧
      r.final.tapes (Reuse.driver (producer a)) = List.replicate D true ∧
      r.final.tapes (Reuse.log (producer a)) = List.replicate (D+1) false := by
  obtain ⟨source, hs, ht, _⟩ := Warm.run a row C Q q denominator f select hQ hf hc
  have hb := Driver.fuel_bound a row C Q hC hQ
  have he := Warm.split_budget a row C Q
  have hsteps := runFrom_steps_le _ _ _ _ hs
  apply WarmReuse.run (producer a) (Warm.machine a) _ (Warm.budget a row Q)
    (scalarWidth (EquationRow.request row) Q) D q _ denominator out source hs ht
  · omega
  · exact (Driver.append_bound a row C Q hQ).trans (Nat.add_le_add_right hD 1)
  · exact fun i => (InputSupport.warm a row C Q q denominator select hC hQ i).trans hD

theorem bank_step (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q D : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2 ^ Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U * (EquationRow.request row).U),
      Int.ModEq ((2 : ℤ) ^ Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row))
          i.divNat i.modNat) (f i.divNat i.modNat))
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) :
    Step (WarmActual.machine a) (budget a row Q D)
      (entry a row C Q D q denominator select out).heads
      (entry a row C Q D q denominator select out).tapes
      (bankHeads (producer a)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator))
      (exitTapes (producer a) D (Warm.input (producer a) row C Q q denominator select)
        (out ++ Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator)) := by
  obtain ⟨r, hr, _, hheads, hout, hwork, hdrv, hlog⟩ :=
    run a row C Q D q denominator f select out hC hQ hf hc hD
  have hnat := WarmActual.native_run a (budget a row Q D) _ r hr
  have hcap := WarmActual.capacity_run a (budget a row Q D) _ r hr
  change runFrom (WarmActual.machine a) (budget a row Q D)
    ⟨(WarmActual.machine a).start, _, _⟩ = some r at hr
  refine ⟨r, hr, ?_, ?_, runFrom_steps_le _ _ _ _ hr⟩
  · rw [hheads]; rfl
  · funext i
    rcases bank_cover (producer a) i with h | h | h | h | h | ⟨j, h⟩
    · subst h; rw [hout, exitTapes_output]
    · subst h; rw [hdrv, exitTapes_driver]
    · subst h; rw [hlog, exitTapes_log]
    · subst h
      rw [hnat, exitTapes_native]
      change (WarmReuse.entry (producer a) (Warm.machine a) D
        (Warm.input (producer a) row C Q q denominator select) out).tapes
          (Reuse.old (producer a) (NativeReadOnly.slot (producer a))) = _
      rw [entry_old, padded_retained]
      exact Or.inl rfl
    · subst h
      rw [hcap, exitTapes_capacity]
      change (WarmReuse.entry (producer a) (Warm.machine a) D
        (Warm.input (producer a) row C Q q denominator select) out).tapes
          (Reuse.old (producer a) (Retained.capacity (producer a))) = _
      rw [entry_old, padded_retained]
      exact Or.inr rfl
    · subst h; rw [hwork, exitTapes_work]

end NearCubicWires.RepairSource.CloseoutFinal.C10RowCommonCapacity
