import Proof.CaseAnalysis.CloseoutRowsEstimatorWarm
import Proof.CaseAnalysis.RowsEstimatorDriverBounds

/-! Literal support of the actual estimator entry. The matrix/source
placeholders are removed by their paid prefixes; only Q, parity, mask and
four fixed-width coefficient/normalization fields remain in the caller bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.InputSupport
open LocalBitMultitape RepairRepresentation MatrixScoreBatch CompetitorSelectedCount RecoveryRootRound
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem extra_bound {m n : ℕ} (A : Fin m→List Bool) (B : Fin n→List Bool) (H : ℕ)
    (ha : ∀ i,i.val≠0→(A i).length≤H) (hb : ∀ i,(B i).length≤H) :
    ∀ i : Fin (m+n),i.val≠0→((Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool) A B) i).length≤H := by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j hj=>?_) (fun j _=>?_) i
  · simpa only [Fin.addCases_left] using ha j hj
  · simpa only [Fin.addCases_right] using hb j

theorem table (p : Program) (r : Request) (Q : ℕ) (odd : Bool)
    (q : CompetitorValidity.Estimate) (denominator : ℕ) (xs : List (Bool × ℕ)) :
    ∀ i,i.val≠0→(Table.input p r Q odd q denominator xs i).length≤Q+xs.length+4*scalarWidth r Q+8 := by
  unfold Table.input
  apply extra_bound
  · unfold CompetitorSelectedTable.extend
    apply extra_bound
    · unfold CompetitorCountTable.input CompetitorCountTable.extend
      apply extra_bound
      · unfold CompetitorCountBanks.input CompetitorCountBanks.extend
        apply extra_bound
        · intro i hi;simp [CompetitorCrossScheduler.input,hi]
        · intro i;simp
      · intro i
        unfold CompetitorCountTable.metadata
        split_ifs <;>simp;omega
    · intro i
      unfold CompetitorSelectedTable.extra
      split_ifs <;>simp [CompetitorCountMask.mask_length];omega
  · intro i
    fin_cases i
    all_goals simp [CountRequest.extra,CompetitorRationalDecision.width,frame_length,SignedSortKey.binary_length]
    all_goals omega

theorem record (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    ∀ i,i.val≠0→(Record.input p row Q q denominator select i).length≤
      Q+(EquationRow.request row).U^2+4*scalarWidth (EquationRow.request row) Q+8 := by
  let xs:=CompetitorSelectedCells.cells row.odd (fun _ _=>0) select
  have hx:=CompetitorSelectedCells.cells_length row.odd (fun _ _=>0) select
  unfold Record.input Consumer.input
  apply extra_bound
  · intro i hi
    have hz : i≠0:=fun he=>hi (congrArg Fin.val he)
    simp [EquationRowFramed.input,hz]
  · intro i
    unfold Consumer.extra
    split_ifs with hi
    · simp
    · have h:=table p (EquationRow.request row) Q row.odd q denominator xs i hi
      change _≤Q+(EquationRow.request row).U^2+4*scalarWidth (EquationRow.request row) Q+8
      dsimp [xs] at h
      nlinarith

theorem cells_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) :
    (EquationRow.request row).U^2≤Driver.tableValue a row.d row.p := by
  have hc : 1≤Driver.tableCoefficient a := by
    apply Nat.succ_le_of_lt
    unfold Driver.tableCoefficient
    positivity
  have hp : 1≤(row.d+row.p+1)^(CompetitorCrossScheduler.exponent a):=Nat.one_le_pow _ _ (by omega)
  change (2^row.d)^2≤_
  unfold Driver.tableValue
  nlinarith [Nat.mul_le_mul_right ((2^row.d)^2) hc,
    Nat.mul_le_mul_left (Driver.tableCoefficient a*(2^row.d)^2) hp]

theorem metadata_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (hQ : Q≤(EquationRow.request row).p) :
    Q+(EquationRow.request row).U^2+4*scalarWidth (EquationRow.request row) Q+8≤
      Driver.value a row.d row.p row.cuts.length C := by
  have hb:=scalar_width_bound (EquationRow.request row) Q hQ
  change scalarWidth (EquationRow.request row) Q≤4*(row.d+(row.p+1)+1) at hb
  change Q≤row.p+1 at hQ
  have hu:=cells_bound a row
  have hpow : row.d+row.p+row.cuts.length+1≤(row.d+row.p+row.cuts.length+1)^3 :=
    Nat.le_self_pow (by decide) _
  unfold Driver.value
  omega

theorem warm (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    ∀ i,(Warm.input (CompetitorCrossScheduler.producer a) row C Q q denominator select i).length≤
      Driver.value a row.d row.p row.cuts.length C := by
  intro i
  unfold Warm.input Warm.supplied
  refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (CompetitorCrossScheduler.producer a))
    (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left]
    by_cases hj : j=52
    · subst j
      have ht : Scanned.output row C 52=Header.stream row := by
        change Prepare.output row 52=_
        exact (install_slot Prepare.scanSlots (by decide) _ _ 0).trans (by rfl)
      rw [ht]
      unfold Driver.value
      omega
    · exact Driver.scanned_support a row C hC j hj
  · simp only [Fin.addCases_right,WholePrefix.extra]
    split_ifs with hj
    · simp
    · exact (record (CompetitorCrossScheduler.producer a) row Q q denominator select j hj).trans
        (metadata_bound a row C Q hQ)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.InputSupport
