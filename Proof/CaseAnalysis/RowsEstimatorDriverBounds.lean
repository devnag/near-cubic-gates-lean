import Proof.CaseAnalysis.RowsEstimatorScanned

/-! Scalar formula for the paid reset driver. Its only varying arguments
are the actual scanner counts d,p,G and retained native C. Table size enters
once, and the native capacity enters linearly. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Driver
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tableCoefficient (a : WilliamsAlgorithm) :=
  4*2^(CompetitorCrossScheduler.exponent a)*(CompetitorCountTableRecord.coefficient a+1)
noncomputable def tableValue (a : WilliamsAlgorithm) (d p : ℕ) :=
  tableCoefficient a*(2^d)^2*(d+p+1)^(CompetitorCrossScheduler.exponent a)
noncomputable def value (a : WilliamsAlgorithm) (d p G C : ℕ) :=
  64*(C+1)+2000000*(d+p+G+1)^3+tableValue a d p

theorem table_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) :
    CompetitorCountTableRecord.envelope a (EquationRow.request row)≤tableValue a row.d row.p := by
  let U:=2^row.d
  let S:=row.d+row.p+1
  let e:=CompetitorCrossScheduler.exponent a
  let c:=CompetitorCountTableRecord.coefficient a
  have hU : 1≤U:=Nat.one_le_pow _ _ (by decide)
  have hS : 1≤S:=by unfold S;omega
  change c*(U+1)^2*(row.d+(row.p+1)+1)^e≤4*2^e*(c+1)*U^2*S^e
  calc
    c*(U+1)^2*(row.d+(row.p+1)+1)^e ≤ c*(2*U)^2*(2*S)^e := by
      gcongr <;>omega
    _ = 4*2^e*c*U^2*S^e := by simp only [mul_pow];ring
    _ ≤ 4*2^e*(c+1)*U^2*S^e := by gcongr;omega

theorem fuel_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    Whole.budget a row C Q+1≤value a row.d row.p row.cuts.length C := by
  have h:=whole_linear a row C Q hC hQ
  have ht:=table_bound a row
  unfold linearFuel EquationRowRaw.mass at h
  unfold value
  omega

theorem append_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (hQ : Q≤(EquationRow.request row).p) :
    20*CompetitorSelectedCount.scalarWidth (EquationRow.request row) Q+27≤
      value a row.d row.p row.cuts.length C+1 := by
  have hb:=CompetitorSelectedCount.scalar_width_bound (EquationRow.request row) Q hQ
  change CompetitorSelectedCount.scalarWidth (EquationRow.request row) Q≤4*(row.d+(row.p+1)+1) at hb
  have hm : 1≤row.d+row.p+row.cuts.length+1 := by omega
  have hpow : row.d+row.p+row.cuts.length+1≤(row.d+row.p+row.cuts.length+1)^3 :=
    Nat.le_self_pow (by decide) _
  unfold value
  omega

theorem cold_input_bound (row : EquationRow.Input) (C : ℕ) (i : Fin 70) (hi : i≠52) :
    (Cold.input row C i).length≤C+row.d+row.p+1 := by
  fin_cases i
  all_goals first | exact False.elim (hi rfl) | skip
  all_goals simp [Cold.input,Framed.input,Framed.extend,Prepare.input,Fin.addCases]
  all_goals omega

theorem scanned_support (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ)
    (hC : (Header.stream row).length≤C) (i : Fin 70) (hi : i≠52) :
    (Scanned.output row C i).length≤value a row.d row.p row.cuts.length C := by
  obtain ⟨r,hr,rt,_rh,rs⟩:=Scanned.run row C hC
  have hc:=cold_linear row C hC
  have ht:=cold_input_bound row C i hi
  have hs : Scanned.budget row C≤Cold.budget row C := by
    unfold Scanned.budget Cold.budget Framed.budget
    omega
  have hstart : (Scanned.entry row C).heads i=0 := by
    change Cold.heads row i=0
    exact if_neg hi
  have hm : 1≤EquationRowRaw.mass row := by unfold EquationRowRaw.mass;omega
  have h12 : EquationRowRaw.mass row≤(EquationRowRaw.mass row)^2 := by
    simpa only [pow_two] using Nat.le_mul_self (EquationRowRaw.mass row)
  have h23 : (EquationRowRaw.mass row)^2≤(EquationRowRaw.mass row)^3 := by
    nlinarith [Nat.mul_le_mul_left ((EquationRowRaw.mass row)^2) hm]
  have hcap : r.steps+1≤value a row.d row.p row.cuts.length C := by
    unfold value
    unfold EquationRowRaw.mass at hc hm h12 h23
    omega
  have hin : ((Scanned.entry row C).tapes i).length≤value a row.d row.p row.cuts.length C := by
    change (Cold.input row C i).length≤_
    unfold value
    unfold EquationRowRaw.mass at hm h12 h23
    omega
  have hout:=CloseoutRowsProjectionReset.scratch_support Scanned.machine (Scanned.budget row C)
    (value a row.d row.p row.cuts.length C) _ r hr i hstart hin hcap
  rw [rt] at hout
  exact hout

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Driver
