import Proof.CaseAnalysis.RowsEstimatorWhole

/-! The exact estimator fuel has one linear native-capacity term and one
Williams table term. The metadata polynomial never contains the native C. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cold_linear (row : EquationRow.Input) (C : ℕ)
    (hC : (Header.stream row).length ≤ C) :
    Cold.budget row C ≤ 10*C+10000*(EquationRowRaw.mass row)^2 := by
  let X := EquationRowRaw.mass row
  have hx : 1 ≤ X := by unfold X EquationRowRaw.mass; omega
  have hd : row.d+1 ≤ X := by unfold X EquationRowRaw.mass; omega
  have hp : row.p+1 ≤ X := by unfold X EquationRowRaw.mass; omega
  have hg : row.cuts.length+1 ≤ X := by unfold X EquationRowRaw.mass; omega
  have hw : Fields.w row.d row.odd ≤ 2*row.d := Nat.sub_le _ _
  have hfields : Fields.budget row.d row.odd ≤ 14*X+33 := by
    unfold Fields.budget
    omega
  have hn : Scan.countFields row ≤ 2*X+2 := by
    unfold Scan.countFields
    omega
  have hm := Nat.mul_le_mul (by omega : row.cuts.length ≤ X)
    (by omega : 2*Scan.countFields row+3 ≤ 4*X+7)
  have hscan : Scan.ticks row ≤ C+4*X^2+7*X+2 := by
    change (Header.stream row).length+row.cuts.length*(2*Scan.countFields row+3)+2 ≤ _
    nlinarith
  have hsingle (n : ℕ) (h : n+1 ≤ X) : EquationHeaderAppend.budget n ≤ 200*X^2 := by
    have hb := Cold.header_scalar n
    have hh := Nat.mul_le_mul h h
    nlinarith
  have h0 := hsingle row.d hd
  have h1 := hsingle row.p hp
  have h2 := hsingle row.cuts.length hg
  have hheader : Header.budget row ≤ 600*X^2+C+5 := by
    change (EquationHeaderAppend.budget row.d+1+EquationHeaderAppend.budget row.p+1+
      EquationHeaderAppend.budget row.cuts.length)+1+(Header.stream row).length+2 ≤ _
    omega
  change Cold.budget row C ≤ 10*C+10000*X^2
  unfold Cold.budget Framed.budget Prepare.budget Header.framedBudget
  nlinarith [Nat.le_mul_self X]

theorem source_linear (row : EquationRow.Input) (C : ℕ)
    (hC : (Header.stream row).length ≤ C) :
    (EquationRowRaw.source row).length ≤ C+2*EquationRowRaw.mass row+8 := by
  have hn (n : ℕ) : natBitLength n ≤ n+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hd := hn row.d
  have hp := hn row.p
  have hg := hn row.cuts.length
  have he : EquationRowRaw.source row =
      (natWord row.d++natWord row.p++natWord row.cuts.length)++row.odd::Header.stream row := by
    simp only [EquationRowRaw.source,EquationHeaderRead.word,EquationHeaderRead.header,
      EquationRowCuts.stream,Header.stream,List.append_assoc]
  rw [he]
  simp only [List.length_append,List.length_cons,DecompositionSource.natWord_length]
  unfold EquationRowRaw.mass
  omega

noncomputable def linearFuel (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ) :=
  40*C+1000000*(EquationRowRaw.mass row)^3+
    CompetitorCountTableRecord.envelope a (EquationRow.request row)

theorem whole_linear (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p) :
    Whole.budget a row C Q+1 ≤ linearFuel a row C := by
  have hc := cold_linear row C hC
  have hs := source_linear row C hC
  have ht := CompetitorCountTableRecord.budget_bound a (EquationRow.request row) Q hQ
  have hx : 1 ≤ EquationRowRaw.mass row := by unfold EquationRowRaw.mass; omega
  have h12 : EquationRowRaw.mass row ≤ (EquationRowRaw.mass row)^2 := by
    simpa only [pow_two] using Nat.le_mul_self (EquationRowRaw.mass row)
  have h23 : (EquationRowRaw.mass row)^2 ≤ (EquationRowRaw.mass row)^3 := by
    nlinarith [Nat.mul_le_mul_left ((EquationRowRaw.mass row)^2) hx]
  unfold Whole.budget CloseoutRowsRawRecord.budget EquationRowFramed.uniformBudget linearFuel
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
