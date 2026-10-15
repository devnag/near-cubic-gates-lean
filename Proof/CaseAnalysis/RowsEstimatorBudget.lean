import Proof.CaseAnalysis.CloseoutRowsEstimatorCold

/-! A coarse additive preprocessing envelope in the actual retained row
scalars and literal cut-byte length. It has no external-row cardinality or
columnwise size assumption, and introduces no Williams table factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scale (row : EquationRow.Input) (C : ℕ):=
  row.d+row.p+row.cuts.length+(Header.stream row).length+C+1

theorem header_scalar (n : ℕ) : EquationHeaderAppend.budget n≤200*(n+1)^2:=by
  have hn:natBitLength n≤n+1:=by
    unfold natBitLength
    exact Nat.succ_le_succ (Nat.log_le_self 2 n)
  unfold EquationHeaderAppend.budget
  nlinarith

theorem budget_bound (row : EquationRow.Input) (C : ℕ) :
    budget row C≤10000*(scale row C)^2:=by
  let X:=scale row C
  have hx:1≤X:=by unfold X scale;omega
  have hd:row.d+1≤X:=by unfold X scale;omega
  have hp:row.p+1≤X:=by unfold X scale;omega
  have hg:row.cuts.length+1≤X:=by unfold X scale;omega
  have hl:(Header.stream row).length≤X:=by unfold X scale;omega
  have hC:C≤X:=by unfold X scale;omega
  have hw:Fields.w row.d row.odd≤2*row.d:=Nat.sub_le _ _
  have hfields:Fields.budget row.d row.odd≤14*X+33:=by
    unfold Fields.budget
    omega
  have hn:Scan.countFields row≤2*X+2:=by
    unfold Scan.countFields
    omega
  have hm:=Nat.mul_le_mul (by omega:row.cuts.length≤X)
    (by omega:2*Scan.countFields row+3≤4*X+7)
  have hscan:Scan.ticks row≤4*X^2+8*X+2:=by
    change (Header.stream row).length+row.cuts.length*(2*Scan.countFields row+3)+2≤_
    nlinarith
  have hsingle (n : ℕ) (h:n+1≤X):EquationHeaderAppend.budget n≤200*X^2:=by
    have hb:=header_scalar n
    have hm:=Nat.mul_le_mul h h
    nlinarith
  have h0:=hsingle row.d hd
  have h1:=hsingle row.p hp
  have h2:=hsingle row.cuts.length hg
  have hheader:Header.budget row≤600*X^2+X+5:=by
    change (EquationHeaderAppend.budget row.d+1+EquationHeaderAppend.budget row.p+1+
      EquationHeaderAppend.budget row.cuts.length)+1+(Header.stream row).length+2≤_
    omega
  change budget row C≤10000*X^2
  unfold budget Framed.budget Prepare.budget Header.framedBudget
  nlinarith

theorem run_bound (row : EquationRow.Input) (C : ℕ) (hC:(Header.stream row).length≤C) : ∃ actual,
    runFrom machine (budget row C) (entry row C)=some actual ∧
    actual.final.tapes 66=frame (EquationRowRaw.source row) ∧
    actual.final.tapes 68=List.replicate C true ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤10000*(scale row C)^2:=by
  obtain ⟨actual,hr,h66,h68,hh,hs⟩:=run row C hC
  exact ⟨actual,hr,h66,h68,hh,hs.trans (budget_bound row C)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
