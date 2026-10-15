import Proof.CaseAnalysis.RowsRawRecord

/-! The executed raw-row printer is paid once. The same generated-gate
inequality required by the matrix request absorbs its cubic gate dependence
into a linear full-table factor; only short widths remain polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPrinterBudget
open RepairRepresentation MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cut_length (p : ℕ) (c : Cut) :
    (cutWord p c).length=(c.leftWeights.length+c.rightWeights.length+2)*(2*p+3) := by
  simp [cutWord,fields,List.length_flatMap]
  ring

theorem source_length (row : EquationRow.Input) :
    (EquationRowRaw.source row).length≤16*(row.cuts.length+1)*(row.d+row.p+1)^2 := by
  let H := row.d+row.p+1
  let G := row.cuts.length
  have hH : 1≤H := by dsimp [H]; omega
  have hH2 : H≤H^2 := by simpa only [pow_two] using Nat.le_mul_self H
  have h12 : 1≤H^2 := hH.trans hH2
  have hG : G≤G*H^2 := by simpa using Nat.mul_le_mul_left G h12
  have cb : ∀ c∈row.cuts,(cutWord row.p c).length≤6*H^2 := by
    intro c hc
    obtain ⟨hl,hr⟩ := row.lengths c hc
    have hright : c.rightWeights.length≤row.d := by omega
    rw [cut_length]
    have hfirst : c.leftWeights.length+c.rightWeights.length+2≤2*H := by dsimp [H]; omega
    have hsecond : 2*row.p+3≤3*H := by dsimp [H]; omega
    exact (Nat.mul_le_mul hfirst hsecond).trans_eq (by ring)
  have hb := RowBinLift.sum_le_length_mul (row.cuts.map (fun c => (cutWord row.p c).length))
    (6*H^2) (by intro n hn; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hn; exact cb c hc)
  simp only [List.length_map] at hb
  have hd : natBitLength row.d≤row.d+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hp : natBitLength row.p≤row.p+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hg : natBitLength G≤G+1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  simp only [EquationRowRaw.source,EquationHeaderRead.word,EquationHeaderRead.header,
    List.length_append,MatrixScoreRawGateBounds.natWord_length,List.length_cons,
    EquationRowCuts.stream,List.length_flatMap]
  change _≤16*(G+1)*H^2
  change (row.cuts.map (fun c => (cutWord row.p c).length)).sum≤G*(6*H^2) at hb
  change natBitLength row.cuts.length≤G+1 at hg
  dsimp only [H] at hH2 hG ⊢
  dsimp only [H] at hb
  nlinarith

theorem uniform_bound (row : EquationRow.Input) :
    EquationRowFramed.uniformBudget row≤625000*(row.cuts.length+1)^3*(row.d+row.p+1)^3 := by
  let H := row.d+row.p+1
  let G := row.cuts.length+1
  have hH : 1≤H := by dsimp [H]; omega
  have hG : 1≤G := by dsimp [G]; omega
  have hm : EquationRowRaw.mass row≤G*H := by dsimp [EquationRowRaw.mass,G,H]; nlinarith
  have hm3 := Nat.pow_le_pow_left hm 3
  rw [mul_pow] at hm3
  have hs := source_length row
  have hG3 : G≤G^3 := by simpa using Nat.pow_le_pow_right hG (by decide : 1≤3)
  have hH3 : H^2≤H^3 := Nat.pow_le_pow_right hH (by decide)
  have hprod := Nat.mul_le_mul hG3 hH3
  have hpos : 1≤G^3*H^3 := Nat.mul_pos (by positivity) (by positivity)
  change (EquationRowRaw.source row).length≤16*G*H^2 at hs
  change EquationRowFramed.uniformBudget row≤625000*G^3*H^3
  unfold EquationRowFramed.uniformBudget
  nlinarith

theorem gate_cube (s G : ℕ) (hg : G^100≤2^s) : (G+1)^3≤8*2^s := by
  by_cases hz : G=0
  · subst G
    simp only [Nat.zero_add,one_pow]
    have hp : 1≤2^s := Nat.one_le_pow _ _ (by decide)
    omega
  · have hp : 1≤G := by omega
    have hb := Nat.pow_le_pow_left (show G+1≤2*G by omega) 3
    have he : G^3≤G^100 := Nat.pow_le_pow_right hp (by decide)
    rw [mul_pow] at hb
    exact hb.trans (Nat.mul_le_mul_left 8 (he.trans hg))

theorem printer_linear_table (s : ℕ) (row : EquationRow.Input)
    (hg : row.cuts.length^100≤2^s) :
    EquationRowFramed.uniformBudget row≤5000000*2^s*(row.d+row.p+1)^3 := by
  have h := Nat.mul_le_mul_right ((row.d+row.p+1)^3)
    (Nat.mul_le_mul_left 625000 (gate_cube s row.cuts.length hg))
  exact (uniform_bound row).trans (h.trans_eq (by ring))

end NearCubicWires.RepairOrdinary.CloseoutRowsPrinterBudget
