import Proof.Amplification.RecoveryFrontWhole

/-! Uniform cold-front resource bound. Whole-witness scans remain charged
linearly; canonical NP completeness later bounds that witness length. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem table_budget (bits word : List Bool) :
    RecoveryColdTables.resetBudget (width bits) (limit bits) word ≤
      2048*(bits.length+1)^2+16*word.length+64 := by
  have hc : limit bits ≤ 6*(bits.length+1) := by
    change 3*(max 1 bits.length+1) ≤ 6*(bits.length+1)
    omega
  have hw : width bits ≤ 3*(bits.length+1) := by
    change max 1 bits.length+2 ≤ 3*(bits.length+1)
    omega
  have hp := Nat.mul_le_mul hc hw
  have hl : bits.length+1 ≤ (bits.length+1)^2 := by
    nlinarith [Nat.zero_le (bits.length*bits.length)]
  unfold RecoveryColdTables.resetBudget RecoveryColdTables.budget
    RecoveryColdTableSlice.budget RecoveryColdTableSkip.budget
  nlinarith only [hp,hc,hl]

theorem front_budget (bits word : List Bool) :
    budget bits word ≤ 274877906944*(bits.length+1)^4+36*word.length+512 := by
  have hsat := RecoveryColdSAT.cold_budget bits word
  have hview := RecoveryColdView.cold_budget bits word
  have htable := table_budget bits word
  have hw : width bits+1 ≤ 4*(bits.length+1) := by
    change max 1 bits.length+2+1 ≤ 4*(bits.length+1)
    omega
  have hp : (width bits+1)^4 ≤ 256*(bits.length+1)^4 := by
    calc
      _ ≤ (4*(bits.length+1))^4 := Nat.pow_le_pow_left hw 4
      _ = _ := by ring
  have hpos : 1 ≤ (bits.length+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hp24 : (bits.length+1)^2 ≤ (bits.length+1)^4 := by
    calc
      _ = 1*(bits.length+1)^2 := by omega
      _ ≤ (bits.length+1)^2*(bits.length+1)^2 := Nat.mul_le_mul_right _ hpos
      _ = _ := by ring
  unfold budget prefixBudget RecoveryColdScanner.scanBudget
  omega

theorem input_layout (bits word : List Bool) : input bits word=
    fun i : Fin 279=>if i.val=0 then frame bits else if i.val=1 then frame word else [] := by
  funext i
  fin_cases i <;> simp [input,RecoveryColdTablesAmbient.coldTapes,RecoveryColdScanner.tapes,
    RecoveryColdSAT.input_layout,Fin.addCases]

theorem front_bounded (bits word : List Bool) :
    ∃ bit r,run machine (274877906944*(bits.length+1)^4+36*word.length+512) (input bits word)=some r ∧
      r.steps ≤ 274877906944*(bits.length+1)^4+36*word.length+512 ∧
      r.final.heads 277=0 ∧ r.final.tapes 277=[bit] ∧
      (bit=true → Prepared bits word r.final.heads r.final.tapes) := by
  obtain ⟨bit,r,hr,hb,hh,ht,hready⟩ := front_run bits word
  have hm := run_moreFuel machine (budget bits word)
    (274877906944*(bits.length+1)^4+36*word.length+512-budget bits word) _ r hr
  rw [Nat.add_sub_of_le (front_budget bits word)] at hm
  exact ⟨bit,r,hm,hb.trans (front_budget bits word),hh,ht,hready⟩

end NearCubicWires.RepairOrdinary.RecoveryColdFront
