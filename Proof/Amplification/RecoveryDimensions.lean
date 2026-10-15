import Proof.Amplification.RecoveryBinaryFix

/-! Whole cold dimensions producer from a framed binary input and blank
workspace. It produces the actual canonical unary width and binary input
bound, with all copies, empty-input corrections and rewinds charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdDimensions
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def widthMachine := TapeEmbedding.machine 3 RecoveryColdWidthEntry.machine
noncomputable def prefixMachine := Composition.machine widthMachine RecoveryColdBinaryCount.machine
noncomputable def machine := Composition.machine prefixMachine RecoveryColdBinaryFix.machine
def input (bits : List Bool) : Fin 5→List Bool := ![frame bits,[],[],[],[]]
def budget (bits : List Bool) := 6*bits.length+HierarchyInputLength.budget bits+16

theorem budget_le (bits : List Bool) : budget bits ≤ 128*(bits.length+1)^2 := by
  have he : PCPResourceLedger.ell bits.length ≤ bits.length := by
    apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul_left (8*bits.length) he
  unfold budget HierarchyInputLength.budget HierarchyInputLength.rawBudget ClockInputLength.cost
  nlinarith only [hm]

theorem width_run (bits : List Bool) :
    ∃ r,run widthMachine (6*bits.length+10) (input bits)=some r ∧
      r.final.heads=RecoveryColdBinaryCount.heads ∧ r.final.tapes=RecoveryColdBinaryCount.input bits := by
  obtain ⟨base,hbase,hbt,hbh,_⟩ := RecoveryColdWidthEntry.entry_run bits
  obtain ⟨r,hr,_,hf⟩ := RecoveryBankPair.left_run RecoveryColdWidthEntry.machine (6*bits.length+10)
    (initialConfiguration RecoveryColdWidthEntry.machine ![frame bits,[]]) base hbase
    (fun _ : Fin 3=>0) (fun _=>[])
  have hi : RecoveryBankPair.cfg
      (initialConfiguration RecoveryColdWidthEntry.machine ![frame bits,[]]).heads
      (initialConfiguration RecoveryColdWidthEntry.machine ![frame bits,[]]).tapes
      (fun _ : Fin 3=>0) (fun _=>[])
      (initialConfiguration RecoveryColdWidthEntry.machine ![frame bits,[]]).control=
      initialConfiguration widthMachine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_⟩
  · rw [hf,hbh]
    funext i
    fin_cases i <;> rfl
  · rw [hf,hbt]
    funext i
    fin_cases i <;> rfl

theorem dimensions_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
    ∃ r,run machine (budget bits) (input bits)=some r ∧
      r.final.heads=RecoveryColdBinaryCount.heads ∧ r.final.tapes=RecoveryColdBinaryFix.output bits cap scratch ∧
      r.steps ≤ 128*(bits.length+1)^2 := by
  obtain ⟨first,hfirst,hfh,hft⟩ := width_run bits
  obtain ⟨cap,scratch,hcap,hscratch,count,hcount,hch,hct,_⟩ := RecoveryColdBinaryCount.count_run bits
  have hi : Composition.restart first.final RecoveryColdBinaryCount.machine.start=
      (⟨RecoveryColdBinaryCount.machine.start,RecoveryColdBinaryCount.heads,RecoveryColdBinaryCount.input bits⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  rw [←hi] at hcount
  have hprefix := Composition.run_join widthMachine RecoveryColdBinaryCount.machine
    (6*bits.length+10) (HierarchyInputLength.budget bits) _ first count hfirst hcount
  let pref := Composition.joinedReceipt first count
  obtain ⟨last,hlast,hlh,hlt,_⟩ := RecoveryColdBinaryFix.fix_run bits cap scratch
  have hj : Composition.restart pref.final RecoveryColdBinaryFix.machine.start=
      (⟨RecoveryColdBinaryFix.machine.start,RecoveryColdBinaryCount.heads,RecoveryColdBinaryCount.output bits cap scratch⟩ : Configuration 5 _) := by
    apply configuration_ext
    · rfl
    · exact hch
    · exact hct
  rw [←hj] at hlast
  have h := Composition.run_join prefixMachine RecoveryColdBinaryFix.machine
    (6*bits.length+10+1+HierarchyInputLength.budget bits) 4 _ pref last hprefix hlast
  have he : 6*bits.length+10+1+HierarchyInputLength.budget bits+1+4=budget bits := by unfold budget; omega
  rw [he] at h
  let r := Composition.joinedReceipt pref last
  have hr : run machine (budget bits) (input bits)=some r := h
  exact ⟨cap,scratch,hcap,hscratch,r,hr,hlh,hlt,
    (runFrom_steps_le machine (budget bits) _ r hr).trans (budget_le bits)⟩

end NearCubicWires.RepairOrdinary.RecoveryColdDimensions
