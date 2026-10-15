import Proof.Amplification.RecoveryCapWhole

/-! Cold scalar preparation from the original framed input and blank
workspace: code, binary bound, zero field, quadratic erase driver, and the
literal linear certificate cap. All head restoration and joins are paid. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeaderCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) (i : Fin 22) := if i.val=0 then frame bits else []
def limit (bits : List Bool) := 3*(max 1 bits.length+1)
noncomputable def ambient (bits : List Bool) (cap scratch : Nat) (i : Fin 22) : List Bool :=
  Fin.addCases (RecoveryColdHeader.output bits cap scratch) (fun _ : Fin 2=>[]) i
def slots : Fin 3→Fin 22 := ![1,20,21]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def capMachine := RecoveryFocus.machine slots RecoveryColdCap.machine
noncomputable def prefixMachine := TapeEmbedding.machine 2 RecoveryColdHeader.machine
noncomputable def machine := Composition.machine prefixMachine capMachine
noncomputable def output (bits : List Bool) (cap scratch : Nat) := install slots (ambient bits cap scratch)
  ![RecoveryColdCap.word (max 1 bits.length+1+1),RecoveryColdCap.word (limit bits),
    List.replicate (3*(max 1 bits.length+1)+3) false]
def budget (bits : List Bool) := RecoveryColdHeader.budget bits+1+(6*(max 1 bits.length+1)+8)

theorem width_tape (bits : List Bool) (cap scratch : Nat) :
    RecoveryColdHeader.output bits cap scratch 1=
      RecoveryColdCap.word (max 1 bits.length+1+1) :=
  install_other RecoveryColdHeader.driverSlots _ _ _ (by intro j; fin_cases j <;> decide)

theorem cap_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun capMachine (6*(max 1 bits.length+1)+8) (ambient bits cap scratch) (output bits cap scratch) := by
  apply (RecoveryColdCap.cap_ready (max 1 bits.length+1)).focus slots slots_injective
  intro j
  fin_cases j
  · exact width_tape bits cap scratch
  · rfl
  · rfl

theorem prefix_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run prefixMachine (RecoveryColdHeader.budget bits) (input bits)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=ambient bits cap scratch := by
  obtain ⟨cap,scratch,hcap,hscratch,b,hb,hbh,hbt,_⟩ := RecoveryColdHeader.header_run bits
  obtain ⟨r,hr,_,hf⟩ := RecoveryBankPair.left_run RecoveryColdHeader.machine
    (RecoveryColdHeader.budget bits) (initialConfiguration RecoveryColdHeader.machine (RecoveryColdHeader.input bits)) b hb
    (fun _ : Fin 2=>0) (fun _=>[])
  have hi : RecoveryBankPair.cfg
      (initialConfiguration RecoveryColdHeader.machine (RecoveryColdHeader.input bits)).heads
      (initialConfiguration RecoveryColdHeader.machine (RecoveryColdHeader.input bits)).tapes
      (fun _ : Fin 2=>0) (fun _=>[])
      (initialConfiguration RecoveryColdHeader.machine (RecoveryColdHeader.input bits)).control=
      initialConfiguration prefixMachine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨cap,scratch,hcap,hscratch,r,hr,?_,?_⟩
  · rw [hf,hbh]
    funext i
    fin_cases i <;> rfl
  · rw [hf,hbt]
    rfl

theorem prepare_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run machine (budget bits) (input bits)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=output bits cap scratch ∧ r.steps≤budget bits := by
  obtain ⟨cap,scratch,hcap,hscratch,first,hfirst,hfh,hft⟩ := prefix_run bits
  obtain ⟨last,hlast,hlt,hlh,_⟩ := cap_ready bits cap scratch
  have hi : Composition.restart first.final capMachine.start=initialConfiguration capMachine (ambient bits cap scratch) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h := Composition.run_join prefixMachine capMachine (RecoveryColdHeader.budget bits)
    (6*(max 1 bits.length+1)+8) _ first last hfirst hlast
  let r := Composition.joinedReceipt first last
  have hr : run machine (budget bits) (input bits)=some r := h
  exact ⟨cap,scratch,hcap,hscratch,r,hr,funext hlh,hlt,runFrom_steps_le machine (budget bits) _ r hr⟩

end NearCubicWires.RepairOrdinary.RecoveryColdHeaderCap
