import Proof.PCP.ProjectionNormalizationDriverAtoms

/-! Complete physical query-driver production from raw R/Q and the two
parsed native counters. No difference or product is an input premise. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Drivers
open LocalBitMultitape RepairOrdinary RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 6) : Fin 4 → Fin 18 :=
  ![![0,4,5,6],![1,7,8,9],![5,2,10,11],![8,3,12,13],![0,8,14,15],![0,12,16,17]] j
theorem injective (j : Fin 6) : Function.Injective (slots j) := by fin_cases j <;> decide

theorem install_slots (j : Fin 6) (a : Fin 18 → List Bool) (b : Fin 4 → List Bool) (i : Fin 18) :
    install (slots j) a b i=
      if i=slots j 0 then b 0 else if i=slots j 1 then b 1 else
      if i=slots j 2 then b 2 else if i=slots j 3 then b 3 else a i := by
  by_cases h0 : i=slots j 0
  · subst i; rw [install_slot _ (injective j)]; simp
  by_cases h1 : i=slots j 1
  · subst i; rw [install_slot _ (injective j)]; simp [h0]
  by_cases h2 : i=slots j 2
  · subst i; rw [install_slot _ (injective j)]; simp [h0,h1]
  by_cases h3 : i=slots j 3
  · subst i; rw [install_slot _ (injective j)]; simp [h0,h1,h2]
  have hnone : ∀ k,slots j k≠i := by
    intro k
    fin_cases k
    · exact Ne.symm h0
    · exact Ne.symm h1
    · exact Ne.symm h2
    · exact Ne.symm h3
  rw [install_other _ _ _ _ hnone]
  simp [h0,h1,h2,h3]

def input (R Q r q : ℕ) : Fin 18 → List Bool := fun i =>
  if i=0 then List.replicate R true else if i=1 then List.replicate Q true else
  if i=2 then CompareMachine.word r else if i=3 then CompareMachine.word q else []
noncomputable def counterR := RecoveryFocus.machine (slots 0) Counter.machine
noncomputable def counterQ := RecoveryFocus.machine (slots 1) Counter.machine
noncomputable def differenceR := RecoveryFocus.machine (slots 2) Difference.machine
noncomputable def differenceQ := RecoveryFocus.machine (slots 3) Difference.machine
noncomputable def productTotal := RecoveryFocus.machine (slots 4) Product.reset
noncomputable def productExtra := RecoveryFocus.machine (slots 5) Product.reset
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine counterR counterQ) differenceR) differenceQ) productTotal) productExtra
def budget (R Q q : ℕ) := Counter.budget R+1+Counter.budget Q+1+(2*R+8)+1+(2*Q+8)+1+
  DriverAtoms.productBudget R Q+1+DriverAtoms.productBudget R (Q-q)
def Fields (R Q r q : ℕ) (out : Fin 18 → List Bool) : Prop :=
  out 0=List.replicate R true ∧ out 1=List.replicate Q true ∧
  out 2=CompareMachine.word r ∧ out 3=CompareMachine.word q ∧
  out 10=UnaryTemplate.tape (R-r) ∧ out 14=CompareMachine.word (R*Q) ∧
  out 16=CompareMachine.word ((Q-q)*R)

theorem drivers_run (R Q r q : ℕ) (hr : r ≤ R) (hq : q ≤ Q) : ∃ out,
    ClockJoin.ReadyRun machine (budget R Q q) (input R Q r q) out ∧ Fields R Q r q out := by
  obtain ⟨a,ha,ha0,ha2⟩ := DriverAtoms.counter_run R
  have hA := ha.focus (slots 0) (injective 0) (input R Q r q) (by
    intro i; fin_cases i <;> simp [slots,input,Counter.input])
  let A := install (slots 0) (input R Q r q) a
  obtain ⟨b,hb,hb0,hb2⟩ := DriverAtoms.counter_run Q
  have hB := hb.focus (slots 1) (injective 1) A (by
    intro i; fin_cases i <;> simp only [A,install_slots] <;> simp [slots,input,Counter.input])
  let B := install (slots 1) A b
  obtain ⟨c,hc,hc0,hc1,hc2⟩ := DriverAtoms.difference_run R r hr
  have hC := hc.focus (slots 2) (injective 2) B (by
    intro i; fin_cases i <;> simp only [B,A,install_slots] <;> simp [slots,input,Difference.input,Difference.input3,Fin.addCases,ha2])
  let C := install (slots 2) B c
  obtain ⟨d,hd,hd0,hd1,hd2⟩ := DriverAtoms.difference_run Q q hq
  have hD := hd.focus (slots 3) (injective 3) C (by
    intro i; fin_cases i <;> simp only [C,B,A,install_slots] <;> simp [slots,input,Difference.input,Difference.input3,Fin.addCases,hb2])
  let D := install (slots 3) C d
  obtain ⟨e,he,he0,he1,he2⟩ := DriverAtoms.product_run R Q
  have hE := he.focus (slots 4) (injective 4) D (by
    intro i; fin_cases i <;> simp only [D,C,B,A,install_slots] <;> simp [slots,input,Product.input,Product.input3,Fin.addCases,ha0,hd0])
  let E := install (slots 4) D e
  obtain ⟨f,hf,hf0,hf1,hf2⟩ := DriverAtoms.template_product_run R (Q-q)
  have hF := hf.focus (slots 5) (injective 5) E (by
    intro i; fin_cases i <;> simp only [E,D,C,B,A,install_slots] <;> simp [slots,input,DriverAtoms.templateInput,he0,hd2])
  have hAB := ClockJoin.join _ _ _ _ _ _ _ hA hB
  have hABC := ClockJoin.join _ _ _ _ _ _ _ hAB hC
  have hABCD := ClockJoin.join _ _ _ _ _ _ _ hABC hD
  have hABCDE := ClockJoin.join _ _ _ _ _ _ _ hABCD hE
  have hABCDEF := ClockJoin.join _ _ _ _ _ _ _ hABCDE hF
  refine ⟨_,hABCDEF,?_⟩
  simp only [Fields,E,D,C,B,A,install_slots]
  simp [slots,hf0,hb0,hc1,hd1,hc2,he2,hf2,Nat.mul_comm]

theorem budget_bound (R Q q : ℕ) : budget R Q q ≤ 128*(R+Q+1)^2 := by
  have h := Nat.sub_le Q q
  have hp := Nat.mul_le_mul_left R h
  dsimp [budget,Counter.budget,DriverAtoms.productBudget]
  nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.Drivers
