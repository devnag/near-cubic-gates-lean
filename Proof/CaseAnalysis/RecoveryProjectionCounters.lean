import Proof.CaseAnalysis.RecoveryProjectionBank

/-! Existing restoring counters produce the remaining three raw/sentinel
outputs. All projector cells are retained byte for byte. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def countMachine := RecoveryFocus.machine countSlots Counter.machine
noncomputable def rawRMachine := RecoveryFocus.machine rawRSlots (UWalkUnary.machine false false)
noncomputable def rawQMachine := RecoveryFocus.machine rawQSlots (UWalkUnary.machine false false)
def outputR (A : Fin 113→List Bool) (R : ℕ) :=
  Function.update (Function.update A 109 (List.replicate R true)) 110 (List.replicate (R+2) false)
def outputQ (A : Fin 113→List Bool) (Q : ℕ) :=
  Function.update (Function.update A 111 (List.replicate Q true)) 112 (List.replicate (Q+2) false)

theorem count_ready (n : ℕ) (A : Fin 113→List Bool)
    (h103 : A 103=List.replicate n true) (h106 : A 106=[]) (h107 : A 107=[]) (h108 : A 108=[]) : ∃ O,
    ClockJoin.ReadyRun countMachine (Counter.budget n) A O ∧ O 106=CompareMachine.word n ∧
      (∀ i,i≠106→i≠107→i≠108→O i=A i) := by
  obtain ⟨out,hr,h0,h2⟩ := DriverAtoms.counter_run n
  have h:=hr.focus countSlots count_injective A (by
    intro i;fin_cases i
    · exact h103
    · exact h107
    · exact h106
    · exact h108)
  refine ⟨install countSlots A out,h,(install_slot countSlots count_injective A out 2).trans h2,?_⟩
  intro i h106' h107' h108'
  by_cases h103' : i=103
  · subst i
    exact (install_slot countSlots count_injective A out 0).trans (h0.trans h103.symm)
  apply install_other
  intro j hj;fin_cases j
  · exact h103' hj.symm
  · exact h107' hj.symm
  · exact h106' hj.symm
  · exact h108' hj.symm

theorem rawR_ready (R : ℕ) (A : Fin 113→List Bool)
    (h34 : A 34=CompareMachine.word R) (h109 : A 109=[]) (h110 : A 110=[]) :
    ClockJoin.ReadyRun rawRMachine (2*R+6) A (outputR A R) := by
  have h:=(UWalkUnary.ready false false 0 R).focus rawRSlots rawR_injective A (by
    intro i;fin_cases i
    · change A 34=ZeroPadding.pad 0 (CompareMachine.word R)
      rw [ZeroPadding.pad_zero];exact h34
    · exact h109
    · exact h110)
  have he : install rawRSlots A (UWalkUnary.result false false 0 R)=outputR A R := by
    apply HierarchyWidth.install_eq rawRSlots rawR_injective
    · intro j;fin_cases j
      · change A 34=ZeroPadding.pad 0 (CompareMachine.word R)
        rw [ZeroPadding.pad_zero];exact h34
      · change List.replicate R true=UWalkUnary.output false false R
        simp [UWalkUnary.output,UWalkUnary.lead]
      · rfl
    · intro i hi
      have h109' : i≠109:=fun he=>hi 1 he.symm
      have h110' : i≠110:=fun he=>hi 2 he.symm
      simp only [outputR,Function.update_of_ne h109',Function.update_of_ne h110']
  simpa only [rawRMachine,he] using h

theorem rawQ_ready (Q : ℕ) (A : Fin 113→List Bool)
    (h35 : A 35=CompareMachine.word Q) (h111 : A 111=[]) (h112 : A 112=[]) :
    ClockJoin.ReadyRun rawQMachine (2*Q+6) A (outputQ A Q) := by
  have h:=(UWalkUnary.ready false false 0 Q).focus rawQSlots rawQ_injective A (by
    intro i;fin_cases i
    · change A 35=ZeroPadding.pad 0 (CompareMachine.word Q)
      rw [ZeroPadding.pad_zero];exact h35
    · exact h111
    · exact h112)
  have he : install rawQSlots A (UWalkUnary.result false false 0 Q)=outputQ A Q := by
    apply HierarchyWidth.install_eq rawQSlots rawQ_injective
    · intro j;fin_cases j
      · change A 35=ZeroPadding.pad 0 (CompareMachine.word Q)
        rw [ZeroPadding.pad_zero];exact h35
      · change List.replicate Q true=UWalkUnary.output false false Q
        simp [UWalkUnary.output,UWalkUnary.lead]
      · rfl
    · intro i hi
      have h111' : i≠111:=fun he=>hi 1 he.symm
      have h112' : i≠112:=fun he=>hi 2 he.symm
      simp only [outputQ,Function.update_of_ne h111',Function.update_of_ne h112']
  simpa only [rawQMachine,he] using h

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
