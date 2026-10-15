import Proof.MachineModel.OrdinaryWilliamsTemplateLayout

/-! The first three calls of the literal template-preparation controller.
The width converter and both differences consume their actual input tapes
and retain all earlier live registers and untouched future workspace. -/
namespace NearCubicWires.RepairOrdinary.WilliamsTemplates
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_ready (a : Fin 50 → List Bool) (w : ℕ)
    (h4 : a 4=CompareMachine.word w) (hb : Blank 6 a) :
    ∃ b, ReadyRun (programs 0) (4*w+12) a b ∧ Old 4 a b ∧ b 5=a 5 ∧
      b 6=List.replicate w true ∧ b 8=UnaryTemplate.tape w ∧ Blank 10 b := by
  obtain ⟨r,hr,h1,_,h3,hh,hs⟩ := MatrixTemplateCopy.word_run w
  have ready : ReadyRun MatrixTemplateCopy.resetMachine (4*w+12)
      (MatrixTemplateCopy.wordInput w) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (widthSlots j)=MatrixTemplateCopy.wordInput w j := by
    intro j; fin_cases j
    · exact h4
    · exact hb 6 (by decide)
    · exact hb 7 (by decide)
    · exact hb 8 (by decide)
    · exact hb 9 (by decide)
  let b := install widthSlots a r.final.tapes
  refine ⟨b,ready.focus widthSlots (by decide) a hin,?_,?_,?_,?_,?_⟩
  · apply install_old
    intro j hj
    fin_cases j <;> simp [widthSlots] at hj
  · exact install_other widthSlots a r.final.tapes 5 (by decide)
  · change b (widthSlots 1)=_
    exact (install_slot widthSlots (by decide) a r.final.tapes 1).trans h1
  · change b (widthSlots 3)=_
    exact (install_slot widthSlots (by decide) a r.final.tapes 3).trans h3
  · exact install_blank widthSlots a r.final.tapes 10 (by decide) (hb.later (by decide))

theorem delta_ready (a : Fin 50 → List Bool) (v u : ℕ) (huv : u ≤ v)
    (h2 : a 2=UnaryTemplate.tape v) (h0 : a 0=UnaryTemplate.tape u) (hb : Blank 10 a) :
    ∃ b, ReadyRun (programs 1) (2*v+8) a b ∧ Old 10 a b ∧
      b 10=UnaryTemplate.tape (v-u) ∧ Blank 12 b := by
  obtain ⟨r,hr,hr0,hr1,hr2,hh,hs⟩ := MatrixUnaryDifference.reset_run v u huv
  have ready : ReadyRun MatrixUnaryDifference.resetMachine (2*v+8)
      (MatrixUnaryDifference.resetInput v u) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (deltaSlots j)=MatrixUnaryDifference.resetInput v u j := by
    intro j; fin_cases j
    · exact h2
    · exact h0
    · exact hb 10 (by decide)
    · exact hb 11 (by decide)
  let b := install deltaSlots a r.final.tapes
  refine ⟨b,ready.focus deltaSlots (by decide) a hin,?_,?_,?_⟩
  · apply install_old
    intro j hj
    fin_cases j
    · exact hr0.trans h2.symm
    · exact hr1.trans h0.symm
    · simp [deltaSlots] at hj
    · simp [deltaSlots] at hj
  · change b (deltaSlots 2)=_
    exact (install_slot deltaSlots (by decide) a r.final.tapes 2).trans hr2
  · exact install_blank deltaSlots a r.final.tapes 12 (by decide) (hb.later (by decide))

theorem gap_ready (a : Fin 50 → List Bool) (v u : ℕ) (huv : u ≤ v)
    (h8 : a 8=UnaryTemplate.tape v) (h3 : a 3=UnaryTemplate.tape u) (hb : Blank 12 a) :
    ∃ b, ReadyRun (programs 2) (2*v+8) a b ∧ Old 12 a b ∧
      b 12=UnaryTemplate.tape (v-u) ∧ Blank 14 b := by
  obtain ⟨r,hr,hr0,hr1,hr2,hh,hs⟩ := MatrixUnaryDifference.reset_run v u huv
  have ready : ReadyRun MatrixUnaryDifference.resetMachine (2*v+8)
      (MatrixUnaryDifference.resetInput v u) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (gapSlots j)=MatrixUnaryDifference.resetInput v u j := by
    intro j; fin_cases j
    · exact h8
    · exact h3
    · exact hb 12 (by decide)
    · exact hb 13 (by decide)
  let b := install gapSlots a r.final.tapes
  refine ⟨b,ready.focus gapSlots (by decide) a hin,?_,?_,?_⟩
  · apply install_old
    intro j hj
    fin_cases j
    · exact hr0.trans h8.symm
    · exact hr1.trans h3.symm
    · simp [gapSlots] at hj
    · simp [gapSlots] at hj
  · change b (gapSlots 2)=_
    exact (install_slot gapSlots (by decide) a r.final.tapes 2).trans hr2
  · exact install_blank gapSlots a r.final.tapes 14 (by decide) (hb.later (by decide))

end NearCubicWires.RepairOrdinary.WilliamsTemplates
