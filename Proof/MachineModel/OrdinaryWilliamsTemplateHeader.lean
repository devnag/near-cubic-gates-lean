import Proof.MachineModel.OrdinaryWilliamsTemplateProducts

/-! Last two actual preparation calls: duplicate the row-count driver
and serialize the source's exact binary dimension header. -/
namespace NearCubicWires.RepairOrdinary.WilliamsTemplates
open LocalBitMultitape RecoveryRootRound RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem copy_ready (a : Fin 50 → List Bool) (u : ℕ)
    (h0 : a 0=UnaryTemplate.tape u) (hb : Blank 44 a) :
    ∃ b, ReadyRun (programs 6) (4*u+12) a b ∧ Old 44 a b ∧
      b 46=UnaryTemplate.tape u ∧ Blank 48 b := by
  obtain ⟨r,hr,hr0,_,_,hr3,hh,hs⟩ := MatrixTemplateCopy.reset_run u
  have ready : ReadyRun MatrixTemplateCopy.resetMachine (4*u+12)
      (MatrixTemplateCopy.resetInput u) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (copySlots j)=MatrixTemplateCopy.resetInput u j := by
    intro j; fin_cases j
    · exact h0
    · exact hb 44 (by decide)
    · exact hb 45 (by decide)
    · exact hb 46 (by decide)
    · exact hb 47 (by decide)
  let b := install copySlots a r.final.tapes
  refine ⟨b,ready.focus copySlots (by decide) a hin,?_,?_,?_⟩
  · apply install_old
    intro j hj; fin_cases j
    · exact hr0.trans h0.symm
    all_goals simp [copySlots] at hj
  · exact (install_slot copySlots (by decide) a r.final.tapes 3).trans hr3
  · exact install_blank copySlots a r.final.tapes 48 (by decide) (hb.later (by decide))

theorem header_ready (a : Fin 50 → List Bool) (v : ℕ)
    (h5 : a 5=frame (binary (natBitLength v) v))
    (h6 : a 6=List.replicate (natBitLength v) true) (hb : Blank 48 a) :
    ∃ b, ReadyRun (programs 7) (6*natBitLength v+6) a b ∧ Old 48 a b ∧ b 48=natWord v := by
  obtain ⟨r,hr,hr0,hr1,hr2,hh,hs⟩ := MatrixNaturalHeader.natural_run v
  have ready : ReadyRun MatrixNaturalHeader.resetMachine (6*natBitLength v+6)
      (MatrixNaturalHeader.resetInput (binary (natBitLength v) v)) r.final.tapes := ⟨r,hr,rfl,hh,hs⟩
  have hin : ∀ j, a (headerSlots j)=MatrixNaturalHeader.resetInput (binary (natBitLength v) v) j := by
    intro j; fin_cases j
    · exact h5
    · simpa [headerSlots,MatrixNaturalHeader.resetInput,MatrixNaturalHeader.input,Fin.addCases] using h6
    · exact hb 48 (by decide)
    · exact hb 49 (by decide)
  let b := install headerSlots a r.final.tapes
  refine ⟨b,ready.focus headerSlots (by decide) a hin,?_,?_⟩
  · apply install_old
    intro j hj; fin_cases j
    · exact hr0.trans h5.symm
    · exact hr1.trans h6.symm
    · simp [headerSlots] at hj
    · simp [headerSlots] at hj
  · exact (install_slot headerSlots (by decide) a r.final.tapes 2).trans hr2

end NearCubicWires.RepairOrdinary.WilliamsTemplates
