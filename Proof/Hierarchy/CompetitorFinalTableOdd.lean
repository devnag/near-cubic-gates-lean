import Proof.Hierarchy.CompetitorFinalTableSlice
import Proof.Hierarchy.CompetitorFinalTableSemantics

/-! The actual odd branch runs the full signed residue pass, then the
paid row projection, returning the same output ABI as the even branch. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneTable CompetitorOddRowSlice
open SourceInterfaces WilliamsProductCertificate WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def oddBudget (u w q : ℕ) := CompetitorResidueTableDock.budget w q (u*u)+1+CompetitorOddRowSliceDock.budget u q

theorem odd_run {u : ℕ} (b w q pos : ℕ) (state : State (u*u)) (f : Fin u → Fin u → ℕ)
    (he : u/2+u/2=u) (ambient : Fin 159 → List Bool)
    (hc : Native b w state ambient) (hq : q≤w)
    (h36 : ambient 36=List.replicate q true) (h37 : ambient 37=UnaryTemplate.tape u)
    (fresh : ∀ i : Fin 159,90 ≤ i.val → ambient i=[])
    (hfit : ∀ i,state.positive i<2^w ∧ state.negative i<2^w)
    (hsemantic : CompetitorResidueTable.residueWords w q (canonical state)=(rowMajorNatMatrix f).flatMap (binary q)) :
    ∃ r,runFrom oddProgram (oddBudget u w q)
      (RecoveryCalls.restarted oddProgram (heads pos) ambient)=some r ∧
      r.steps≤oddBudget u w q ∧ r.final.heads=heads pos ∧
      r.final.tapes 141=word q true f ∧
      (∀ i : Fin 39,r.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)) := by
  obtain ⟨first,hfirst,_,hfh,h99,hkeep,hfresh⟩ := residue_run b w q pos true state ambient hc hq h36 fresh hfit
  have hs : first.final.tapes 99=(rowMajorNatMatrix f).flatMap (binary q) := h99.trans hsemantic
  have h36' : first.final.tapes 36=List.replicate q true := (hkeep 36).trans h36
  have h37' : first.final.tapes 37=UnaryTemplate.tape u := (hkeep 37).trans h37
  obtain ⟨last,hlast,_,hlh,h141,hlkeep⟩ := slice_run q pos f he first.final.tapes hs h36' h37'
    (by intro i hi; exact hfresh i hi (by have := i.isLt; change i≠99; intro h; subst i; omega))
  have heq : Composition.restart first.final sliceProgram.start=
      RecoveryCalls.restarted sliceProgram (heads pos) first.final.tapes := by
    apply configuration_ext
    · rfl
    · exact hfh
    · rfl
  have hl : runFrom sliceProgram (CompetitorOddRowSliceDock.budget u q)
      (Composition.restart first.final sliceProgram.start)=some last := by rw [heq]; exact hlast
  have hall := Composition.run_join (residueProgram true) sliceProgram _ _ _ first last hfirst hl
  refine ⟨Composition.joinedReceipt first last,hall,runFrom_steps_le _ _ _ _ hall,hlh,?_,?_⟩
  · change last.final.tapes 141=word q true f
    rw [h141]
    simp only [word,values,ite_true]
    congr 3
  · intro i
    change last.final.tapes (i.castAdd 120)=ambient (i.castAdd 120)
    exact (hlkeep (i.castAdd 101)).trans (hkeep i)

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
