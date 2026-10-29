import SourceAdapters.RAMACSP.CheckFrame
import SourceAdapters.RAMACSP.Embed
import SourceAdapters.Routing.Final
import SourceAdapters.RAMTrace.EventTrace

/-!
# The concrete affine constraint reduction

Step 1 of `thm:short-pcp-ours` combines the actual event-trace equivalence,
ordered input embedding, emitted constraint, weighted degree, and canonical
frame of `def:acsp`. Shoup supplies the field choice. The computational
certificates describe the size and total ordinary construction of this same
instance, with its one input subspace and neighbor pairs.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters
open NearCubicWires NearCubicWires.RepairOrdinary Polynomial

/-- The certificates for Step 1 of `thm:short-pcp-ours` assemble the instance
of `def:acsp` after Shoup's field choice. The embedding appendix supplies the
acceptance equivalence; `lem:generator` supplies its description and machine bounds. -/
theorem affineConstraint_ownReduction_of_frontier (hIrr : Published.Shoup.FindIrrPolyAlgorithm17)
    (hET : Joins.RAMEventTrace)
    (cons : (ℕ → (ZMod 2)[X]) → Verifier → ClockRequest → List CodeGate)
    (hE : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → EmbeddingEquivalence V irrPoly (cons irrPoly V))
    (hD : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → DegreeBound V irrPoly (cons irrPoly V))
    (hK : ∀ irrPoly V, ConstraintConstantsReduced V irrPoly (cons irrPoly V))
    (hS : ∀ irrPoly V, ParameterSize V irrPoly (cons irrPoly V))
    (hG : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → Published.Shoup.PolyTimeIrrChoice irrPoly →
      GeneratorMachine V irrPoly (cons irrPoly V)) :
    ∀ V, Joins.AffineConstraintReduction V := by
  obtain ⟨irrPoly, hI, hP⟩ := hIrr
  intro V
  exact affineConstraint_of_frontier V irrPoly (cons irrPoly V) hI hET (hE irrPoly V hI) (hD irrPoly V hI)
    (hK irrPoly V) (hS irrPoly V) (hG irrPoly V hI hP) (frameSyntax V irrPoly (cons irrPoly V) hI)
    (frameBounds V irrPoly (cons irrPoly V)) (frameNeighbors V irrPoly (cons irrPoly V) hI)

/-- For the emitted constraint of the embedding appendix, the checked frame,
constant and weighted-degree proofs supply the conditions of `def:acsp`. This
form accepts the embedding and generation certificates used by Step 1 of
`thm:short-pcp-ours` and `lem:generator`. -/
theorem affineConstraint_ownReduction_of_ESG (hIrr : Published.Shoup.FindIrrPolyAlgorithm17)
    (hE : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → EmbeddingEquivalence V irrPoly (ownCons V irrPoly))
    (hS : ∀ irrPoly V, ParameterSize V irrPoly (ownCons V irrPoly))
    (hG : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → Published.Shoup.PolyTimeIrrChoice irrPoly →
      GeneratorMachine V irrPoly (ownCons V irrPoly)) :
    ∀ V, Joins.AffineConstraintReduction V :=
  affineConstraint_ownReduction_of_frontier hIrr RAMTrace.ramEventTrace
    (fun irrPoly V => ownCons V irrPoly) hE (fun irrPoly V hI => degreeBound_own V irrPoly hI)
    (fun irrPoly V => constraintConstantsReduced V irrPoly) hS hG

/-- The geometric, constraint and embedding proofs discharge the mathematical
conditions of `def:acsp` and Step 1 of `thm:short-pcp-ours`. The additional inputs
are the description-size and total ordinary-generator certificates of
`lem:generator` for this same instance. -/
theorem affineConstraint_ownReduction_of_SG (hIrr : Published.Shoup.FindIrrPolyAlgorithm17)
    (hS : ∀ irrPoly V, ParameterSize V irrPoly (ownCons V irrPoly))
    (hG : ∀ irrPoly V, Published.Shoup.IrreducibleChoice irrPoly → Published.Shoup.PolyTimeIrrChoice irrPoly →
      GeneratorMachine V irrPoly (ownCons V irrPoly)) :
    ∀ V, Joins.AffineConstraintReduction V :=
  affineConstraint_ownReduction_of_ESG hIrr embeddingEquivalence hS hG

end NearCubicGates.Adapters.RAMACSP
