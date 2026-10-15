import Proof.Foundations.OperationalWilliamsSourceCore
import Proof.Foundations.ExecutableProgramTightRefuterSource
import Proof.Foundations.TrustExactDecompositionChildCount

/-!
# Published theorem assumptions

The eight fields are the unique published-source firewall.  Algorithmic
sources carry executable refinements whose outputs and resource charges come
from fixed interpreters or literal local-machine receipts.  Genuinely
mathematical sources remain semantic.  No algorithmic row stores an
independent semantic duplicate.
-/

namespace NearCubicWires

open SourceInterfaces
open ExecutableInterfaces
open ExecutableProgramTimedSource
open ExecutableProgramTightRefuterSource
open WilliamsPublishedForm

structure PublishedContracts where
  thresholdNormalization : ThresholdNormalizationContract
  /-- **Assumed: the decomposition algorithm exists.  Not assumed: any of its
  quantitative bounds.**

  `paper.tex:2306-2310` imports only the *qualitative* threshold-to-exact
  conversion of [CW19, Prop. 18(2), App. B Lemmas 48-49], "with the complete
  construction and safe quantitative bounds replayed locally in Appendix A.12";
  `paper.tex:390-391` repeats that "all of its quantitative bounds are replayed
  locally".  The replay exists because CW19's printed Lemma 48 proof contains
  three identified errors, and A.12 "imports no one of those three literal
  claims" (`paper.tex:2698-2705`).

  Accordingly this field is literally `Nonempty ExecutableExactDecompositionAlgorithm`.
  It used to carry a second, polynomial child-count clause;
  `ExecutableInterfaces.executableDisjointExactDecomposition_iff_legacy` proves
  the two forms equivalent, the bound being a theorem about the fixed
  `NPOracleProgram` interpreter rather than an import
  (`TrustExactDecompositionChildCount`).

  Remaining local proof obligation, not discharged here: A.12's own sharper
  count `max{1, n·L̄}` and its coefficient/target envelopes
  (`paper.tex:2576-2696`) are not yet formalized; the interface only needs the
  looser interpreter-derived bound, so nothing downstream depends on them. -/
  disjointExactDecomposition : ExecutableDisjointExactDecompositionContract
  booleanRectangularProduct : FaithfulWilliamsRectangularProductContract
  expanderSpectrum : ExpanderSpectrumContract
  primeThetaBound : PrimeThetaBoundContract
  projectionPcpAndPcpp : ExecutableProgramProjectionPcpAndPcppContract
  refuterAndXor : CertifiedTightExecutableProgramRefuterAndXorContract
  worstCaseAmplifier : ExecutableWorstCaseAmplifierContract

theorem PublishedContracts.disjointExactDecompositionSemantic
    (contracts : PublishedContracts) :
    DisjointExactDecompositionContract :=
  executableDisjointDecomposition_implies_semantic
    contracts.disjointExactDecomposition

theorem PublishedContracts.booleanRectangularProductSemantic
    (contracts : PublishedContracts) :
    BooleanRectangularProductContract :=
  faithfulWilliams_implies_semantic contracts.booleanRectangularProduct

theorem PublishedContracts.pointwisePcppExecutable
    (contracts : PublishedContracts) :
    ExecutablePointwisePCPPContract :=
  contracts.projectionPcpAndPcpp.2

/-- Safe compatibility for the existing refuter recovery cone.  The hierarchy
timed machine remains definitionally derived from the selected executable
program; no arbitrary acceptance/step pair enters through this projection. -/
theorem PublishedContracts.refuterAndXorLegacy
    (contracts : PublishedContracts) :
    ExecutableRefuterAndXorContract :=
  certifiedTightProgramRefuterAndXor_implies_legacy contracts.refuterAndXor

theorem PublishedContracts.worstCaseAmplifierSemantic
    (contracts : PublishedContracts) :
    WorstCaseAmplifierContract :=
  executableWorstCaseAmplifier_implies_semantic contracts.worstCaseAmplifier

theorem PublishedContracts.asPublishedConjunction
    (contracts : PublishedContracts) :
    ThresholdNormalizationContract ∧
      ExecutableDisjointExactDecompositionContract ∧
      FaithfulWilliamsRectangularProductContract ∧
      ExpanderSpectrumContract ∧
      PrimeThetaBoundContract ∧
      ExecutableProgramProjectionPcpAndPcppContract ∧
      CertifiedTightExecutableProgramRefuterAndXorContract ∧
      ExecutableWorstCaseAmplifierContract :=
  ⟨contracts.thresholdNormalization,
    contracts.disjointExactDecomposition,
    contracts.booleanRectangularProduct,
    contracts.expanderSpectrum,
    contracts.primeThetaBound,
    contracts.projectionPcpAndPcpp,
    contracts.refuterAndXor,
    contracts.worstCaseAmplifier⟩

end NearCubicWires
