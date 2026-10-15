import Proof.Foundations.SourceRegistry
import Proof.CaseAnalysis.RawRowsThresholdAccuracy

namespace NearCubicWires.RepairSource.CloseoutFinal

open RepairRepresentation SourceInterfaces SupplierPipeline RepairOrdinary ExecutableInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The selected exact rectangular-product algorithm (paper Appendix B). Every
estimator machine is built over this one value. -/
def williamsOf (sources : EightSources) : WilliamsAlgorithm :=
  Classical.choice sources.williams

/-- The selected disjoint exact-decomposition algorithm (paper A.12). -/
def decompositionOf (sources : EightSources) : DecompositionAlgorithm :=
  Classical.choice sources.decomposition

/-- Gabber-Galil spectral radius, used by the threshold powered walk (paper A.5,
A.9 item 4). -/
theorem expanderOf (sources : EightSources) : ExpanderSpectrumContract :=
  sources.expander

/-- Rosser-Schoenfeld Chebyshev theta, used by the prime surrogate (paper A.6,
A.9 item 5). -/
theorem primeOf (sources : EightSources) : PrimeThetaBoundContract :=
  sources.prime

/-- Finite integer normalization on the retained support (paper A.9 item 1). -/
theorem normalizationOf (sources : EightSources) : ThresholdNormalizationContract :=
  sources.normalization

/-- The chosen decomposition algorithm's output length bound, the field the
source-atom cache consumes. -/
theorem decomposition_output (sources : EightSources) (r : ExactDecompositionRequest) :
    (exactListWord ((decompositionOf sources).output r).children).length ≤
      DecompositionSource.sourceBudget (decompositionOf sources) r :=
  DecompositionSource.output_length (decompositionOf sources) r

/-- The threshold prime certificate at the SELECTED decomposition algorithm and
the SELECTED Chebyshev contract: this is the application that ties
`sources.prime` and `sources.decomposition` to the paper's A.6 error bound. -/
theorem threshold_error_bound (sources : EightSources)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    (CloseoutRawRows.thresholdPrimeCertificate (primeOf sources) (decompositionOf sources)
      r desc target hfour hd).error ≤
      1/(CloseoutRawRows.thresholdPrimeDen (decompositionOf sources) desc target + 1 : ℕ) :=
  CloseoutRawRows.threshold_prime_error (primeOf sources) (decompositionOf sources)
    r desc target hfour hd

end
end NearCubicWires.RepairSource.CloseoutFinal
