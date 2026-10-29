import NineInputs
import SourceAdapters.Normalization.IntegerThreshold
import SourceAdapters.Restriction.CentralBinomial
import SourceAdapters.Probability.BernsteinFinite
import SourceAdapters.Base.Primes
import SourceAdapters.Williams.Final
import SourceAdapters.Assembly.Field6Ordinary
import SourceAdapters.Assembly.Field7
import SourceAdapters.Amplification.Field8
import SourceAdapters.Assembly.Field9Encoder

/-!
# From the published statements to the nine inputs

`sources_to_nine`: every field of `NineInputs` from the published statements of `PublishedInputs`, by the
adapter proving it.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters

open NearCubicGates.Close

/-- The nine inputs from the published statements: each field by its adapter. -/
theorem sources_to_nine (h : PublishedInputs) :
    NineInputs := {
  normalization := @NearCubicGates.Adapters.Normalization.threshold_normalization,
  restriction := @NearCubicGates.Adapters.Restriction.centralBinomialRestriction,
  bernstein := @NearCubicGates.Adapters.Probability.finiteBernstein,
  primes := @NearCubicGates.Adapters.Base.primes_of_primeNumberTheorem h.apostol_primeNumberTheorem,
  rectangularProduct := @NearCubicGates.Adapters.Williams.Final.williams14_of_leaf h.williams_rectangularProductLeaf,
  shortPCP := @NearCubicGates.Adapters.Assembly.field6Ordinary h.bcgt13_theorem11_1 h.shoup_findIrrPolyAlgorithm17,
  refuter := @NearCubicGates.Adapters.Assembly.field7,
  amplification := @NearCubicGates.Adapters.Amplification.field8 h.stv_theorem29,
  threeQueryPCPP := @NearCubicGates.Adapters.Assembly.field9Encoder h.cw19Proximity_lemma22Half h.cw19Code_lemma26 }

end NearCubicGates.Adapters
